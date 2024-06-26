// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"strings"
	"time"

	"github.com/awslabs/ar-go-tools/analysis"
	"github.com/awslabs/ar-go-tools/analysis/config"
	"github.com/awslabs/ar-go-tools/analysis/dataflow"
	"github.com/awslabs/ar-go-tools/analysis/modptr"
	"github.com/awslabs/ar-go-tools/internal/formatutil"
	"golang.org/x/tools/go/ssa"
)

var (
	// Flags
	configPath = flag.String("config", "", "Config file path for analysis")
	verbose    = flag.Bool("verbose", false, "Verbose printing on standard output")
	maxDepth   = flag.Int("max-depth", -1, "Override max depth in config")
	// Other constants
	buildmode = ssa.InstantiateGenerics // necessary for reachability
	version   = "unknown"
)

func init() {
	flag.Var(&buildmode, "build", ssa.BuilderModeDoc)
}

const usage = ` Perform a modification tracking analysis on your packages.
Usage:
    modptr [options] <package path(s)>
Examples:
% modptr -config config.yaml package...
`

func main() {
	var err error
	flag.Parse()

	if flag.NArg() == 0 {
		_, _ = fmt.Fprint(os.Stderr, usage)
		flag.PrintDefaults()
		os.Exit(2)
	}

	logger := log.New(os.Stdout, "", log.Flags())

	cfg := &config.Config{} // empty default config
	if *configPath != "" {
		config.SetGlobalConfig(*configPath)
		cfg, err = config.LoadGlobal()
		if err != nil {
			fmt.Fprintf(os.Stderr, "could not load config %q\n", *configPath)
			return
		}
	}

	// Override config parameters with command-line parameters
	if *verbose {
		cfg.LogLevel = int(config.DebugLevel)
	}
	if *maxDepth > 0 {
		cfg.MaxDepth = *maxDepth
	}

	logger.Printf(formatutil.Faint("Argot modptr tool - build " + version))
	logger.Printf(formatutil.Faint("Reading sources") + "\n")

	lp, err := analysis.LoadProgram(nil, "", buildmode, flag.Args())
	if err != nil {
		fmt.Fprintf(os.Stderr, "could not load program: %v\n", err)
		return
	}
	program := lp.Program

	start := time.Now()
	goPtrRes, err := dataflow.DoPointerAnalysis(program, func(*ssa.Function) bool { return true }, true)
	if err != nil {
		fmt.Fprintf(os.Stderr, "could not compute pointer analysis: %v\n", err)
		return
	}
	ptrRes, err := modptr.DoPointerAnalysis(program, func(*ssa.Function) bool { return true }, true)
	if err != nil {
		fmt.Fprintf(os.Stderr, "could not compute (modified) pointer analysis: %v\n", err)
		return
	}

	result, err := modptr.Analyze(cfg, lp, ptrRes, goPtrRes)
	duration := time.Since(start)
	if err != nil {
		fmt.Fprintf(os.Stderr, "analysis failed: %v\n", err)
		return
	}
	logger.Printf("")
	logger.Printf(strings.Repeat("*", 80))
	logger.Printf("Analysis took %3.4f s", duration.Seconds())
	logger.Printf("")
	if len(result.Modifications) == 0 {
		logger.Printf(
			"RESULT:\n\t\t%s", formatutil.Red("No results detected")) // safe %s
		os.Exit(1)
	} else {
		logger.Printf(
			"RESULT:\n\t\t%s", formatutil.Green("Potential writes and/or aliases detected")) // safe %s
	}

	Report(logger, program, result)
}

// Report logs the taint analysis result
func Report(logger *log.Logger, program *ssa.Program, result modptr.Result) {
	// Prints location of modifications in the SSA
	fail := false
	for entry, mods := range result.Modifications {
		entryVal := entry.Val
		entryPos := entry.Pos
		msg := formatutil.Green("No writes to source memory detected")
		if len(mods.Writes) > 0 {
			msg = formatutil.Red("Source memory has been modified")
			fail = true
		}
		logger.Printf(
			"%s of arg %s of call %s in %s: [SSA] %s at %s\n",
			msg,
			entry.Val.Name(),
			entry.Call.String(),
			entry.Val.Parent().String(),
			formatutil.SanitizeRepr(entryVal),
			entryPos.String()) // safe %s (position string)
		for instr := range mods.Writes {
			modInstr := instr
			modPos := program.Fset.Position(modInstr.Pos())
			logger.Printf(
				"\tWrite: [SSA] %s in function %s\n\t\t%s\n",
				formatutil.SanitizeRepr(modInstr),
				modInstr.Parent().String(),
				modPos.String(), // safe %s (position string)
			)
		}
		for instr := range mods.Allocs {
			modInstr := instr
			modPos := program.Fset.Position(modInstr.Pos())
			logger.Printf(
				"\tAlloc: [SSA] %s in function %s\n\t\t%s\n",
				formatutil.SanitizeRepr(modInstr),
				modInstr.Parent().String(),
				modPos.String(), // safe %s (position string)
			)
		}
	}

	if fail {
		os.Exit(1)
	}
}
