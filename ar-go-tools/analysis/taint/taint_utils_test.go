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

package taint

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"testing"

	"github.com/awslabs/ar-go-tools/analysis/config"
	"github.com/awslabs/ar-go-tools/internal/analysistest"
	"github.com/awslabs/ar-go-tools/internal/formatutil"
	"golang.org/x/tools/go/ssa"
)

// checkTaint checks that actual matches the expected target->sink annotation ids from the test.
//
//gocyclo:ignore
func checkTaint(t *testing.T, prog *ssa.Program, expect analysistest.TargetToSources,
	actual map[FlowNode]map[FlowNode]bool) {
	type seenSource struct {
		Pos   analysistest.LPos
		Trace string
	}
	type seenSink struct {
		Pos analysistest.LPos
	}
	hasMeta := expect.HasMetadata()
	if hasMeta {
		t.Log("Test file has annotation metadata")
	}
	seenTaintFlow := make(map[seenSink]map[seenSource]bool)
	cmpSink := func(actual seenSink) func(analysistest.AnnotationID) bool {
		return func(expect analysistest.AnnotationID) bool {
			// sinks don't have metadata
			return actual.Pos == expect.Pos
		}
	}
	cmpSource := func(actual seenSource) func(analysistest.AnnotationID) bool {
		return func(expect analysistest.AnnotationID) bool {
			return actual.Pos == expect.Pos && actual.Trace == expect.Meta
		}
	}

	for sink, sources := range actual {
		sinkInstr := sink.Instr
		posSink, ok := position(prog, sinkInstr)
		if !ok {
			// skip invalid positions
			continue
		}
		actualSink := seenSink{Pos: analysistest.RemoveColumn(posSink)}
		for source := range sources {
			if _, ok := seenTaintFlow[actualSink]; !ok {
				seenTaintFlow[actualSink] = map[seenSource]bool{}
			}

			sourceInstr := source.Instr
			posSource, ok := position(prog, sourceInstr)
			if !ok {
				continue
			}
			trace := source.Trace
			if !hasMeta {
				// don't compare traces if the test file annotations do not have metadata
				trace = ""
			}
			actualSource := seenSource{Trace: trace, Pos: analysistest.RemoveColumn(posSource)}
			seen := false
			if expectSources := findExpectSourceIds(expect, cmpSink(actualSink)); len(expectSources) > 0 {
				if _, ok := findExpectSourceID(expectSources, cmpSource(actualSource)); ok {
					seenTaintFlow[actualSink][actualSource] = true
					seen = true
				}
			}
			if !seen {
				msg := fmt.Sprintf("false positive:\n%s\nwith trace: %s\nflows to\n%s\n",
					actualSource.Pos, actualSource.Trace, actualSink.Pos)
				if !hasMeta {
					t.Errorf(msg)
				} else {
					// TODO false positives are logs for now for tests with metadata until context-sensitivity is
					// improved
					t.Logf(msg)
				}
			}
		}
	}

	for expectSinkID, expectSourceIds := range expect {
		sSink := seenSink{Pos: expectSinkID.Pos}
		for expectSourceID := range expectSourceIds {
			sSource := seenSource{Pos: expectSourceID.Pos, Trace: expectSourceID.Meta}
			if !seenTaintFlow[sSink][sSource] {
				// Remaining entries have not been detected!
				if expectSourceID.Meta != "" {
					t.Errorf("failed to detect that source %s:\n%s\nwith trace: %s\nflows to\n%s\n",
						expectSourceID.ID, expectSourceID.Pos, expectSourceID.Meta, expectSinkID.Pos)
				} else {
					t.Errorf("failed to detect that source %s:\n%s\nflows to\n%s\n",
						expectSourceID.ID, expectSourceID.Pos, expectSinkID.Pos)
				}
				if len(seenTaintFlow[sSink]) > 0 {
					// List possible sources for debugging
					t.Logf("Possible sources:\n")
					for source := range seenTaintFlow[sSink] {
						t.Logf("\t%+v\n", source)
					}
				}
			}
		}
	}
}

func checkEscape(t *testing.T, prog *ssa.Program, expect analysistest.TargetToSources,
	actual map[ssa.Instruction]map[ssa.Instruction]bool) {

	seenEscapeFlow := make(map[analysistest.LPos]map[analysistest.LPos]bool)
	cmpPos := func(pos analysistest.LPos) func(analysistest.AnnotationID) bool {
		return func(expectId analysistest.AnnotationID) bool {
			// just compare the positions
			return expectId.Pos == pos
		}
	}

	for escape, sources := range actual {
		escapePos, ok := position(prog, escape)
		if !ok {
			// skip invalid positions
			continue
		}
		posEscape := analysistest.RemoveColumn(escapePos)
		if _, ok := seenEscapeFlow[posEscape]; !ok {
			seenEscapeFlow[posEscape] = map[analysistest.LPos]bool{}
		}
		for source := range sources {
			sourcePos, ok := position(prog, source)
			if !ok {
				// skip invalid positions
				continue
			}
			posSource := analysistest.RemoveColumn(sourcePos)
			seen := false
			if expectSources := findExpectSourceIds(expect, cmpPos(posEscape)); len(expectSources) > 0 {
				if _, ok := findExpectSourceID(expectSources, cmpPos(posSource)); ok {
					seenEscapeFlow[posEscape][posSource] = true
					seen = true
				}
			}
			if !seen {
				t.Errorf("false positive:\n%s\n escapes at\n%s\n", posSource, posEscape)
			}
		}
	}

	for sinkID, sources := range expect {
		for sourceID := range sources {
			if !seenEscapeFlow[sinkID.Pos][sourceID.Pos] {
				// Remaining entries have not been detected!
				t.Errorf("failed to detect that:\n%s\nescapes at\n%s\n", sourceID.Pos, sinkID.Pos)
			}
		}
	}
}

// findExpectSourceIds returns all the source ids that match the target according to cmp.
func findExpectSourceIds(targetToSources analysistest.TargetToSources,
	cmp func(analysistest.AnnotationID) bool) map[analysistest.AnnotationID]bool {
	res := make(map[analysistest.AnnotationID]bool)
	for target, sources := range targetToSources {
		if cmp(target) {
			for source := range sources {
				res[source] = true
			}
		}
	}

	return res
}

func findExpectSourceID(sources map[analysistest.AnnotationID]bool,
	cmp func(analysistest.AnnotationID) bool) (analysistest.AnnotationID, bool) {
	for source := range sources {
		if cmp(source) {
			return source, true
		}
	}

	return analysistest.AnnotationID{}, false
}

func checkExpectedPositions(t *testing.T, p *ssa.Program, flows *Flows, expectTaint analysistest.TargetToSources,
	expectEscapes analysistest.TargetToSources) {
	checkTaint(t, p, expectTaint, flows.Sinks)
	checkEscape(t, p, expectEscapes, flows.Escapes)
}

func noErrorExpected(_ error) bool {
	return false
}

// expectTaintCondInFuncs returns a function that returns true when the supplied
// CondError's callee is in funcNames.
//
// Note: the tests are implemented this way because *ssa.If does not store any position data
func expectTaintedCondInFuncs(funcNames ...string) func(error) bool {
	return func(err error) bool {
		var e *CondError
		if !errors.As(err, &e) {
			return false
		}

		for _, calleeName := range funcNames {
			if e.ParentName == calleeName {
				return true
			}
		}

		return false
	}
}

// runTest runs a test instance by building the program from all the files in files plus a file "main.go", relative
// to the directory dirName
func runTest(t *testing.T, dirName string, files []string, summarizeOnDemand bool, errorExpected func(e error) bool) {
	// Change directory to the testdata folder to be able to load packages
	_, filename, _, _ := runtime.Caller(0)
	dir := filepath.Join(filepath.Dir(filename), "..", "..", "testdata", "src", "taint", dirName)
	err := os.Chdir(dir)
	if err != nil {
		panic(err)
	}

	// The LoadTest function is relative to the testdata/src/taint-tracking-inter folder, so we can
	// load an entire module with subpackages
	lp := analysistest.LoadTest(t, ".", files)
	program := lp.Program
	cfg := lp.Config
	cfg.LogLevel = int(config.InfoLevel)
	cfg.SummarizeOnDemand = summarizeOnDemand
	result, err := Analyze(cfg, lp.LoadedProgram)
	if err != nil {
		for _, err := range result.State.CheckError() {
			if !errorExpected(err) {
				t.Errorf("taint analysis returned error: %v", err)
			}
		}
	}

	expectSinkToSources, expectEscapeToSources := analysistest.GetExpectedTargetToSources(dir, ".")
	checkExpectedPositions(t, program, result.TaintFlows, expectSinkToSources, expectEscapeToSources)
	// Remove reports - comment if you want to inspect
	if err := os.RemoveAll(cfg.ReportsDir); err != nil {
		t.Fatalf("failed to remove dir %v: %v", cfg.ReportsDir, err)
	}
}

func TestAll(t *testing.T) {
	_, filename, _, _ := runtime.Caller(0)
	dir := filepath.Join(filepath.Dir(filename), "..", "..", "testdata", "src", "taint", "basic")
	err := os.Chdir(dir)
	if err != nil {
		panic(err)
	}
	sink2source, _ := analysistest.GetExpectedTargetToSources(dir, ".")
	for sink, sources := range sink2source {
		for source := range sources {
			fmt.Printf("Source %s -> sink %s\n", formatutil.SanitizeRepr(source), formatutil.SanitizeRepr(sink))
		}
	}
}
