
# Reachability Tool

Several of the AR-Go-Tools use the reachability algorithm in analysis/reachability.  This algorithm performs a whole-program analysis of which functions are called either directly or via an interface.  It is less conservative than the x/tools AllFunctions but more conservative than the pointer analysis.  

The reachability tool is a thin wrapper around the reachability algorithm, dumping a complete list of every function that the algorithm considers to be reachable.  The tool exists to allow deep dives into the results of other tools, such as dependencies or packagescan.  While other tools can provide a summary of package reachability, the reachabilty tool can provide the supporting function-level data which can then be filtered to determine which specific functions are responsible for package inclusion.  

The reachability tool reports on every function that it deems reachable from either the global initialization function (main.init) or the global main function (main.main).  In order to understand which functions are reachable from each of these, it supports two command line arguments to suppress starting from main.init (-noinit) or main.main (-nomain).  

Running reachability three times with (a) no arguments, (b) -noinit, and (c) -nomain and piping the output through wc gives the size of the set of functions reachable from both, from main, and from  init.  Subtracting the latter two from the first gives the number of functions reachable from only init and only main.  This can help in understanding side effects incurred from merely importing a package.

The reachability algorithm is only one estimate of which functions are needed in the program.  It differs from the estimate offered by the pointer analysis and from which functions are actually linked into the binary by the compiler.  The `compare` tool is provided to better understand these differences.  
