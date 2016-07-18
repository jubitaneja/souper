===============================================
How to build and test LLVM using souper?
===============================================

Requirements
----------------
1. cmake version 3.4.3 or higher
2. Z3 solver
3. Redis
4. Latest toolchain of llvm to compile souper
5. Redigo Redis client (If you've Go installed already).
   Set $GOPATH=<path_to_workspace_directory>

Building Souper
----------------
1. Download or clone the git repository: https://github.com/google/souper.git
2. Build dependencies:
   ./update_deps.sh $BUILD_TYPE
   - $BUILD_TYPE defaults to Release and can be set to any LLVM build type
3. Run make from build directory
   $ mkdir <path_to_build_dir> && cd <path_to_build_dir>
   $ cmake -DCMAKE_BUILD_TYPE=$BUILD_TYPE $EXTRA_CMAKE_FLAGS $SOLVER <path_to_souper>
     - The build type defaults to Release and can be any of the LLVM build type.
       The build type must be same as the one passed to build dependencies.
     - $EXTRA_CMAKE_FLAGS are usually used to specify the path of compiler used to
       build souper. Example, -DCMAKE_C_COMPILER=<path_to_clang>, -DCMAKE_CXX_COMPILER=<path_to_clang++>
     - $SOLVER : specify the solver path if you want to test Souper fully with its test suite.
       Specify the flag as: -DTEST_SOLVER="-z3-path=<path_to_z3_binary>"
4. Run 'make' from souper-build directory
5. Run 'make check' to run Souper's testsuite.

Environment variables to be set to build LLVM using souper
----------------------------------------------------------
There are a lot of options you can set as per your requirements. You can check
in souper's help menu: "souper --help"
To see the number of optimizations and count of static profile of all optimizations, you can set:
export SOUPER_STATIC_PROFILE=1
To allow constant synthesis, you can set:
export SOUPER_INFER_INT=1

How to build LLVM using souper?
--------------------------------
1. Download or clone the LLVM toolchain: http://llvm.org/releases/download.html
2. Set up the source directory.
   Untar the llvm source
   $ cd path/to/llvm_source
   Untar the clang source in /path/to/llvm/tools/ directory 
   Rename clang's source from tools/cfe-* to tools/clang
3. Configure from build directory
   $ mkdir path/to/llvm_build_dir
   $ path/to/llvm_source/configure --prefix=path/to/install (Setting the prefix is optional)
4. Run redis-server, if you want to cache the optimizations and want to see their total 
   count or profiling information.
5. Build clang from build directory
   $ cd path/to/llvm_build_dir (as mentioned in Step 3)
   $ make CC=path/to/sclang CXX=path/to/sclang++
6. Install and Test
   $ make install
   $ make check
7. Dump the cached optimizations data from redis as:
   $ path/to/souper_build_dir/cache_dump

NOTE:
-------
When you build llvm using souper, Souper queries the SMT solver to find the optimizations.
Solvers usually tend to use a lot of memory space. You can restrict the memory usage before
running the 'make' command to build LLVM.
$ ulimit -m 2000000 -v 2000000
In this example, the maximum memory size and virtual memory size is limited to 2GB.
