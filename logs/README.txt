===============================================
How to build and test LLVM using souper?
===============================================

-------------------------
Section A: Requirements
-------------------------
1. Machine: Ubuntu-14.04.4 (x86_64)
2. cmake - 3.6.0 (version must be 3.4.3 or higher)
   URL: https://cmake.org/download/
3. Z3 solver - 4.4.1
   URL: https://github.com/Z3Prover/z3
4. Redis - 3.2.1
   URL: http://redis.io/download
5. clang - 3.8.1
   URL: http://llvm.org/releases/download.html 
6. Redigo Redis client (If you've Go installed already).
   Set $GOPATH=<path_to_workspace_directory>
   $ go get github.com/garyburd/redigo/redis

-----------------------------
Section B: Building Souper
-----------------------------
1. Download or clone the git repository
   $ git clone https://github.com/google/souper.git

2. Build dependencies
   $ cd souper/
   $ ./update_deps.sh Release
   Here, Release is the default build type and can be set to any other LLVM build type too.

3. Run make from build directory
   $ mkdir <path_to_build_dir> && cd <path_to_build_dir>
   $ cmake -DCMAKE_BUILD_TYPE=Release $EXTRA_CMAKE_FLAGS $SOLVER <path_to_souper>
     - The build type defaults to Release and can be any of the other LLVM build type too.
       The build type must be same as the one passed to build dependencies.
     - $EXTRA_CMAKE_FLAGS are usually used to specify the path of compiler used to
       build souper. Example, -DCMAKE_C_COMPILER=<path_to_clang-3.8.1>, -DCMAKE_CXX_COMPILER=<path_to_clang++-3.8.1>
     - $SOLVER : specify the solver option as: -DTEST_SOLVER="-z3-path=<path_to_z3_binary>"

4. Run 'make' from souper's build directory

5. Run 'make check' to run Souper's testsuite.

------------------------------------------------------------------------
Section C: Environment variables to be set to build LLVM using souper
------------------------------------------------------------------------
There are a lot of options you can set as per your requirements. You can check
in souper's help menu: "souper --help"
- Set the solver path
  export $SOUPER_SOLVER="-z3-path=path/to/z3/solver/binary"
- To see the number of optimizations and count of static profile of all optimizations, you can set:
  export SOUPER_STATIC_PROFILE=1
- To allow constant synthesis, you can set:
  export SOUPER_INFER_INT=1
- To keep going if there are solver errors because of out of memory or timeout
  export SOUPER_IGNORE_SOLVER_ERRORS=1

--------------------------------------------------------
Section D: How to use Redis to build LLVM using souper?
--------------------------------------------------------
1. Make sure redis-server is not already running. You can check
   this as follows:
   $ redis-cli ping
   - If the output is: Could not connect to Redis at 127.0.0.1:6379: Connection refused
     This means redis-server is 'not' running
   - If the output is: PONG
     This means redis-server is running. You can turn it off as:
     $ redis-cli shutdown

2. Make sure no keyvalues are stored in redis already
   $ redis-cli info

   At the end of the info log, if you find:
   --------------------------------------
   cluster_enabled:0
   # Keyspace
   This information log doesn't give any values of keys, it indicates redis-server has
   no keyvalues stored in it. It is good to be used.
   --------------------------------------
   cluster_enabled:0
   # Keyspace
  db0:keys=14,expires=0,avg_ttl=0i
  The keys shown in last lines indicate that redis already has saved some keys.
  Find dump.rdb file in your system and delete them.
   

------------------------------------------------
Section E: How to build LLVM using souper?
------------------------------------------------
1. Download the LLVM-3.8.1 toolchain: http://llvm.org/releases/download.html

2. Set up the source directory.
   - Untar the llvm source
     $ tar -xf llvm-3.8.1.src.tar.xz
     $ cd llvm-3.8.1.src/

   - Untar the clang source in /path/to/llvm/tools/ directory 
     $ tar -xf /path/to/cfe-3.8.1.src.tar.xz -C tools/

   - Rename clang's source from tools/cfe-* to tools/clang
     $ mv tools/cfe-3.8.1.src tools/clang

3. Configure from build directory
   $ mkdir path/to/llvm_build_dir
   $ path/to/llvm_source/configure --prefix=path/to/install (Setting the prefix is optional)

4. Run redis-server
   Before running the redis-server, make sure it's not being used and doesn't have any key values
   stored in it. See Section D above and then run the following command.

   $ path/to/redis-server

5. When you build llvm using souper, Souper queries the SMT solver to find the optimizations.
   Solvers usually tend to use a lot of memory space. It is good to restrict the memory usage before
   running the 'make' command to build LLVM. In this example, the maximum memory size and virtual
   memory size is limited to 2GB.
   $ ulimit -m 2000000 -v 2000000

6. Build clang from build directory
   $ cd path/to/llvm_build_dir (as mentioned in Step 3)
   $ make CC=path/to/sclang CXX=path/to/sclang++

7. Install and Test clang
   $ mkdir path/to/install/directory
   $ make install
   $ make check-all

8. Dump the cached optimizations data from redis as:
   $ path/to/souper_build_dir/cache_dump
