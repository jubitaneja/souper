#!/bin/sh -e

llvm_build_type=Release

llvm_srcdir=third_party/llvm
llvm_installdir=$(pwd)/${llvm_srcdir}/$llvm_build_type-sound
llvm_builddir=$(pwd)/${llvm_srcdir}/${llvm_build_type}-build-sound

z3_installdir=$(pwd)/third_party/z3-install
export PATH=$z3_installdir/bin:$PATH

mkdir -p $llvm_builddir

cmake_flags=".. -DCMAKE_INSTALL_PREFIX=$llvm_installdir -DLLVM_ENABLE_ASSERTIONS=On -DLLVM_TARGETS_TO_BUILD=host -DCMAKE_BUILD_TYPE=$llvm_build_type -DZ3_INCLUDE_DIR=$z3_installdir/include -DZ3_LIBRARIES=$z3_installdir/lib/libz3.a -DZ3_EXECUTABLE=$z3_installdir/bin/z3"

if [ -n "`which ninja`" ] ; then
  (cd $llvm_builddir && cmake -G Ninja $cmake_flags "$@")
  ninja -C $llvm_builddir
  ninja -C $llvm_builddir install
else
  (cd $llvm_builddir && cmake $cmake_flags "$@")
  make -C $llvm_builddir -j8
  make -C $llvm_builddir -j8 install
fi
# we want these but they don't get installed by default
cp $llvm_builddir/bin/llvm-lit $llvm_installdir/bin
cp $llvm_builddir/bin/FileCheck $llvm_installdir/bin
cp $llvm_builddir/lib/libgtest_main.a $llvm_installdir/lib
cp $llvm_builddir/lib/libgtest.a $llvm_installdir/lib


