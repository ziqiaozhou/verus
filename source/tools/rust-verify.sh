#! /bin/bash

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
fi

case $(uname -m) in
  x86_64)
    ARCH=x86_64
    ;;
  arm64)
    ARCH=aarch64
    ;;
  *)
    echo "Unknown architecture $(uname -m)" 1>&2
    exit 1
    ;;
esac

VERUS_Z3_PATH="$(pwd)/z3" DYLD_LIBRARY_PATH=../rust/install/lib/rustlib/${ARCH}-apple-darwin/lib LD_LIBRARY_PATH=../rust/install/lib/rustlib/${ARCH}-unknown-linux-gnu/lib ../rust/install/bin/rust_verify --pervasive-path pervasive --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/libbuiltin_macros.$DYN_LIB_EXT --extern state_machines_macros=../rust/install/bin/libstate_machines_macros.$DYN_LIB_EXT --edition=2018 $@
