#!/usr/bin/env bash
# Spike 3: link ocamlrun (OCaml 4.14.2 + the verified generational GC) with
# the sweep probe compiled in (-DSPIKE_SWEEP_PROBE) and spike 2's par_env.
#   _build/sweep/ocamlrun       plain, system compiler, stock runtime objects
#   _build/sweep/ocamlrun_tsan  ThreadSanitizer, whole runtime instrumented
# Run from spike/parallel/ after `make setup` in generational/ocaml-integration
# and spike 2's extraction into _extract_fill/.
set -eu
HERE=$(pwd)
GI=$HERE/../../generational/ocaml-integration
SNAP=$HERE/../../generational/snapshot
OC=$GI/ocaml-4.14-verified-gen
TSAN_CC=${TSAN_CC:-/usr/local/opt/llvm@18/bin/clang}   # see Spike 2, ThreadSanitizer
INC="-include $SNAP/compat.h -I$SNAP -I$SNAP/internal -I$SNAP/krmllib -I$SNAP/krmllib/krml
     -I$SNAP/krmllib/krml/internal -I$GI -I$OC/runtime -I$OC -Ic -I_extract_fill"
CF="-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function
    -DSPIKE_SWEEP_PROBE $INC"
SRC="$SNAP/GC_Gen_Impl.c $SNAP/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c
     $SNAP/krmlinit.c $SNAP/compat.c $GI/verified_gc/alloc_gen.c c/par_env.c c/sweep_probe.c"
LIBS="-lm -lpthread -Wl,-no_compact_unwind"
mkdir -p _build/sweep

# Plain: the runtime objects `make setup` built, as they are.
cc -O2 $CF -o _build/sweep/ocamlrun $SRC $OC/runtime/prims.o $OC/runtime/libcamlrun.a $LIBS

# TSan: rebuild the bytecode runtime itself with -fsanitize=thread in a copy of
# the tree, so the interpreter's own heap accesses are instrumented too.
T=_build/sweep/ocaml-tsan
if [ ! -f $T/runtime/libcamlrun.a ]; then
  rm -rf $T && mkdir -p $T && cp -R $OC/. $T/
  rm -f $T/runtime/verified_gc $T/runtime/*.o $T/runtime/*.a
  make -C $T/runtime -j8 libcamlrun.a prims.o CC="$TSAN_CC" \
    OC_CFLAGS="-O1 -g -fsanitize=thread -fno-strict-aliasing -fwrapv -pthread"
fi
$TSAN_CC -O1 -g -fsanitize=thread $CF -o _build/sweep/ocamlrun_tsan $SRC \
  $T/runtime/prims.o $T/runtime/libcamlrun.a $LIBS
