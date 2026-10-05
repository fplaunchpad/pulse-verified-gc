#!/usr/bin/env bash
# Compile the extracted C of spike 2 with the hand-written par_env body:
# a plain build, a ThreadSanitizer build, and the racy TSan control.
# Run from spike/parallel/ after extraction into _extract_fill/.
set -eu
K=../../fstar
INC="-Ic -I_extract_fill -I$K/include/krml -I$K/lib/krml/dist/minimal"
CF="-std=c11 -Wall -Wextra -g -O1 $INC"
# Apple clang 12's TSan runtime segfaults on macOS 15 even for an empty main,
# so the TSan builds use Homebrew LLVM 18.
TSAN_CC=${TSAN_CC:-/usr/local/opt/llvm@18/bin/clang}
SRC="c/par_env.c c/thread_probe.c _extract_fill/Spike_FillHalves.c"
mkdir -p _build
clang $CF -o _build/test_fill c/test_fill.c $SRC -lpthread
$TSAN_CC $CF -fsanitize=thread -o _build/test_fill_tsan c/test_fill.c $SRC
$TSAN_CC $CF -fsanitize=thread -o _build/tsan_control c/tsan_control.c $SRC
