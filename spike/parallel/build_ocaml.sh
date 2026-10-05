#!/usr/bin/env bash
# Link the extracted C (plus par_env.c) into an OCaml 4.14.0 program through a
# C stub, as bytecode (-custom) and native.  Run from spike/parallel/.
set -eu
HERE=$(pwd)
K=$HERE/../../fstar
OX="opam exec --switch=4.14.0 --"
INC="-I$HERE/c -I$HERE/_extract_fill -I$K/include/krml -I$K/lib/krml/dist/minimal"
mkdir -p _build/ocaml
cp ocaml/main.ml _build/ocaml/
cd _build/ocaml
for c in $HERE/ocaml/fill_stub.c $HERE/c/par_env.c $HERE/c/thread_probe.c $HERE/_extract_fill/Spike_FillHalves.c; do
  $OX ocamlc -c -ccopt "-std=c11 -Wall -Wextra $INC" "$c"
done
OBJS="fill_stub.o par_env.o thread_probe.o Spike_FillHalves.o"
$OX ocamlc -custom -o main.byte main.ml $OBJS -cclib -lpthread
$OX ocamlopt -o main.native main.ml $OBJS -cclib -lpthread
