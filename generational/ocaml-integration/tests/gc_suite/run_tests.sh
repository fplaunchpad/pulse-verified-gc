#!/bin/sh
# Build and run each test, then compare against the output the stock
# OCaml 4.14.1 GC produces. All values are deterministic, so a different
# number means corruption rather than just a crash.
#
# Run in bytecode and native separately. Bytecode passes today. Native is
# where the infix gap appeared.

set -u
OCAMLC=${OCAMLC:-ocamlc}
OCAMLOPT=${OCAMLOPT:-ocamlopt}
MODE=${1:-both}

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

pass=0
fail=0

expected_for() {
  awk -v t="=== $1" '$0==t{f=1;next} /^=== /{f=0} f' expected_output.txt
}

run_one() {
  base=$1; mode=$2; exe=$3
  printf '%-22s %-9s ' "$base" "$mode"
  if ! "$exe" > "$TMP/$base.$mode.out" 2>"$TMP/$base.$mode.err"; then
    printf 'FAIL (exit %d)\n' $?
    sed 's/^/    /' "$TMP/$base.$mode.err" | head -5
    fail=$((fail+1)); return
  fi
  if expected_for "$base" | diff -q - "$TMP/$base.$mode.out" >/dev/null 2>&1; then
    printf 'ok\n'; pass=$((pass+1))
  else
    printf 'OUTPUT DIFFERS\n'
    printf '    expected: %s\n' "$(expected_for "$base" | tr '\n' ' ')"
    printf '    got:      %s\n' "$(tr '\n' ' ' < "$TMP/$base.$mode.out")"
    fail=$((fail+1))
  fi
}

for f in t*.ml; do
  base=$(basename "$f" .ml)

  if [ "$MODE" = both ] || [ "$MODE" = byte ]; then
    if $OCAMLC -o "$TMP/$base.byte" "$f" 2>"$TMP/$base.cerr"; then
      run_one "$base" bytecode "$TMP/$base.byte"
    else
      printf '%-22s %-9s COMPILE FAIL\n' "$base" bytecode
      sed 's/^/    /' "$TMP/$base.cerr" | head -5
      fail=$((fail+1))
    fi
  fi

  if [ "$MODE" = both ] || [ "$MODE" = native ]; then
    if $OCAMLOPT -o "$TMP/$base.exe" "$f" 2>"$TMP/$base.oerr"; then
      run_one "$base" native "$TMP/$base.exe"
    else
      printf '%-22s %-9s COMPILE FAIL\n' "$base" native
      sed 's/^/    /' "$TMP/$base.oerr" | head -5
      fail=$((fail+1))
    fi
  fi

  rm -f "$base".cm* "$base".o
done

echo
echo "passed $pass, failed $fail"
[ "$fail" -eq 0 ]
