# Verified Generational GC — OCaml 4.14 Integration

Drop-in replacement for OCaml 4.14's garbage collector using a **verified
generational GC** (Cheney minor + mark-and-sweep major) extracted from F*/Pulse
to C via KaRaMeL.

## Architecture

```
OCaml 4.14 runtime (patched: memory.h, interp.c, minor_gc.c, ...)
    ↓ inline minor bump allocation; verified_allocate_minor() slow path
alloc_gen.c (bridge: root scanning, minor/major collection, heap init)
    ↓ minor_alloc(), allocate(), minor_collect_full(), gen_gc()
GC_Gen_Impl.c (KaRaMeL-extracted verified code)
```

### Three layers

1. **GC_Gen_Impl.c** — KaRaMeL-extracted verified code.  Contains both the
   generational (minor bump + Cheney BFS promotion) and mark-and-sweep (major)
   collectors.  Zero hand-written logic — all code extracted from verified
   F*/Pulse source.

2. **alloc_gen.c** — C bridge layer.  Provides the shared minor
   bump pointer used by the inline `Alloc_small` fast path,
   `verified_allocate_minor()` for the small-allocation slow path, and
   `verified_allocate()` for shared/major allocation.  Handles:
   - NULL-base trick for major heap (offsets = absolute addresses)
   - Root scanning via `caml_do_roots`
   - Minor→major address translation for roots
   - Inter-generational pointer handling via OCaml's `caml_ref_table`
   - Gray stack management for major GC

3. **runtime_gen.patch** — OCaml runtime modifications (~250 lines).  Patches
   `memory.h` (inline minor allocation plus slow-path `verified_allocate_minor`),
   `memory.c` (caml_alloc_shr), `interp.c` (Setup_for_gc), `minor_gc.c`
   (disable native GC).

## Quick start

```bash
# 1. Set up (clone OCaml, apply patches, build runtimes)
make setup

# 2. Run smoke tests
make test

# 3. Run benchmarks (requires hyperfine)
make benchmark
```

## Compiling and running your own `.ml` file

Both compilers live in the OCaml tree. The `.opt` binaries are native and
self-contained, so use those. One variable for the rest of this section:

```bash
GC=$(pwd)/ocaml-4.14-verified-gen      # from generational/ocaml-integration
```

### Bytecode

```bash
$GC/ocamlc.opt -nostdlib -I $GC/stdlib \
               -use-runtime $GC/runtime/ocamlrun \
               -o prog.byte prog.ml
./prog.byte
```

`-use-runtime` is not optional. Without it the executable's header names
whatever runtime this compiler was configured with — `/usr/local/bin/ocamlrun`,
a stock install. On a machine without one you get
`bad interpreter: no such file or directory`; on a machine *with* one your test
runs happily on the **stock** collector and tells you nothing.

### Native

```bash
$GC/ocamlopt.opt -nostdlib -I $GC/runtime -I $GC/stdlib \
                 -o prog.exe prog.ml
./prog.exe
```

**`-I $GC/runtime` must come before `-I $GC/stdlib`.** The verified collector is
not a separate library — it is archived *inside* `libasmrun.a`
(`runtime/Makefile`, the `libasmrun.$(A)` rule extracts `libvergc_gen_native.a`
into it), so nothing on the command line mentions the GC. But the tree keeps
**two copies** of that archive:

| path | what it is |
|---|---|
| `runtime/libasmrun.a` | the build output; always current |
| `stdlib/libasmrun.a` | a copy, refreshed only by `make runtimeopt` |

`-I` dirs are searched in the order given, so listing `runtime` first links the
build output. List `stdlib` first — or omit `-I $GC/runtime` — and you link the
copy, which may be from any earlier build. That failure is silent: the program
compiles, links, runs, and passes against an old collector.

### After changing the GC

Any edit to the F\* source, the snapshot, or a hand patch needs all three of
these, in order:

```bash
make -C verified_gc                                # rebuild GC_Gen_Impl.o etc.
cd ocaml-4.14-verified-gen && make runtime runtimeopt
```

`make runtime runtimeopt` both builds the archives *and* propagates them into
`stdlib/`. Note that `make -C runtime all allopt` builds them but does **not**
propagate — and that `make coldstart` builds only the bytecode flavours, so
after a coldstart alone there is no `libasmrun.a` to link native against at all.

Switching git branches counts as changing the GC: the snapshot is tracked but
the build artifacts are not, so they survive the checkout and are then stale.

### Confirming which collector you actually got

Worth doing once per setup, because every way of getting this wrong is silent.

```bash
# native: the verified entry points should be present
nm prog.exe | grep -E 'verified_allocate|minor_collect_full|find_infix_parents'

# bytecode: the header should name the in-tree runtime
head -1 prog.byte
```

Presence of those symbols proves *a* verified GC is linked, not that it is the
*current* one — a stale `stdlib/libasmrun.a` contains them too. If that matters,
compare the archives directly:

```bash
cmp $GC/runtime/libasmrun.a $GC/stdlib/libasmrun.a && echo in-sync
```

### Scope: what this does and does not exercise

Compiling a file this way runs **your program** on the verified collector. It
does not run the *compiler* on it: `ocamlc.opt` and `ocamlopt.opt` are prebuilt
binaries with a collector of their own vintage statically linked in, and they
are unaffected by the rebuild steps above.

To put the current collector under the compiler itself you have to rebuild the
compiler with it, which is what `make coldstart` (bytecode, stdlib bootstrap)
and `make world.opt` (native, ~900 `ocamlopt` invocations) do. Those are also
the strongest tests available, since a collector broken enough to matter cannot
complete a bootstrap.

## Trust boundary

| Component | Lines | Why trusted |
|-----------|-------|-------------|
| `alloc_gen.c` | ~250 | Bridge: root scanning, address translation, heap init |
| NULL-base patches | ~20 | 6 patches to GC_Gen_Impl.c for absolute addressing |
| `runtime_gen.patch` | ~250 | OCaml runtime modifications |
| `krmlinit.c` | ~25 | Derived constant initialization |
| `compat.c` | ~5 | Missing `FStar_UInt64_ne` shim |
| `caml_ref_table` completeness | — | Same trust as stock OCaml |

Everything else is KaRaMeL-extracted from verified F*/Pulse code with zero admits.

## Configuration

Set `MIN_EXPANSION_WORDSIZE` environment variable to control major heap size
(in words).  Default: 32M words (256MB).

Minor heap size is set at runtime with `MINOR_HEAP_WORDS`.  The default is
256K words (2MB), matching OCaml's default, with a floor large enough for
`Max_young_wosize`.
