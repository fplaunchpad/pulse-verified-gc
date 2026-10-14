# Makefile for Generational GC
#
# Builds on top of mark-and-sweep (major heap) and common modules.
# Verification: make verify
# Extraction:   make extract  (Custard → _extract/Custard.{c,h}; requires M&S and common verified)
# Snapshot:     make snapshot (copies Custard.{c,h} into snapshot/)

FSTAR_HOME ?= $(CURDIR)/../fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML       ?= $(KRML_HOME)/krml

FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

C = ../common
M = ../mark-and-sweep

OUTPUT_DIR  = _output
EXTRACT_DIR = _extract
SNAPSHOT_DIR = snapshot

# Shared checked-file cache (see the root Makefile).  F* writes
# `M.fst.checked` into --cache_dir, which defaults to the current working
# directory, so every build in this repo points at one explicit directory.
CACHE_DIR ?= ../_cache

# --- F* flags ---------------------------------------------------------------

# Z3 version used for all SMT queries (bundled with the F* installation).
Z3_VERSION ?= 4.15.3

# Z3 4.15.3 regression workaround -- see the root Makefile for details.
# Applied per module (EAGER_QI_CHECKED), never globally: at the raised
# eager-instantiation threshold other modules hang instead.
EAGER_QI ?= --z3smtopt '(set-option :smt.qi.eager_threshold 100)'

# Z3 4.15.3 flakiness workaround -- see the top-level Makefile.
RETRY ?= --retry 3

# Hard per-query wall-clock bound; see the root Makefile for the rationale.
# Some Z3 4.15.3 searches never terminate and never charge the rlimit, so
# `--z3rlimit` alone cannot bound them.
Z3_TIMEOUT ?= --z3smtopt '(set-option :timeout 300000)'

FSTAR_FLAGS = \
  $(RETRY) \
  $(Z3_TIMEOUT) \
  --z3version $(Z3_VERSION) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include spec --include impl \
  --include $(C)/spec --include $(C)/lib --include $(C)/impl \
  --include $(M)/spec --include $(M)/impl

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# --- Sources ----------------------------------------------------------------

SPEC_SRC = $(wildcard spec/*.fst spec/*.fsti)
IMPL_SRC = $(wildcard impl/*.fst impl/*.fsti)

# Exclude SPOT test files from orphan checking (they are tests, not production code)
SPOT_SRC = spec/GC.Gen.SPOT.fst spec/GC.Gen.SPOT.Lemmas.fst impl/GC.Gen.SPOT.Pulse.fst impl/GC.Gen.SPOT.Simple.fst impl/GC.Gen.SPOT.Full.fst
ALL_SRC  = $(filter-out $(SPOT_SRC),$(SPEC_SRC) $(IMPL_SRC))

# All checked files land in one shared cache, so targets are derived from the
# module file name alone.
checked = $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(notdir $(1))))

ROOT_SRC = impl/GC.Gen.Impl.fsti impl/GC.Gen.Impl.fst
ROOT_CHECKED = $(call checked,$(ROOT_SRC))
ALL_CHECKED  = $(call checked,$(ALL_SRC))

# --- Auto-generated dependency graph ----------------------------------------

.depend: Makefile $(ALL_SRC)
	$(FSTAR) --dep full $(ROOT_SRC) --output_deps_to $@.raw
	@awk -v cwd="$$(pwd)/" -v proj="$$(cd .. && pwd)/" ' \
	  { gsub(cwd, ""); gsub(proj, "../") } \
	  /^[^ \t].*:/ { flush(); split($$0, a, ":"); target = a[1]; \
	    keep = (target ~ /\.checked$$/); n = 0; next } \
	  keep { line = $$0; sub(/^[ \t]+/, "", line); sub(/[ \t]*\\?[ \t]*$$/, "", line); \
	    if (line ~ /\.checked$$/) deps[++n] = line } \
	  END { flush() } \
	  function flush() { if (!keep || target == "") return; \
	    print target ": \\"; \
	    for (i=1;i<=n;i++) print "\t" deps[i] (i < n ? " \\" : ""); \
	    print ""; delete deps; n=0 }' $@.raw > $@
	@printf '\nDEP_CHECKED := ' >> $@
	@awk '/^[^ \t].*\.checked:/ { target=$$1; sub(/:$$/, "", target); \
	    print target }' $@ \
	  | sort -u | tr '\n' ' ' >> $@
	@printf '\n' >> $@
	@rm -f $@.raw

# --- Default goal -----------------------------------------------------------

.PHONY: all verify check-orphans extract snapshot clean

all: verify

# Bind every cache target to its source file so `$<` is always the source.
define bind_source
$(CACHE_DIR)/$(notdir $(1)).checked: $(1)
endef
$(foreach s,$(SPEC_SRC) $(IMPL_SRC),$(eval $(call bind_source,$(s))))

-include .depend

# Restrict the dependency closure to this directory's own modules, then map
# each checked file back to the source it was built from.
VERIFY_CHECKED = $(filter $(ALL_CHECKED),$(DEP_CHECKED))
REACHABLE_SRC = $(foreach c,$(VERIFY_CHECKED), \
                  $(filter %/$(patsubst %.checked,%,$(notdir $(c))),$(ALL_SRC)))
ORPHAN_SRC = $(filter-out $(REACHABLE_SRC),$(ALL_SRC))

# --- Pattern rules (verification) -------------------------------------------
#
# One rule for every module; per-module SMT tuning goes through the
# target-specific variable EXTRA_FLAGS.  `private` stops GNU make from
# propagating it to the target's prerequisites.

# Modules that hang at Z3 4.15.3's default eager-instantiation threshold.
#
# Opt-in, not a default: at the raised threshold other modules diverge instead.
# See the top-level Makefile for the rationale.
EAGER_QI_CHECKED = \
  $(CACHE_DIR)/GC.Gen.Cheney.fst.checked \
  $(CACHE_DIR)/GC.Gen.Cheney.Dense.fst.checked \
  $(CACHE_DIR)/GC.Gen.CheneyPreservation.Forwarding.fst.checked \
  $(CACHE_DIR)/GC.Gen.CheneyPreservation.Frame.fst.checked \
  $(CACHE_DIR)/GC.Gen.CheneyPreservation.NonBlueOrigin.fsti.checked \
  $(CACHE_DIR)/GC.Gen.CombinedGraph.fst.checked \
  $(CACHE_DIR)/GC.Gen.MinorCollectForwarding.Edges.fst.checked \
  $(CACHE_DIR)/GC.Gen.MinorCollectForwarding.Reflection.fst.checked \
  $(CACHE_DIR)/GC.Gen.PromoteUpdate.BlueAlloc.fst.checked \
  $(CACHE_DIR)/GC.Gen.Promote.fst.checked \
  $(CACHE_DIR)/GC.Gen.TwoPassEquiv.fst.checked \
  $(CACHE_DIR)/GC.Gen.Impl.Cheney.fst.checked

$(EAGER_QI_CHECKED): private EXTRA_FLAGS = $(EAGER_QI)

# GC.Gen.Promote.fst needs a higher rlimit for abstract heap_size proofs
$(CACHE_DIR)/GC.Gen.Promote.fst.checked: private EXTRA_FLAGS = --z3rlimit_factor 3 $(EAGER_QI)

$(filter-out $(EAGER_QI_CHECKED),$(call checked,$(wildcard impl/*.fst impl/*.fsti))): \
  private EXTRA_FLAGS = --z3rlimit 160

$(filter $(EAGER_QI_CHECKED),$(call checked,$(wildcard impl/*.fst impl/*.fsti))): \
  private EXTRA_FLAGS = --z3rlimit 160 $(EAGER_QI)

$(CACHE_DIR)/%.checked:
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) $(EXTRA_FLAGS) $<

$(OUTPUT_DIR):
	@mkdir -p $@

# Verify the GC.Gen.Impl root closure and fail if new orphan modules appear.
check-orphans:
	@if [ -n "$(strip $(ORPHAN_SRC))" ]; then \
	  echo "=== unreachable generational modules from $(ROOT_SRC) ==="; \
	  printf '  %s\n' $(ORPHAN_SRC); \
	  exit 1; \
	fi

verify: check-orphans $(VERIFY_CHECKED)
	@echo "=== GC.Gen.Impl root closure verified ==="

# === Extraction (F* → C, via Custard) =======================================
#
# Extracts generational impl + mark-and-sweep impl + common impl into a
# single self-contained C translation unit, _extract/Custard.{c,h}, with F*'s
# Custard backend (--codegen Custard --custard_backend C).  No KaRaMeL and no
# krmllib: Custard's C needs only <stdint.h> and friends.
#
# Prerequisites: M&S and common .checked files must already exist
# (run `make -C ../mark-and-sweep verify` first if needed).

# Public API (external linkage, declared in Custard.h): every definition of
# these modules.  Everything else reachable from them is emitted `static`.
CUSTARD_API_MODS = \
  GC.Gen.Impl GC.Gen.Impl.MinorHeap GC.Gen.Impl.Cheney GC.Gen.Impl.UpdatePtrs \
  GC.Impl GC.Impl.Allocator GC.Impl.MarkBounded

# Globals the hand-written runtime glue reads or writes, that are not already
# public through CUSTARD_API_MODS:
#   - minor_heap_size_u64, max_young_wosize_u64, minor_base_addr are set by
#     the OCaml bridge at runtime;
#   - minor_heap_size_sz, fwd_arr_size_sz are derived from minor_heap_size_u64.
#     Custard folds their initialisers from the .fst value (2048), so
#     snapshot/krmlinit.c recomputes them after the bridge has configured the
#     nursery, exactly as KaRaMeL's krmlinit_globals used to.
CUSTARD_ENTRIES = \
  GC.Gen.Base.minor_heap_size_u64 GC.Gen.Base.max_young_wosize_u64 \
  GC.Gen.Base.minor_base_addr \
  GC.Gen.Impl.MinorHeap.minor_heap_size_sz GC.Gen.Impl.MinorHeap.fwd_arr_size_sz

# Emit public names unqualified (as KaRaMeL's -no-prefix did), so that the
# bridge's names (heap_t, allocate, gen_gc, zero_addr, read_u64_le, ...) are
# unchanged.
CUSTARD_NO_PREFIX = \
  $(CUSTARD_API_MODS) GC.Gen.Base GC.Impl.Heap GC.Impl.Stack \
  GC.Impl.ArrayWord GC.Spec.ZeroAddr GC.Lib.Header

CUSTARD_FLAGS = \
  --codegen Custard --custard_backend C \
  --custard_monomorphize_types true \
  $(foreach m,$(CUSTARD_API_MODS),--custard_entry_module $(m)) \
  $(foreach e,$(CUSTARD_ENTRIES),--custard_entry $(e)) \
  $(foreach m,$(CUSTARD_NO_PREFIX),--custard_c_no_prefix $(m))

$(EXTRACT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR)/Custard.c: verify | $(EXTRACT_DIR)
	$(FSTAR) --odir $(EXTRACT_DIR) $(CUSTARD_FLAGS) impl/GC.Gen.Impl.fst

extract: $(EXTRACT_DIR)/Custard.c
	@echo "=== Extraction complete: $(EXTRACT_DIR)/Custard.{c,h} ==="

# --- Snapshot ---------------------------------------------------------------
#
# Only the generated pair is copied.  krmlinit.{c,h} and compat.{c,h} in
# snapshot/ are hand-written glue and are left alone.

snapshot: extract
	@echo "=== Creating snapshot ==="
	@cp $(EXTRACT_DIR)/Custard.c $(EXTRACT_DIR)/Custard.h $(SNAPSHOT_DIR)/
	@echo "=== Snapshot updated ==="

# --- Cleanup ----------------------------------------------------------------

clean:
	rm -f $(ALL_CHECKED)
	rm -f .depend .depend.raw
	rm -rf $(OUTPUT_DIR) $(EXTRACT_DIR)
