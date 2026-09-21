# Standalone build for the verified generational GC snapshot.
#
# This compiles the KaRaMeL-extracted C code without needing F* or KaRaMeL
# installed. The krmllib/ headers are vendored in this directory.
#
# Usage:
#   make            Build and run the test harness
#   make test       Same as above
#   make clean      Remove build artifacts

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable

# krmllib headers are vendored under krmllib/
CFLAGS += -I. -Iinternal -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal
CFLAGS += -include compat.h

LIB_SOURCES = GC_Gen_Impl.c GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c krmlinit.c compat.c
SOURCES = $(LIB_SOURCES) main.c
TARGET  = gc_gen_test
DEPS    = GC_Gen_Impl.h internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h

# Size-exactness of the allocator, driven directly rather than through the
# OCaml testsuite: the one-word-leftover case is presented on every run
# instead of depending on allocation history. Seconds, no F*, no OCaml.
ALLOC_TARGET = alloc_exact_test

.PHONY: all test clean alloc-exact-test

all: test

test: $(TARGET)
	./$(TARGET)

alloc-exact-test: $(ALLOC_TARGET)
	./$(ALLOC_TARGET)

$(TARGET): $(SOURCES) $(DEPS)
	$(CC) $(CFLAGS) $(SOURCES) -o $@

$(ALLOC_TARGET): $(LIB_SOURCES) alloc_exact_test.c $(DEPS)
	$(CC) $(CFLAGS) $(LIB_SOURCES) alloc_exact_test.c -o $@

clean:
	rm -f $(TARGET) $(ALLOC_TARGET)
