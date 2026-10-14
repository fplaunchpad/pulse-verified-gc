# Standalone build for the verified generational GC snapshot.
#
# This compiles the Custard-extracted C code (Custard.{c,h}) without needing
# F* installed. Custard's C is self-contained: no krmllib.
#
# Usage:
#   make            Build and run the test harness
#   make test       Same as above
#   make clean      Remove build artifacts

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable

CFLAGS += -I.
CFLAGS += -include compat.h

LIB_SOURCES = Custard.c custard_glue.c compat.c
SOURCES = $(LIB_SOURCES) main.c
TARGET  = gc_gen_test
DEPS    = Custard.h custard_glue.h compat.h

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
