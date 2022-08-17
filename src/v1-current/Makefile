SHELL=/bin/bash

# Detect number of cores
NPROCS := 32

# TODO: This doesn't actually work for some reason
# ifdef NUMBER_OF_PROCESSORS # Windows
# 	NPROCS := $(NUMBER_OF_PROCESSORS) \
# else
# 	OS := $(shell uname -s) \
# 	ifeq($(OS),Linux) # Linux
# 		NPROCS := $(shell grep -c '^processor' /proc/cpuinfo) \
# 	endif
# 	ifeq($(OS),Darwin) # Mac OS X
# 		NPROCS := $(shell system_profiler | awk '/Number Of CPUs/{print $4}{next;}') \
# 	endif
# endif

# Make these cores work
MAKEFLAGS := --jobs=$(NPROCS)

COQFLAGS?=

EXEs := coqc coqdoc
_ := $(foreach exe,$(EXEs),\
				$(if $(shell which $(exe)),\
						$(eval $(exe) := $(exe)),\
						$(if $(shell which $(exe).exe),\
							$(eval $(exe) := $(exe).exe),\
							$(error "No $(exe) or $(exe).exe in PATH"))))

CLEANING_LIST := %.aux %.glob %.o %.vo %.vio %.vok %.vos %.html

targets := Basic Common CC Kleene Implementation SP BranchingOrder Merge EPP EPPTheorem Amendment Turing
doc-targets := $(addsuffix .html, $(targets))
build-targets := $(addsuffix .vo, $(targets))

all: doc build

$(build-targets):
	$(coqc) $(COQFLAGS) $(basename $@).v

.SECONDEXPANSION:
$(doc-targets): $$(basename $$@).vo
	$(coqdoc) -g $(basename $@).v

# TODO: Use coqdep instead of writing deps manually
Common.vo: Basic.vo
CC.vo: Basic.vo Common.vo
Kleene.vo: Basic.vo
Implementation.vo: Common.vo CC.vo Kleene.vo
SP.vo: Common.vo CC.vo
BranchingOrder.vo: SP.vo
Merge.vo: BranchingOrder.vo
EPP.vo: CC.vo Merge.vo
EPPTheorem.vo: EPP.vo
Amendment.vo: EPP.vo
Turing.vo: Amendment.vo EPPTheorem.vo Implementation.vo

doc: $(doc-targets)

build: $(build-targets)

clean:
	@rm -f $(foreach file,$(targets),$(subst %,$(file),$(CLEANING_LIST))) 3>&1 1>&2 2>&3 3>&- | grep -v "No such file or directory" | 3>&1 1>&2 2>&3 3>&-
