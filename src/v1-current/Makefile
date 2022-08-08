SHELL=/bin/bash

COQFLAGS?=

EXEs := coqc coqdoc
_ := $(foreach exe,$(EXEs),\
        $(if $(shell which $(exe)),\
            $(eval $(exe) := $(exe)),\
            $(if $(shell which $(exe).exe),\
              $(eval $(exe) := $(exe).exe),\
              $(error "No $(exe) or $(exe).exe in PATH"))))

CLEANING_LIST := %.aux %.glob %.o %.vo 

targets := Basic Common CC SP BranchingOrder Merge EPP Amendment Kleene Implementation

.PHONY: all clean targets

all: $(targets)

$(targets):
	$(coqc) $@

clean:
	@rm -f $(foreach file,$(targets),$(subst %,$(file),$(CLEANING_LIST))) 3>&1 1>&2 2>&3 3>&- | grep -v "No such file or directory" | 3>&1 1>&2 2>&3 3>&-
