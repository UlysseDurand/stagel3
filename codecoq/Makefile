EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://www.chargueraud.org/softs/tlc/' TLC \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject
VS:=$(wildcard *.v)
VS_IN_PROJ:=$(shell grep .v $(COQ_PROJ))

ifeq (,$(VS_IN_PROJ))
VS_OTHER := $(VS)
else
VS := $(VS_IN_PROJ)
endif

all: html

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)
	find . -name "*.aux" -type f -delete

html: $(COQMAKEFILE) $(VS)
	rm -fr html
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html



$(COQMAKEFILE): $(COQ_PROJ) $(VS)
		coq_makefile -f $(COQ_PROJ) $(VS_OTHER) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ) $(VS): ;

.PHONY: clean all force
