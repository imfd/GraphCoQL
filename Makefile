
## Documentation related ##
DOC_DIR:=./doc
DOC_ASSETS_DIR:=$(DOC_DIR)/assets
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(DOC_ASSETS_DIR)/header.html --with-footer $(DOC_ASSETS_DIR)/footer.html
export COQDOCFLAGS

DOC_OUT_MSG:="Generated documentation can be found in $(DOC_DIR)/html"

COQMAKEFILE:=CoqMakeFile
COQ_PROJ:=_CoqProject


SRC_DIR:=src
PROOFS_DIR:=src/theory

VS:=$(wildcard src/*.v)
PROOFS:=$(wildcard src/theory/*.v)

AT=



all: all_coq html


all_coq : $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) all


$(COQMAKEFILE): $(COQ_PROJ) $(VS) $(PROOFS) Makefile
		${AT}coq_makefile -f $(COQ_PROJ) -o $@




html: $(COQMAKEFILE) $(VS) $(PROOFS)
	rm -fr $(DOC_DIR)/html
	make -f $(COQMAKEFILE) $@
	@mv ./html $(DOC_DIR)/
	@cp $(DOC_ASSETS_DIR)/resources/* $(DOC_DIR)/html
	@echo $(DOC_OUT_MSG)

.PHONY : clean all



clean: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $@
	$(RM) -f $(COQMAKEFILE)
