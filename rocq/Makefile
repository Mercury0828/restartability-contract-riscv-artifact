# RESTART-V Rocq (M4). Toolchain: Coq 8.15 (WSL). CPU-only.
COQMK := CoqMakefile
all: $(COQMK)
	$(MAKE) -f $(COQMK)
$(COQMK): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMK)
clean:
	-$(MAKE) -f $(COQMK) clean 2>/dev/null || true
	rm -f $(COQMK) $(COQMK).conf *.vo *.vok *.vos *.glob .*.aux
.PHONY: all clean
