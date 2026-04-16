COQMKFILENAME=CoqSrc.mk

LIBNAME=VCO

.PHONY: all clean coq 

all: coq

%.mk : Makefile _%
	coq_makefile -f _$* -o $*.mk

$(COQMKFILENAME): Makefile
	{ echo "-R src $(LIBNAME) " ; find src -name "*.v" ; } > _CoqProject && coq_makefile -f _CoqProject -o $(COQMKFILENAME)

coq: $(COQMKFILENAME)
	@$(MAKE) -f $(COQMKFILENAME)

clean:
	@if [ -f $(COQMKFILENAME) ]; then \
		$(MAKE) -f $(COQMKFILENAME) clean; \
	fi
	rm -f $(COQMKFILENAME)
	rm -f "$(COQMKFILENAME).conf"
	rm -rf _CoqProject

	find . -name "*.aux" -delete
	find . -name ".lia.cache" -delete
	find . -name ".nia.cache" -delete
	find . -name "*.vo" -delete
	find . -name "*.glob" -delete
	find . -name "*.v.d" -delete
	find . -name "*.vok" -delete
	find . -name "*.vos" -delete