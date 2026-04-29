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

# New target for push-button evaluation of LOC
STAT_TMP := .stat_tmp

statistics:
	@echo "===== Checking for Admitted proofs ====="
	@find . -name "*.v" | xargs grep "Admitted" || echo "No Admitted found."
	@echo ""

	@echo "===== Basic Data Types ====="
	@cd src && coqwc Lib*.v | tee ../$(STAT_TMP)_basic.txt
	@echo ""

	@echo "===== Definition of Labelled Transition Systems ====="
	@cd src && coqwc LTS.v SyncLTS.v | tee ../$(STAT_TMP)_lts.txt
	@echo ""

	@echo "===== Trace Refinement, Simulation and Verified Concurrent Object ====="
	@cd src && coqwc BSim.v ComposedRefinement.v ImplRefinement.v Invariants.v Refinement.v VerifiedConcurrentObject.v ComposedLTS.v | tee ../$(STAT_TMP)_refine.txt
	@echo ""

	@echo "===== Compositionality ====="
	@cd src && coqwc RawTensor.v RawCompose.v HE.v VE.v SyncCompLTS.v Tensor.v ImplTensor.v HComp.v Compose.v Link.v ImplRawCompose.v Linking.v Weaken.v VComp.v | tee ../$(STAT_TMP)_comp.txt
	@echo ""

	@echo "===== Register-Counter-Timer example ====="
	@cd src && coqwc Register*.v Counter*.v Timer.v TickNat.v | tee ../$(STAT_TMP)_rct.txt
	@echo ""

	@echo "===== Bounded queue example - Total ====="
	@cd src && coqwc A*.v Q*.v KInduction.v Identity.v VeriTactics.v | tee ../$(STAT_TMP)_bq_total.txt
	@echo ""

	@echo "===== Bounded queue: Basic definitions and skeleton of simulation proofs ====="
	@cd src && coqwc AQC.v Array.v ArrayProp.v ArrayQueue.v ArrayQueueImpl.v ArrayQueueImplProp*.v ArrayQueueMapping.v ArrayQueueProp.v Queue.v KInduction.v VeriTactics.v
	@echo ""

	@echo "===== Bounded queue: Verified concurrent layers ====="
	@cd src && coqwc ArrayCorrectness.v ArraySC.v ArrayQueueImplSC.v ArrayQueueReduceSC.v ArrayToQueue.v QC.v QueueProp.v
	@echo ""

	@echo "===== Bounded queue: Proof of invariants ====="
	@cd src && coqwc ArrayQueueInvariant*.v Identity.v
	@echo ""

	@echo "===== Summary (automatically computed from coqwc) ====="

	@basic=$$(awk 'END {print $$1+$$2}' $(STAT_TMP)_basic.txt); \
	lts=$$(awk 'END {print $$1+$$2}' $(STAT_TMP)_lts.txt); \
	refine=$$(awk 'END {print $$1+$$2}' $(STAT_TMP)_refine.txt); \
	comp=$$(awk 'END {print $$1+$$2}' $(STAT_TMP)_comp.txt); \
	rct=$$(awk 'END {print $$1+$$2}' $(STAT_TMP)_rct.txt); \
	bq=$$(awk 'END {print $$1+$$2}' $(STAT_TMP)_bq_total.txt); \
	total_framework=$$((basic + lts + refine + comp)); \
	echo "Basic Data Types:            $$basic lines"; \
	echo "LTS definitions:             $$lts lines"; \
	echo "Refinement & Simulation:     $$refine lines"; \
	echo "Compositionality:            $$comp lines"; \
	echo "Total framework:             $$total_framework lines"; \
	echo "Register-Counter-Timer:      $$rct lines"; \
	echo "Bounded queue (total):       $$bq lines"; \
	echo ""

	@rm -f $(STAT_TMP)_*.txt