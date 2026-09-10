.PHONY: all clean verify

all: carmichael.pdf

# machine-verify the main theorem: full Lean build (kernel-checks every
# proof), then AxiomCheck.lean asserts in-Lean (via #guard_msgs) that each
# audited declaration depends only on the three standard axioms — a sorry
# or native_decide would change the axiom list and fail elaboration
verify:
	cd lean && lake build
	cd lean && lake env lean AxiomCheck.lean
	@echo "VERIFIED: build green; audited declarations depend only on propext, Classical.choice, Quot.sound"

# two passes so cross-references and hyperlinks resolve
%.pdf: %.tex
	pdflatex -interaction=nonstopmode $<
	pdflatex -interaction=nonstopmode $<

clean:
	rm -f *.aux *.log *.out *.toc
