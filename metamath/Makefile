.PHONY: verify verify2 clean html add index merge

KNIFE    ?= $(HOME)/.cargo/bin/metamath-knife
MMVERIFY ?= $(HOME)/metamath/mmverify.py
MMEXE    ?= $(HOME)/metamath/metamath-exe/src/metamath
DB       := carmichael.mm

# machine-verify every proof in carmichael.mm (which includes set.mm) with
# two independent checkers: metamath-knife (Rust) and mmverify.py (Python),
# then check that no mathbox axiom ($a) entered the dependency tree, and that
# every $a of ours is a conservative definition (one syntax axiom, one df-,
# dummies bound and $d-distinct), and that carmtm is the frozen statement
# (scratch/carmtm.mmp) with no hypotheses
verify:
	$(KNIFE) -v $(DB) | tee scratch/knife.log
	@grep -q '^0 diagnostics issued' scratch/knife.log
	python3 $(MMVERIFY) $(DB) --logfile scratch/mmverify.log
	python3 tools/mm.py axioms
	python3 tools/mm.py defcheck
	python3 tools/gen/f2_freeze.py
	MM_DB=$(DB) python3 tools/gen/t15_freeze.py check
	@echo "VERIFIED: $(DB) passes metamath-knife and mmverify.py; axiom footprint is set.mm's main body; every df- is a conservative definition"

# knife only (sub-second); used after every add
verify2:
	python3 tools/mm.py verify

# unify one worksheet and append it: make add WS=worksheets/LABEL.mmp
add:
	python3 tools/mm.py add $(WS)

# append a finished sortie: make merge S=sorties/ID.mm (then make verify)
merge:
	python3 tools/mm.py merge $(S)

# assertion index for tools/mm.py grep
index:
	python3 tools/mm.py index

# metamath.org-style pages (Unicode) for every theorem of ours, in scratch/html
html:
	python3 tools/mm.py html

clean:
	rm -rf scratch/html scratch/*.html scratch/*.log scratch/*.out scratch/RunParms-*.txt scratch/assertions.idx
