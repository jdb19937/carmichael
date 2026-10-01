#!/usr/bin/env python3
"""Driver for the Metamath campaign.  Run from carmichael/metamath/.

  mm.py unify  WS.mmp      unify a worksheet (mmatch, or mmj2 batch unification);
                           print the unified worksheet (with proof) or the errors
  mm.py add    WS.mmp      unify, then append the theorem to carmichael.mm
                           and verify the whole file with metamath-knife
                           ($e hypotheses are renumbered into the proof;
                           a worksheet near mmj2's limits is warned
                           about before the run, and a death is diagnosed)
  mm.py batch  WS.mmp...   unify several worksheets in one mmatch run (a
                           worksheet may cite the earlier ones of the batch),
                           append them all, verify once, roll back on failure
  mm.py verify             metamath-knife -v carmichael.mm
  mm.py show   LABEL...    statement (with $e hypotheses) via metamath-exe
  mm.py grep   REGEX       search assertions of set.mm + carmichael.mm
                           (one line per $a/$p: label then formula)
  mm.py index              rebuild the assertion index (automatic when stale)
  mm.py html               metamath.org-style pages for our theorems -> scratch/html
  mm.py axioms             fail if any theorem uses a $a outside set.mm's main body
  mm.py defcheck           fail if any $a of ours is not a conservative df- definition
  mm.py new ID             create sorties/ID.mm (includes carmichael.mm) for a sortie
  mm.py merge sorties/ID.mm  append a finished sortie to carmichael.mm and verify

Sorties: set MM_DB=sorties/ID.mm (path relative to carmichael/metamath/) and
every command above works on that file instead of carmichael.mm; the
worksheet directory is MM_WS (default worksheets/).  Run everything from
carmichael/metamath/ so the $[ ... $] includes resolve.  MM_HEAP (default 4g)
and MM_STACK (bytes, default 1 GiB) size the JVM; the stack applies when
tools/java/MMJ2BigStack.class is compiled (see the header of its source).

Engines: tools/mmatch (native, G6: loads the database in half a second and
matches a fully specified worksheet, one whose every step cites its
justification, in about a second per 10,000 steps) and mmj2 (Java, 1.5-3
minutes per run, searches for blank refs, work variables).  MM_ENGINE=auto
(the default) runs mmatch when the worksheet is eligible and falls back to
mmj2 otherwise or on any mmatch failure (the failure is printed first);
MM_ENGINE=mmatch never falls back; MM_ENGINE=mmj2 never tries mmatch.
`--engine=auto|mmatch|mmj2` on the command line overrides the variable.

Worksheet format (mmj2 Proof Worksheet):
  $( <MM> <PROOF_ASST> THEOREM=label  LOC_AFTER=?
  * free-text comment lines become the theorem's $( ... $) description
  h1::label.1        |- hypothesis
  2::ref             |- formula            (ref blank => mmj2 searches)
  qed:2,1:           |- conclusion
  $d x A $.                                (optional; mmj2 also generates)
  $)
"""
import os, re, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
# carmichael/metamath: the nearest ancestor of this file holding carmichael.mm
# (so the driver also runs from a staging copy such as tools/next/)
ROOT = os.path.dirname(HERE)
while not os.path.exists(os.path.join(ROOT, "carmichael.mm")) and os.path.dirname(ROOT) != ROOT:
    ROOT = os.path.dirname(ROOT)
MAINDB = os.path.join(ROOT, "carmichael.mm")
# a sortie works in its own include file: MM_DB=sorties/ID.mm (relative to
# carmichael/metamath/), which starts with $[ carmichael.mm $]; every tool
# still runs from ROOT so the includes resolve
DB = os.path.join(ROOT, os.environ.get("MM_DB", "carmichael.mm"))
DBREL = os.path.relpath(DB, ROOT)
SETMM = os.path.join(ROOT, "set.mm-repo", "set.mm")
INDEX = os.path.join(ROOT, "scratch", "assertions-%s.idx" % os.path.basename(DB).replace(".mm", ""))
WSDIR = os.path.join(ROOT, os.environ.get("MM_WS", "worksheets"))
JAVA = "/opt/homebrew/opt/openjdk/bin/java"
MMJ2 = os.path.expanduser("~/metamath/mmj2/mmj2jar/mmj2.jar")
KNIFE = os.path.expanduser("~/.cargo/bin/metamath-knife")
MMEXE = os.path.expanduser("~/metamath/metamath-exe/src/metamath")
# the big-stack launcher (tools/java/MMJ2BigStack.java): mmj2 recurses on the
# parse tree of every formula and overflows the primordial thread's stack on
# long formulas, which -Xss cannot enlarge; the launcher runs BatchMMJ2 on a
# thread with MM_STACK bytes of stack (default 1 GiB).  Used when compiled.
JAVADIR = os.path.join(HERE, "java")
LAUNCHER = os.path.join(JAVADIR, "MMJ2BigStack.class")
HEAP = os.environ.get("MM_HEAP", "4g")
STACK = int(os.environ.get("MM_STACK", str(1 << 30)))
# the native matcher (tools/mmatch-src, G6-HANDOFF.md): used for a worksheet
# whose every step cites its justification; mmj2 remains the engine for
# searches (blank refs) and work variables, and the fallback
MMATCH = os.path.join(HERE, "mmatch")
DEFAULT_ENGINE = "auto"   # mmatch when eligible, mmj2 otherwise (G6-HANDOFF.md)
ENGINE = os.environ.get("MM_ENGINE", DEFAULT_ENGINE)
# the prover's measured limits (TOOLING-DEBT item 2): it exhausts a 4 GB heap
# at about 4,000 worksheet steps and, without the launcher, overflows its stack
# on a 460-step worksheet carrying 2,000-token formulas
WARN_STEPS = 3000
WARN_TOKENS = 1500

NOISE = re.compile(r"^(I-UT-0015|\s*\[|\*\*\*|\s*$|\s*Arg|Hi!|Visit|http|for support|"
                   r"\s*Command Line|CommandLine|\s*= false|I-PA-0412)")


def worksheet_size(ws):
    """(steps, longest formula in tokens, its step) of a worksheet"""
    steps = 0; longest = 0; where = None
    for line in open(ws):
        if re.match(r"^[A-Za-z0-9!?]+:", line) and not line.startswith("$"):
            steps += 1
            if "|-" in line:
                n = len(line.split("|-", 1)[1].split())
                if n > longest:
                    longest, where = n, line.split(":", 1)[0]
        elif line[:1].isspace() and where is not None:
            pass
    return steps, longest, where


def size_warnings(ws):
    """the pre-run warnings for a worksheet near the prover's limits"""
    steps, longest, where = worksheet_size(ws)
    out = []
    if steps > WARN_STEPS:
        out.append("WARNING: %s has %d steps; mmj2 exhausts its %s heap at about 4,000 "
                   "(the sortie protocol says split the theorem, passing bundles between halves)"
                   % (os.path.basename(ws), steps, HEAP))
    if longest > WARN_TOKENS:
        out.append("WARNING: %s carries a %d-token formula at step %s; mmj2 overflowed its stack on "
                   "2,000-token formulas%s" % (os.path.basename(ws), longest, where,
                   " (the big-stack launcher is in use, %d MiB)" % (STACK >> 20) if os.path.exists(LAUNCHER)
                   else " and the big-stack launcher is NOT compiled (tools/java/MMJ2BigStack.java)"))
    return out


def post_mortem(ws, raw, rc):
    """the lines explaining why mmj2 died, if it did"""
    if "RPN-format Metamath proof generated!" in raw:
        return []
    steps, longest, where = worksheet_size(ws)
    size = "%d steps, longest formula %d tokens" % (steps, longest)
    if "OutOfMemoryError" in raw or "Java heap space" in raw or "GC overhead limit" in raw:
        return ["ERROR mmj2 died: HEAP EXHAUSTED (-Xmx%s; %s).  Split the theorem, or raise MM_HEAP." % (HEAP, size)]
    if "StackOverflowError" in raw:
        return ["ERROR mmj2 died: STACK OVERFLOW (%s; %s).  %s" % (
            "launcher stack %d MiB" % (STACK >> 20) if os.path.exists(LAUNCHER) else "primordial thread stack, launcher not compiled",
            size, "Raise MM_STACK or split the theorem." if os.path.exists(LAUNCHER)
            else "Compile tools/java/MMJ2BigStack.java (see its header) or split the theorem.")]
    if rc != 0 and not any(l.startswith("E-") for l in raw.splitlines()):
        return ["ERROR mmj2 died without a proof and without a diagnostic (exit status %d; %s)" % (rc, size)]
    return []


def mmj2_command(rp):
    if os.path.exists(LAUNCHER):
        return [JAVA, "-Djava.awt.headless=true", "-Xmx" + HEAP, "-Dmmj2.stack=%d" % STACK,
                "-cp", MMJ2 + os.pathsep + JAVADIR, "MMJ2BigStack", rp, "n"]
    return [JAVA, "-Djava.awt.headless=true", "-Xmx" + HEAP, "-jar", MMJ2, rp, "n"]


def run_mmj2(ws):
    """Return (ok, text) where text is mmj2's cleaned output.  Warns before the
    run when the worksheet is near the prover's limits and names the cause
    (heap or stack) after it when mmj2 dies."""
    for wline in size_warnings(ws):
        print(wline, file=sys.stderr)
    rp = os.path.join(ROOT, "scratch", "RunParms-%d.txt" % os.getpid())
    with open(rp, "w") as f:
        f.write("LoadFile,%s\nParse,*\nMacrosEnabled,no\n" % DBREL +
                "ProofAsstUnifySearchExclude,biigb,xxxid,dummylink\n"
                "ProofAsstDjVarsSoftErrors,GenerateReplacements\n"
                "OutputVerbosity,9\n"
                "ProofAsstBatchTest,*,%s,un-unified,NotRandomized,Print,"
                "NoDeriveFormulas,NoCompareDJs,NoUpdateDJs,NoAsciiRetest\n"
                % os.path.abspath(ws))
    p = subprocess.run(mmj2_command(rp), cwd=ROOT, capture_output=True, text=True)
    os.unlink(rp)
    raw = p.stdout + p.stderr
    lines = [l for l in raw.splitlines() if not NOISE.match(l)]
    lines += post_mortem(ws, raw, p.returncode)
    text = "\n".join(lines)
    ok = "RPN-format Metamath proof generated!" in text and \
         not any(l.startswith("E-") for l in lines)
    return ok, text


def mmatch_eligible(ws):
    """mmatch's contract: every step cites its justification (a blank ref is
    a search), no work variables, no `!`/`?` search or derive markers"""
    for line in open(ws):
        if line.startswith("$"):
            continue
        m = re.match(r"^([A-Za-z0-9!?]+):([^:]*):(\S*)", line)
        if not m:
            continue
        name, hyps, ref = m.groups()
        if not ref or "!" in name or "?" in name or "?" in hyps:
            return False
        if re.search(r"&[WCS]\d", line):
            return False
    return True


def run_mmatch(ws):
    """(ok, text, exit status) of tools/mmatch on one worksheet; text is the
    unified worksheet, or the E-MMATCH lines"""
    limit = int(os.environ.get("MM_MMATCH_TIMEOUT", "300"))
    try:
        p = subprocess.run([MMATCH, DBREL, os.path.abspath(ws)], cwd=ROOT, capture_output=True,
                           text=True, timeout=limit)
    except subprocess.TimeoutExpired:
        return False, ("E-MMATCH-TIMEOUT: mmatch ran over %d s on %s (MM_MMATCH_TIMEOUT). The usual "
                       "cause is a step citing fewer hypotheses than its assertion takes, which starts "
                       "mmatch's derivation search; supply every hypothesis." % (limit, os.path.basename(ws))), 124
    text = p.stdout + ("\n" + p.stderr if p.stderr.strip() else "")
    ok = p.returncode == 0 and "RPN-format Metamath proof generated!" in p.stdout
    return ok, text, p.returncode


def run_engine(ws, engine=None):
    """(ok, text) from the selected engine: mmatch when eligible, mmj2 as the
    fallback (after printing mmatch's failure) unless MM_ENGINE=mmatch"""
    engine = engine or ENGINE
    if engine == "mmj2" or not os.path.exists(MMATCH):
        return run_mmj2(ws)
    if engine == "auto" and not mmatch_eligible(ws):
        print("mmatch: %s has a blank ref or work variables; using mmj2" % os.path.basename(ws), file=sys.stderr)
        return run_mmj2(ws)
    ok, text, rc = run_mmatch(ws)
    if ok or engine == "mmatch":
        return ok, text
    print(text.strip(), file=sys.stderr)
    print("mmatch failed (exit %d); falling back to mmj2" % rc, file=sys.stderr)
    return run_mmj2(ws)


def parse_unified(text):
    """Extract label, comment, hyps [(label, formula)], conclusion, $d lines, proof."""
    m = re.search(r"\$\( <MM> <PROOF_ASST> THEOREM=(\S+)(.*?)\n\$\)", text, re.S)
    if not m:
        raise SystemExit("no unified worksheet in mmj2 output")
    label, body = m.group(1), m.group(2)
    # join continuation lines (leading whitespace) to the previous step line
    steps, comment, dvs = [], [], []
    for line in body.split("\n")[1:]:
        if line.startswith("*"):
            comment.append(line[1:].strip()); continue
        if line.startswith("$d"):
            d = line.strip()
            if not d.endswith("$."):
                d += " $."
            dvs.append(d); continue
        if line.startswith("$="):
            steps.append(line); continue
        if line[:1].isspace() and steps:
            steps[-1] += " " + line.strip(); continue
        if line.strip():
            steps.append(line)
    hyps, concl, proof = [], None, None
    for s in steps:
        if s.startswith("$="):
            proof = s[2:].strip()
            if proof.endswith("$."):
                proof = proof[:-2].strip()
            continue
        head, formula = s.split(" ", 1) if " " in s else (s, "")
        formula = " ".join(formula.split())
        parts = head.split(":")
        if parts[0].startswith("h"):
            hyps.append((parts[2], formula))
        elif parts[0] == "qed":
            concl = formula
    return label, " ".join(comment).strip(), hyps, concl, dvs, proof


def wrap(s, indent=4, width=79):
    out, cur = [], " " * indent
    for tok in s.split():
        if len(cur) + 1 + len(tok) > width and cur.strip():
            out.append(cur); cur = " " * indent + tok
        else:
            cur += (" " if cur.strip() else "") + tok
    out.append(cur)
    return "\n".join(out)


def block(label, comment, hyps, concl, dvs, proof):
    lines = []
    scoped = bool(hyps or dvs)
    ind = 4 if scoped else 2
    if scoped:
        lines.append("  ${")
    for d in dvs:
        lines.append(" " * ind + d)
    for h, f in hyps:
        lines.append(wrap("%s $e %s $." % (h, f), ind))
    if comment:   # metamath-exe attaches the comment immediately preceding the $p
        lines.append(wrap("$( " + comment + " $)", ind))
    lines.append(wrap("%s $p %s $=" % (label, concl), ind))
    lines.append(wrap(proof + " $.", ind + 2))
    if scoped:
        lines.append("  $}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- $e hypotheses
# mmj2's batch unifier does not count the logical hypotheses of a theorem it
# has not yet seen among that theorem's mandatory hypotheses: it puts their
# labels in the compressed proof's label list instead, so every reference
# beyond the mandatory $f hypotheses is one index short per $e and both
# verifiers reject the proof.  renumber() decodes the letter string, shifts
# those references and re-encodes (folded in from tools/c0lib.py, whose
# `runh` every sortie with $e hypotheses had to know about).  A theorem the
# database already holds is unified with its $e known, and is not renumbered.
_VARS_F = None


def _typed_vars():
    global _VARS_F
    if _VARS_F is None:
        _VARS_F = set()
        for path in (SETMM, MAINDB) + ((DB,) if DB != MAINDB else ()):
            _VARS_F |= set(re.findall(r"^\s*\S+ \$f (?:wff|setvar|class) (\S+) \$\.", open(path).read(), re.M))
    return _VARS_F


def _dec(s):
    out = []; n = 0
    for c in s:
        if c == "Z":
            out.append("Z")
        elif "U" <= c <= "Y":
            n = n * 5 + (ord(c) - ord("U") + 1)
        elif "A" <= c <= "T":
            out.append(n * 20 + (ord(c) - ord("A") + 1)); n = 0
        else:
            raise ValueError("bad proof character " + c)
    if n:
        raise ValueError("truncated proof")
    return out


def _enc(items):
    out = []
    for it in items:
        if it == "Z":
            out.append("Z"); continue
        last = chr(ord("A") + (it - 1) % 20); n = (it - 1) // 20; pre = ""
        while n > 0:
            d = (n - 1) % 5 + 1; pre = chr(ord("U") + d - 1) + pre; n = (n - d) // 5
        out.append(pre + last)
    return "".join(out)


def renumber(proof, nf, hyplabels):
    """the compressed PROOF with the $e labels HYPLABELS moved out of its label
    list into the mandatory hypotheses (after the NF mandatory $f)"""
    m = re.match(r"\(\s*(.*?)\s*\)\s*(.*)$", proof, re.S)
    labels = m.group(1).split(); letters = "".join(m.group(2).split())
    if not any(l in hyplabels for l in labels):
        return proof          # already counted: nothing to repair
    ne = len(hyplabels)
    keep = [l for l in labels if l not in hyplabels]
    idx = {}
    for j, l in enumerate(labels, 1):
        idx[nf + j] = nf + hyplabels.index(l) + 1 if l in hyplabels else nf + ne + keep.index(l) + 1
    out = []
    for it in _dec(letters):
        if it == "Z" or it <= nf:
            out.append(it)
        elif it <= nf + len(labels):
            out.append(idx[it])
        else:
            out.append(nf + ne + len(keep) + (it - nf - len(labels)))   # saved step
    return "( %s ) %s" % (" ".join(keep), _enc(out))


def repair_hyps(hyps, concl, proof):
    """renumber the proof of a new theorem with $e hypotheses (a no-op when
    there are none, or when mmj2 counted them)"""
    if not hyps:
        return proof
    toks = set(concl.split())
    for _h, f in hyps:
        toks |= set(f.split())
    nf = len(toks & _typed_vars())
    return renumber(proof, nf, [h for h, _f in hyps])


def verify():
    p = subprocess.run([KNIFE, "-v", DBREL], cwd=ROOT, capture_output=True, text=True)
    out = p.stdout + p.stderr
    ok = p.returncode == 0 and "0 diagnostics issued" in out
    if ok:
        # every append path (cmd_add, c0lib.addh, zbvlib.addh, ...) calls this and
        # rolls back on failure, so the mathbox gate lives here
        mb = unreviewed_mathbox(open(DB).read())
        if mb:
            ok = False
            out += ("\nMATHBOX CITATION REFUSED: %s cites %s outside MATHBOX_OK "
                    "(find the main-body route; tools/mm.py grep)\n" % (DBREL, " ".join(mb)))
    return ok, out


_MBOX = None


def unreviewed_mathbox(src):
    """set.mm mathbox labels cited by the proofs in SRC and not in MATHBOX_OK"""
    global _MBOX
    if _MBOX is None:
        _MBOX = mathbox_labels(open(SETMM).read())
    ours = set(re.findall(r"^\s*(\S+) \$[ap]\s", src, re.M))
    return sorted((our_proof_labels(src) & _MBOX) - MATHBOX_OK - ours)


def cmd_unify(ws):
    ok, text = run_engine(ws)
    print(text)
    print("UNIFY", "OK" if ok else "FAILED")
    return ok


def cmd_add(ws):
    ok, text = run_engine(ws)
    if not ok:
        print(text); print("UNIFY FAILED; nothing added"); return False
    label, comment, hyps, concl, dvs, proof = parse_unified(text)
    # refuse a new citation of a set.mm mathbox theorem before anything is
    # written (verify() also refuses it, for every other append path)
    mb = unreviewed_mathbox("x $p |- x $= %s $." % proof)
    if mb:
        print("MATHBOX CITATION REFUSED in %s: %s (find the main-body route; "
              "tools/mm.py grep)" % (label, " ".join(mb)))
        return False
    db = open(DB).read()
    if re.search(r"^\s*%s \$p" % re.escape(label), db, re.M) or \
       (DB != MAINDB and re.search(r"^\s*%s \$p" % re.escape(label), open(MAINDB).read(), re.M)):
        print("label %s already in %s; nothing added" % (label, DBREL)); return False
    proof = repair_hyps(hyps, concl, proof)
    with open(DB, "a") as f:
        f.write("\n" + block(label, comment, hyps, concl, dvs, proof))
    vok, vout = verify()
    print(vout.strip())
    if not vok:
        # roll back
        open(DB, "w").write(db)
        print("VERIFY FAILED; rolled back %s" % DBREL); return False
    print("ADDED %s; %s verifies" % (label, DBREL))
    return True


def cmd_batch(wss):
    """add several worksheets with one mmatch run (one database load); a
    worksheet may cite the theorems of the earlier worksheets of the batch.
    Every worksheet must be mmatch-eligible; the theorems are appended in
    order, the file is verified once, and everything is rolled back on
    failure."""
    bad = [ws for ws in wss if not mmatch_eligible(ws)]
    if bad:
        print("not eligible for mmatch (blank refs or work variables); add them one by one: %s" % " ".join(bad))
        return False
    p = subprocess.run([MMATCH, "--batch", DBREL] + [os.path.abspath(ws) for ws in wss], cwd=ROOT, capture_output=True, text=True)
    blocks = {}
    for m in re.finditer(r"\$\( <MM> <PROOF_ASST> THEOREM=(\S+).*?\n\$\)", p.stdout, re.S):
        blocks[m.group(1)] = m.group(0)
    for line in p.stdout.splitlines():
        if line.startswith("E-") or line.startswith("W-"):
            print(line)
    db = open(DB).read()
    out = []
    for ws in wss:
        label = os.path.basename(ws)[:-4]
        if label not in blocks:
            print("FAIL (no proof)", label); continue
        lab, comment, hyps, concl, dvs, proof = parse_unified(blocks[label])
        if re.search(r"^\s*%s \$p" % re.escape(lab), db, re.M):
            print("SKIP (present)", lab); continue
        mb = unreviewed_mathbox("x $p |- x $= %s $." % proof)
        if mb:
            print("MATHBOX CITATION REFUSED in %s: %s" % (lab, " ".join(mb))); continue
        out.append((lab, block(lab, comment, hyps, concl, dvs, repair_hyps(hyps, concl, proof))))
    if not out:
        print("NOTHING ADDED"); return False
    with open(DB, "a") as f:
        for lab, b in out:
            f.write("\n" + b)
    vok, vout = verify()
    print(vout.strip()[-500:])
    if not vok:
        open(DB, "w").write(db)
        print("VERIFY FAILED; rolled back %s" % DBREL); return False
    for lab, _ in out:
        print("ADDED", lab)
    print("%d theorems added; %s verifies" % (len(out), DBREL))
    return len(out) == len(wss)


SORTIE_HEADER = "$[ carmichael.mm $]\n"

# set.mm theorems outside its main body (in a user mathbox) that our proofs
# cite.  Each is an ordinary theorem whose own $a footprint is main-body, so
# soundness is unaffected; they are listed because mathbox content is owned by
# its contributor and may be renamed or reorganised upstream, which would break
# a proof that cites it by name.  cmd_axioms fails if a citation appears that is
# not listed here, so the list cannot grow unnoticed.
MATHBOX_OK = {
    # Numeral and digit arithmetic emitted by tools/num.py and tools/lin.py.
    # Main-body routes exist for all of these; adding them to num.py removes
    # most of this list at a stroke.
    "1p3e4", "1p4e5", "1p7e8", "2p4e6",
    "3p5e8", "4rp", "6rp", "5ne0", "6ne0",
    # base-2 logarithm: floor characterisation and nonnegativity
    "fllog2", "logbge0b",
    # congruences: Lebesgue integral over a changed domain, indexed product
    "itgeq1d", "ixpeq12dv",
    # mapping lemmas without the distinct-variable conditions of their main-body
    # counterparts, required by df-pool, whose domain abstraction binds the
    # mapping's own variable
    "mpteq1df", "mptexf", "ssrab2f",
    # finite set and product utilities
    "elfz2nn", "fprodsplit1", "hashssle",
}


def our_proof_labels(src):
    """every set.mm label cited in a compressed proof of SRC"""
    used = set()
    for m in re.finditer(r"\$p.*?\$=\s*\(([^)]*)\)", src, re.S):
        used.update(m.group(1).split())
    return used


def mathbox_labels(setmm_src):
    mb = setmm_src.find("Mathboxes for user contributions")
    return set(re.findall(r"^\s*(\S+) \$[ap]\s", setmm_src[mb:], re.M))


def cmd_new(sortie):
    """create sorties/ID.mm including carmichael.mm"""
    path = os.path.join(ROOT, "sorties", sortie + ".mm")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if os.path.exists(path):
        print("%s exists" % path); return False
    with open(path, "w") as f:
        f.write("$( Sortie %s of the Metamath campaign: theorems on top of carmichael.mm,\n   merged into it by tools/mm.py merge after re-verification. $)\n\n" % sortie)
        f.write(SORTIE_HEADER)
    print("created %s; use MM_DB=sorties/%s.mm python3 tools/mm.py add ..." % (os.path.relpath(path, ROOT), sortie))
    return True


def atomic_write(path, text):
    """write TEXT to PATH through a temporary file and a rename"""
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        f.write(text); f.flush(); os.fsync(f.fileno())
    os.replace(tmp, path)


def cmd_merge(sortie_path):
    """append the body of a sortie file (everything after its include of
    carmichael.mm) to carmichael.mm, verify, roll back on failure"""
    src = open(os.path.join(ROOT, sortie_path)).read()
    i = src.find(SORTIE_HEADER)
    if i < 0:
        print("no %s in %s" % (SORTIE_HEADER.strip(), sortie_path)); return False
    body = src[i + len(SORTIE_HEADER):]
    main = open(MAINDB).read()
    new_labels = re.findall(r"^\s*(\S+) \$[ap]\s", body, re.M)
    old_labels = set(re.findall(r"^\s*(\S+) \$[ap]\s", main, re.M))
    clash = [l for l in new_labels if l in old_labels]
    if clash:
        print("label clash with carmichael.mm: %s" % " ".join(clash)); return False
    setmm_labels = set(re.findall(r"^\s*(\S+) \$[apef]\s", open(SETMM).read(), re.M))
    clash2 = [l for l in new_labels if l in setmm_labels]
    if clash2:
        print("label clash with set.mm: %s" % " ".join(clash2))
        print("Metamath labels are global; rename in the sortie file and in the "
              "label list of every proof that cites it.")
        return False
    # a sortie's definitions must pass the conservativity check before they
    # enter the main database (MM_DB=sorties/ID.mm python3 tools/mm.py defcheck)
    if not cmd_defcheck((MAINDB, os.path.join(ROOT, sortie_path))):
        print("MERGE REFUSED: fix the definitions of %s first" % sortie_path); return False
    # atomic writes: a running sortie's add re-verifies through the include
    # and must never see a half-written or truncated carmichael.mm
    atomic_write(MAINDB, main + "\n" + body.rstrip("\n") + "\n")
    p = subprocess.run([KNIFE, "-v", "carmichael.mm"], cwd=ROOT, capture_output=True, text=True)
    out = p.stdout + p.stderr
    if p.returncode != 0 or "0 diagnostics issued" not in out:
        atomic_write(MAINDB, main)
        print(out.strip()); print("VERIFY FAILED; rolled back carmichael.mm"); return False
    print("MERGED %d statements from %s; carmichael.mm verifies (run make verify for mmverify + axioms)" % (len(new_labels), sortie_path))
    return True


def cmd_show(labels):
    args = ['read "%s"' % DBREL] + ["show statement %s" % l for l in labels] + ["exit"]
    p = subprocess.run([MMEXE] + args, cwd=ROOT, capture_output=True, text=True)
    for l in p.stdout.splitlines():
        if not re.match(r"^(MM>|Metamath - |Reading|\d+ bytes|The source has|No errors|if you want|\s*$)", l):
            print(l)


def cmd_html():
    """metamath.org-style Unicode pages for every theorem of ours, in scratch/html."""
    out = os.path.join(ROOT, "scratch", "html")
    os.makedirs(out, exist_ok=True)
    labels = re.findall(r"^\s*([0-9a-z]+) \$p", open(DB).read(), re.M)
    # metamath-exe writes LABEL.html into the cwd, and the $[ include $] must
    # resolve from ROOT, so run there and move the pages afterwards
    args = ['read "%s"' % DBREL, "set width 9999"] + \
           ["show statement %s /alt_html" % l for l in labels] + ["exit"]
    subprocess.run([MMEXE] + args, cwd=ROOT, capture_output=True, text=True)
    n = 0
    for l in labels:
        src = os.path.join(ROOT, l + ".html")
        if os.path.exists(src):
            os.replace(src, os.path.join(out, l + ".html")); n += 1
    print("%d pages in scratch/html" % n)


def cmd_axioms():
    """Fail if any theorem of ours depends on an $a beyond set.mm's main body.
    Allowed: every $a declared before set.mm's mathbox section (ZFC axioms,
    definitions).  Forbidden: ax-*/df-* of the mathboxes (e.g. ax-hgt749,
    ax-exfinfld) and any $a of our own file."""
    src = open(SETMM).read()
    mb = src.find("Mathboxes for user contributions")
    allowed = set(re.findall(r"^\s*(\S+) \$a\s", src[:mb], re.M))
    # our own $a statements: syntax axioms and df- definitions only, never ax-
    ours = re.findall(r"^\s*(\S+) \$a\s", open(MAINDB).read(), re.M)
    if DB != MAINDB:
        ours += re.findall(r"^\s*(\S+) \$a\s", open(DB).read(), re.M)
    bad_ax = [l for l in ours if l.startswith("ax-")]
    if bad_ax:
        print("%s declares axioms: %s" % (DBREL, " ".join(bad_ax))); print("AXIOMS FAILED"); return False
    allowed |= set(ours)
    dbsrc = open(DB).read()
    labels = re.findall(r"^\s*([0-9a-z]+) \$p", dbsrc, re.M)
    # every $p must be enumerable, or its axiom footprint would go unchecked
    all_p = re.findall(r"^\s*(\S+) \$p", dbsrc, re.M)
    skipped = [l for l in all_p if l not in labels]
    if skipped:
        print("labels not enumerable by the footprint check (rename them to "
              "[0-9a-z]+): %s" % " ".join(skipped))
        print("AXIOMS FAILED")
        return False
    # citations of set.mm mathbox theorems, against the reviewed list
    mbox = mathbox_labels(src)
    cited = sorted((our_proof_labels(dbsrc) & mbox) - set(ours))
    if DB != MAINDB:
        cited = sorted(set(cited) | ((our_proof_labels(open(MAINDB).read()) & mbox) - set(ours)))
    unlisted = [l for l in cited if l not in MATHBOX_OK]
    if unlisted:
        print("NEW citation of a set.mm mathbox theorem: %s" % " ".join(unlisted))
        print("Each is sound if the $a check passes, but mathbox content is not "
              "stable upstream.  Replace it with a main-body route, or add it to "
              "MATHBOX_OK in tools/mm.py with the reason.")
        print("AXIOMS FAILED")
        return False
    args = ['read "%s"' % DBREL, "set width 9999"] + \
           ["show trace_back %s /axioms" % l for l in labels] + ["exit"]
    p = subprocess.run([MMEXE] + args, cwd=ROOT, capture_output=True, text=True)
    bad, cur = {}, None
    for line in p.stdout.splitlines():
        m = re.match(r'Statement "(\S+)" assumes the following axioms', line)
        if m:
            cur = m.group(1); continue
        if cur and line.startswith("  "):
            for a in line.split():
                if a not in allowed:
                    bad.setdefault(cur, set()).add(a)
    if bad:
        for l in bad:
            print("%s uses non-main-body $a: %s" % (l, " ".join(sorted(bad[l]))))
        print("AXIOMS FAILED"); return False
    print("AXIOMS OK: %d theorems; $a footprint = set.mm main body + %d own "
          "definitions/syntax (no ax-); %d reviewed mathbox theorem citations"
          % (len(labels), len(ours), len(cited)))
    return True


def build_index():
    lines = []
    for path in ((SETMM, MAINDB, DB) if DB != MAINDB else (SETMM, DB)):
        with open(path) as f:
            src = f.read()
        for m in re.finditer(r"^\s*(\S+) \$([ap]) (.*?) \$[=.]", src, re.M | re.S):
            lines.append("%s %s %s" % (m.group(1), m.group(2), " ".join(m.group(3).split())))
    with open(INDEX, "w") as f:
        f.write("\n".join(lines) + "\n")


def cmd_grep(pat):
    if not os.path.exists(INDEX) or os.path.getmtime(INDEX) < max(os.path.getmtime(SETMM), os.path.getmtime(DB), os.path.getmtime(MAINDB)):
        build_index()
    rx = re.compile(pat)
    n = 0
    with open(INDEX) as f:
        for l in f:
            if rx.search(l):
                print(l.rstrip()); n += 1
                if n >= 200:
                    print("... (200 shown)"); break


# ---------------------------------------------------------------- defcheck
# set.mm binders: token patterns in which the FIRST set variable after the
# marker is bound over the rest of the enclosing group.  `S. A B _d x` binds
# x at the END of its group, so the whole group is scanned.
BINDER_PREFIX = ("A.", "E.", "E!", "E*", "F/", "F/_", "U_", "|^|_", "sum_", "prod_",
                 "X_", "Disj_", "iota", "iota_", "iota_")
_VARS = {}


def _load_vars():
    """the typed variables of set.mm (and of our files), from their $f statements"""
    if _VARS:
        return
    paths = [SETMM, MAINDB] + ([DB] if DB != MAINDB else [])
    for path in paths:
        for m in re.finditer(r"^\s*\S+ \$f (setvar|class|wff) (\S+) \$\.", open(path).read(), re.M):
            _VARS[m.group(2)] = m.group(1)


def _is_var(t):
    return t in _VARS


def _is_setvar(t):
    return _VARS.get(t) == "setvar"


def _binds_in_group(toks, s, e, x):
    """does the group toks[s:e] (s = its '(' or '{', e = matching close) bind x
    at its own top level?"""
    depth = 0
    for i in range(s + 1, e):
        t = toks[i]
        if t in "({":
            depth += 1
        elif t in ")}":
            depth -= 1
        if depth != 0:
            continue
        if t in BINDER_PREFIX and i + 1 < e and toks[i + 1] == x:
            return True
        if t == "_d" and i + 1 < e and toks[i + 1] == x:          # S. A B _d x
            return True
        if t == "/" and i + 1 < e and toks[i + 1] == x and i + 2 < e and toks[i + 2] in ("]", "]_"):
            return True                                            # [ A / x ] ph, [_ A / x ]_ B
        if t == "|->" or t == "|":
            # ( x e. A |-> B ), ( x e. A , y e. B |-> C ), { x | ph }, { x e. A | ph },
            # { <. x , y >. | ph }: every set variable before the marker at top level
            for j in range(s + 1, i):
                if toks[j] == x:
                    return True
    return False


def _bound_occurrences_ok(toks, x):
    """every occurrence of set variable x is inside a group that binds it"""
    # matching brackets
    stack, match = [], {}
    for i, t in enumerate(toks):
        if t in "({":
            stack.append(i)
        elif t in ")}":
            if not stack:
                return False
            j = stack.pop(); match[j] = i; match[i] = j
    if stack:
        return False
    for i, t in enumerate(toks):
        if t != x:
            continue
        # walk outward through enclosing groups
        ok = False
        depth = 0
        for j in range(i - 1, -1, -1):
            if toks[j] in ")}":
                depth += 1
            elif toks[j] in "({":
                if depth == 0:
                    if _binds_in_group(toks, j, match[j], x):
                        ok = True; break
                else:
                    depth -= 1
        if not ok:
            return False
    return True


def cmd_defcheck(paths=None):
    """Check every $a of ours is a conservative definition in set.mm's sense:
    a syntax axiom introducing one new constant applied to distinct
    variables, followed by exactly one |- axiom `df-` of the form
    `|- NEW = RHS` (class) or `|- ( NEW <-> RHS )` (wff) whose left side is
    the syntax pattern, whose right side does not mention the constant, and
    whose extra variables are set variables, all bound (by the binders of
    set.mm) and all $d-distinct from every other variable of the statement.
    The binder scan is syntactic and can only fail safe: an unrecognised
    binding form reports FAIL and is read by hand."""
    _load_vars()
    if paths is None:
        paths = (MAINDB, DB) if DB != MAINDB else (MAINDB,)
    problems, ndf = [], 0
    for path in paths:
        text = open(path).read()
        # statements in order, with their enclosing $d lines
        stmts = []
        for m in re.finditer(r"^\s*(\S+) \$a (.*?) \$\.", text, re.M | re.S):
            stmts.append((m.group(1), m.group(2).split(), m.start()))
        syn = {}      # constant -> (label, pattern tokens)
        for lab, toks, _ in stmts:
            if toks[0] in ("class", "wff", "setvar"):
                consts = [t for t in toks[1:] if t not in "(){}" and not _is_var(t)]
                if toks[0] == "setvar" or len(consts) != 1:
                    problems.append("%s: syntax axiom must introduce exactly one constant: %s" % (lab, " ".join(toks)))
                    continue
                if consts[0] in syn:
                    problems.append("%s: constant %s already has syntax axiom %s" % (lab, consts[0], syn[consts[0]][0]))
                vs = [t for t in toks[1:] if _is_var(t)]
                if len(vs) != len(set(vs)):
                    problems.append("%s: repeated variable in syntax pattern" % lab)
                syn[consts[0]] = (lab, toks[1:], set())
        defined = {}
        for lab, toks, pos in stmts:
            if toks[0] != "|-":
                continue
            ndf += 1
            body = toks[1:]
            if not lab.startswith("df-"):
                problems.append("%s: a |- axiom whose label is not df-" % lab)
            # split at the top-level = or <->
            if body[0] == "(" and body[-1] == ")":
                inner = body[1:-1]; depth = 0; split = None
                for i, t in enumerate(inner):
                    if t in "({": depth += 1
                    elif t in ")}": depth -= 1
                    elif depth == 0 and t in ("=", "<->"):
                        split = i; break
                if split is not None and inner[split] == "<->":
                    lhs, rhs, kind = inner[:split], inner[split + 1:], "wff"
                else:
                    lhs = rhs = None
            else:
                lhs = rhs = None
            if lhs is None:
                depth = 0; split = None
                for i, t in enumerate(body):
                    if t in "({": depth += 1
                    elif t in ")}": depth -= 1
                    elif depth == 0 and t == "=":
                        split = i; break
                if split is None:
                    problems.append("%s: not of the form |- NEW = RHS or |- ( NEW <-> RHS )" % lab)
                    continue
                lhs, rhs, kind = body[:split], body[split + 1:], "class"
            lconst = [t for t in lhs if t in syn]
            if len(set(lconst)) != 1 or len(lconst) != 1:
                problems.append("%s: left side must be one syntax pattern, got: %s" % (lab, " ".join(lhs)))
                continue
            c = lconst[0]
            slab, pat, _ = syn[c]
            if c in defined:
                problems.append("%s: constant %s already defined by %s" % (lab, c, defined[c]))
            defined[c] = lab
            # LHS must be the syntax pattern up to a consistent renaming of variables
            if len(pat) != len(lhs):
                problems.append("%s: left side %s is not the syntax pattern %s" % (lab, " ".join(lhs), " ".join(pat)))
                continue
            ren = {}
            for a, b in zip(pat, lhs):
                if _is_var(a):
                    if not _is_var(b) or ren.setdefault(a, b) != b or _VARS[a] != _VARS[b]:
                        problems.append("%s: left side %s is not the syntax pattern %s" % (lab, " ".join(lhs), " ".join(pat)))
                        break
                elif a != b:
                    problems.append("%s: left side %s is not the syntax pattern %s" % (lab, " ".join(lhs), " ".join(pat)))
                    break
            if c in rhs:
                problems.append("%s: %s occurs on the right side" % (lab, c))
            lvars = [t for t in lhs if _is_var(t)]
            if len(lvars) != len(set(lvars)):
                problems.append("%s: repeated variable on the left side" % lab)
            dummies = sorted(set(t for t in rhs if _is_var(t)) - set(lvars))
            bad = [d for d in dummies if not _is_setvar(d)]
            if bad:
                problems.append("%s: class/wff variable %s free on the right side" % (lab, " ".join(bad)))
            # $d lines of the enclosing ${ ... $} block
            bstart = text.rfind("${", 0, pos)
            bend = text.find("$}", pos)
            blk = text[bstart:bend] if bstart >= 0 and (bend < 0 or bend > pos) else ""
            dpairs = set()
            for dl in re.findall(r"\$d (.*?) \$\.", blk):
                vs = dl.split()
                for i in range(len(vs)):
                    for j in range(len(vs)):
                        if i != j:
                            dpairs.add((vs[i], vs[j]))
            allvars = sorted(set(t for t in lhs + rhs if _is_var(t)))
            for d in dummies:
                if not _is_setvar(d):
                    continue
                if not _bound_occurrences_ok(rhs, d):
                    problems.append("%s: dummy %s has a free (or unrecognised-binder) occurrence on the right side" % (lab, d))
                for v in allvars:
                    if v != d and (d, v) not in dpairs:
                        problems.append("%s: dummy %s lacks $d against %s" % (lab, d, v))
        undefined = [c for c in syn if c not in defined]
        if undefined:
            problems.append("%s: syntax constants with no df-: %s" % (os.path.relpath(path, ROOT), " ".join(undefined)))
    if problems:
        for p in problems:
            print(p)
        print("DEFCHECK FAILED (%d problems)" % len(problems)); return False
    print("DEFCHECK OK: %d definitions, each one syntax axiom + one df- of the form NEW = RHS / ( NEW <-> RHS ), "
          "NEW absent from RHS, every dummy a bound set variable with full $d" % ndf)
    return True


if __name__ == "__main__":
    a = sys.argv[1:]
    for opt in [x for x in a if x.startswith("--engine=")]:
        ENGINE = opt.split("=", 1)[1]
        a.remove(opt)
    if ENGINE not in ("auto", "mmatch", "mmj2"):
        print("MM_ENGINE / --engine must be auto, mmatch or mmj2"); sys.exit(2)
    if not a:
        print(__doc__); sys.exit(2)
    if a[0] == "batch":
        sys.exit(0 if cmd_batch(a[1:]) else 1)
    if a[0] == "unify":
        sys.exit(0 if cmd_unify(a[1]) else 1)
    if a[0] == "add":
        sys.exit(0 if cmd_add(a[1]) else 1)
    if a[0] == "new":
        sys.exit(0 if cmd_new(a[1]) else 1)
    if a[0] == "merge":
        sys.exit(0 if cmd_merge(a[1]) else 1)
    if a[0] == "verify":
        ok, out = verify(); print(out.strip()); print("VERIFY", "OK" if ok else "FAILED"); sys.exit(0 if ok else 1)
    if a[0] == "show":
        cmd_show(a[1:])
    elif a[0] == "grep":
        cmd_grep(" ".join(a[1:]))
    elif a[0] == "index":
        build_index()
    elif a[0] == "html":
        cmd_html()
    elif a[0] == "axioms":
        sys.exit(0 if cmd_axioms() else 1)
    elif a[0] == "defcheck":
        sys.exit(0 if cmd_defcheck() else 1)
    else:
        print(__doc__); sys.exit(2)
