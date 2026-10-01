//! mmatch: a proof matcher for fully specified mmj2 proof worksheets.
//!
//!   mmatch [--batch] [--check] [--time] DB WORKSHEET.mmp...
//!
//! Every step of the worksheet must cite its justifying assertion (a blank
//! ref is refused: that is a search, mmj2's job).  A step may omit its formula
//! (an "instance step", `i3::dsqfv`); it is derived from the step that cites
//! it.  The output is the unified worksheet in mmj2's Print format: the step
//! lines with their hypotheses, the `$d` lines mmj2 would generate, the
//! compressed proof after `$=`, and the line
//! `I-PA-0119 Theorem LABEL: RPN-format Metamath proof generated!` on success.
//! Failures print `E-MMATCH ...` lines and set the exit status: 1 for a proof
//! error, 2 for a worksheet mmatch does not handle (blank refs, work
//! variables), 3 for a database or usage problem.
//!
//! With several worksheets (or --batch) the database is loaded once; a
//! worksheet that succeeds becomes citable by the later ones of the batch.

use metamath_rs::database::DbOptions;
use metamath_rs::formula::{Formula, LabelIter};
use metamath_rs::grammar::{Grammar, StmtParse};
use metamath_rs::nameck::{Atom, Nameset};
use metamath_rs::scopeck::{Hyp, ScopeResult};
use metamath_rs::statement::{StatementAddress, SymbolType};
use metamath_rs::{as_str, Database};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::Arc;
use std::time::Instant;

// ------------------------------------------------------------------ atoms

/// knife's `Atom` keeps its u32 private; its derived `Hash` writes exactly
/// that u32, which this hasher records.
struct Grab(u32);
impl Hasher for Grab {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _: &[u8]) {}
    fn write_u32(&mut self, v: u32) {
        self.0 = v
    }
}
fn aid(a: Atom) -> u32 {
    let mut g = Grab(0);
    a.hash(&mut g);
    g.0
}

// ------------------------------------------------------------------ terms

type Id = u32;
const NONE: u32 = u32::MAX;
const F_META: u8 = 1;
const F_HASMETA: u8 = 2;
const F_VAR: u8 = 4;

#[derive(Clone, Copy)]
struct Node {
    /// atom id of the syntax label ($a or $f), or the meta id when F_META
    label: u32,
    ks: u32,
    nk: u32,
    flags: u8,
}

fn sm(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

#[derive(Default)]
struct Arena {
    nodes: Vec<Node>,
    pool: Vec<Id>,
    map: HashMap<u64, Id>,
}

impl Arena {
    fn kids(&self, t: Id) -> &[Id] {
        let n = &self.nodes[t as usize];
        &self.pool[n.ks as usize..(n.ks + n.nk) as usize]
    }
    #[inline]
    fn node(&self, t: Id) -> Node {
        self.nodes[t as usize]
    }
    #[inline]
    fn has_meta(&self, t: Id) -> bool {
        self.nodes[t as usize].flags & (F_META | F_HASMETA) != 0
    }
    #[inline]
    fn is_var(&self, t: Id) -> bool {
        self.nodes[t as usize].flags & F_VAR != 0
    }
    fn same(&self, t: Id, label: u32, kids: &[Id], flags: u8) -> bool {
        let n = self.nodes[t as usize];
        n.label == label && n.flags == flags && n.nk as usize == kids.len() && self.kids(t) == kids
    }
    fn intern(&mut self, label: u32, kids: &[Id], mut flags: u8) -> Id {
        if flags & F_META == 0 {
            for &k in kids {
                if self.nodes[k as usize].flags & (F_META | F_HASMETA) != 0 {
                    flags |= F_HASMETA;
                    break;
                }
            }
        }
        let mut h = sm(label as u64 ^ ((flags as u64) << 40) ^ ((kids.len() as u64) << 48));
        for (i, &k) in kids.iter().enumerate() {
            h = sm(h ^ (k as u64) ^ ((i as u64) << 32));
        }
        loop {
            match self.map.get(&h) {
                Some(&id) if self.same(id, label, kids, flags) => return id,
                Some(_) => h = sm(h ^ 0x5151_5151),
                None => break,
            }
        }
        let id = self.nodes.len() as Id;
        let ks = self.pool.len() as u32;
        self.pool.extend_from_slice(kids);
        self.nodes.push(Node { label, ks, nk: kids.len() as u32, flags });
        self.map.insert(h, id);
        id
    }
    fn meta(&mut self, m: u32) -> Id {
        self.intern(m, &[], F_META)
    }
}

// ------------------------------------------------------------------ assertions

enum HypRef {
    F(u32),
    E(u32),
}

struct Assertion {
    name: String,
    addr: Option<StatementAddress>,
    nvars: usize,
    /// variable symbol names, indexed like the metas 0..nvars
    var_names: Vec<String>,
    /// their typecodes (`wff`, `class`, `setvar`), same indexing
    var_tcs: Vec<String>,
    concl: Id,
    ehyps: Vec<Id>,
    hyp_order: Vec<HypRef>,
    dv: Vec<(u32, u32)>,
    provable: bool,
}

enum Tok {
    C(String),
    K(u8),
}

struct SynInfo {
    name: String,
    arity: usize,
    /// appearance index (knife child order) -> $f order position
    perm: Vec<u8>,
    tmpl: Vec<Tok>,
}

struct VarInfo {
    flabel: String,
    sym: String,
    tc: String,
    faddr: StatementAddress,
}

#[derive(Default)]
struct Names {
    map: HashMap<String, u32>,
    list: Vec<String>,
}
impl Names {
    fn get(&mut self, s: &str) -> u32 {
        if let Some(&i) = self.map.get(s) {
            return i;
        }
        let i = self.list.len() as u32;
        self.list.push(s.to_string());
        self.map.insert(s.to_string(), i);
        i
    }
}

// ------------------------------------------------------------------ worksheet

struct Step {
    name: String,
    hyps: Vec<String>,
    refl: String,
    /// tokens after `|-`
    formula: Option<Vec<String>>,
    is_hyp: bool,
}

impl Step {
    /// the name a step is cited by: a hypothesis step `hN` is cited as `N`
    fn refname(&self) -> &str {
        if self.is_hyp {
            &self.name[1..]
        } else {
            &self.name
        }
    }
}

enum Line {
    Raw(String),
    Dv(Vec<String>),
    Step(usize),
}

struct Ws {
    label: String,
    header: String,
    lines: Vec<Line>,
    steps: Vec<Step>,
    /// the largest number in a step name (mmj2 numbers derived steps after it)
    greatest: u32,
}

/// a step mmj2's Derive feature would add: a missing hypothesis of `before`
/// whose formula no earlier step carries, justified by a search among the
/// hypothesis-free assertions
struct Derived {
    name: String,
    refl: String,
}

/// Err((code, message)): 2 = not handled by mmatch (mmj2's business), 1 = malformed
fn parse_ws(text: &str) -> Result<Ws, (i32, String)> {
    // logical lines: a line starting with whitespace continues the previous one
    let mut logical: Vec<String> = vec![];
    for raw in text.split('\n') {
        let line = raw.strip_suffix('\r').unwrap_or(raw);
        if line.trim().is_empty() {
            continue;
        }
        if line.as_bytes()[0].is_ascii_whitespace() && !logical.is_empty() {
            let last = logical.last_mut().unwrap();
            last.push(' ');
            last.push_str(line.trim());
        } else {
            logical.push(line.to_string());
        }
    }
    let mut ws = Ws { label: String::new(), header: String::new(), lines: vec![], steps: vec![], greatest: 0 };
    let mut seen: HashSet<String> = HashSet::new();
    for line in logical {
        if line.starts_with("$( <MM>") {
            let l = line.split("THEOREM=").nth(1).ok_or((1, "header without THEOREM=".to_string()))?;
            ws.label = l.split_whitespace().next().unwrap_or("").to_string();
            ws.header = line.trim_end().to_string();
            continue;
        }
        let t = line.trim_end();
        if t == "$)" {
            break;
        }
        if t.starts_with('*') || t.starts_with("$(") {
            ws.lines.push(Line::Raw(t.to_string()));
            continue;
        }
        if t.starts_with("$d") {
            let toks: Vec<String> = t.split_whitespace().skip(1).take_while(|x| *x != "$.").map(String::from).collect();
            ws.lines.push(Line::Dv(toks));
            continue;
        }
        if t.starts_with("$=") {
            continue; // a previous proof: regenerated
        }
        let mut it = t.split_whitespace();
        let head = it.next().unwrap();
        let parts: Vec<&str> = head.split(':').collect();
        if parts.len() != 3 || parts[0].is_empty() {
            ws.lines.push(Line::Raw(t.to_string()));
            continue;
        }
        let name = parts[0].to_string();
        if name.contains('!') || name.contains('?') {
            return Err((2, format!("step {} asks mmj2 to search or derive", name)));
        }
        let hyps: Vec<String> = if parts[1].is_empty() { vec![] } else { parts[1].split(',').map(String::from).collect() };
        if hyps.iter().any(|h| h.is_empty() || h == "?") {
            return Err((2, format!("step {} has an unspecified hypothesis", name)));
        }
        let refl = parts[2].to_string();
        let is_hyp = name.starts_with('h');
        let rest: Vec<String> = it.map(String::from).collect();
        let formula = if rest.is_empty() {
            None
        } else {
            if rest[0] != "|-" {
                return Err((1, format!("step {}: formula does not start with |-", name)));
            }
            if rest.iter().any(|x| x.starts_with("&W") || x.starts_with("&C") || x.starts_with("&S")) {
                return Err((2, format!("step {} uses work variables", name)));
            }
            Some(rest[1..].to_vec())
        };
        if refl.is_empty() {
            return Err((2, format!("step {} has a blank ref", name)));
        }
        if is_hyp {
            if formula.is_none() {
                return Err((1, format!("hypothesis step {} has no formula", name)));
            }
            if !hyps.is_empty() {
                return Err((1, format!("hypothesis step {} has hypotheses", name)));
            }
        }
        if !seen.insert(name.clone()) {
            return Err((1, format!("duplicate step name {}", name)));
        }
        if let Ok(k) = name.trim_start_matches(|c: char| c.is_ascii_alphabetic()).parse::<u32>() {
            ws.greatest = ws.greatest.max(k);
        }
        ws.lines.push(Line::Step(ws.steps.len()));
        ws.steps.push(Step { name, hyps, refl, formula, is_hyp });
    }
    if ws.label.is_empty() {
        return Err((1, "no $( <MM> <PROOF_ASST> THEOREM=... header".to_string()));
    }
    Ok(ws)
}

// ------------------------------------------------------------------ engine

struct Engine<'a> {
    db: &'a Database,
    nset: Arc<Nameset>,
    grammar: Arc<Grammar>,
    sp: Arc<StmtParse>,
    scope: Arc<ScopeResult>,
    ar: Arena,
    syn: HashMap<u32, SynInfo>,
    vars: HashMap<u32, VarInfo>,
    asrt_db: HashMap<String, Option<Rc<Assertion>>>,
    asrt_extra: HashMap<String, Rc<Assertion>>,
    names: Names,
    check: bool,
    /// mmj2's unification search list: every hypothesis-free |- assertion in
    /// database order, keyed by the root of its conclusion and the labels of
    /// the root's children (WILD for a variable)
    index: Option<SearchIndex>,
}

const WILD: u32 = u32::MAX - 1;
/// how deep mmj2-style derivation nests (a derived hypothesis proved by an
/// assertion whose own hypotheses are derived again)
const MAX_DERIVE_DEPTH: u32 = 4;

/// a justification found by the autocomplete search: the assertion, the base
/// of its metas (bound in the job), and per hypothesis an earlier step or a
/// nested derivation
#[derive(Clone)]
struct Deriv {
    a: Rc<Assertion>,
    b: u32,
    hyps: Vec<DHyp>,
}

#[derive(Clone)]
enum DHyp {
    Step(usize),
    Nested(Box<Deriv>),
}

struct SearchIndex {
    cands: Vec<Rc<Assertion>>,
    buckets: HashMap<Vec<u32>, Vec<usize>>,
}

/// per-worksheet unification state
struct Job {
    sigma: Vec<Id>,
    trail: Vec<u32>,
    /// meta id -> (step index, variable index, typecode letter W/C/S)
    meta_info: Vec<(u32, u32, u8)>,
    rcache: HashMap<Id, Id>,
}

impl Job {
    fn alloc(&mut self, a: &Assertion, step: u32) -> u32 {
        let b = self.sigma.len() as u32;
        for k in 0..a.nvars {
            self.sigma.push(NONE);
            let tc = match a.var_tcs[k].as_str() {
                "class" => b'C',
                "setvar" => b'S',
                _ => b'W',
            };
            self.meta_info.push((step, k as u32, tc));
        }
        b
    }
    fn undo(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let m = self.trail.pop().unwrap();
            self.sigma[m as usize] = NONE;
        }
    }
}

struct Unified {
    text: String,
    /// for batch registration
    reg: Rc<Assertion>,
    proof_len: usize,
}

const HYP: u32 = 1 << 31;

struct PNode {
    label: u32,
    kids: Vec<u32>,
}

/// proof nodes deduplicated by (label, kids): an identical subproof is
/// emitted once and back-referenced
#[derive(Default)]
struct PArena {
    nodes: Vec<PNode>,
    map: HashMap<(u32, Vec<u32>), u32>,
}

impl PArena {
    fn add(&mut self, label: u32, kids: Vec<u32>) -> u32 {
        if let Some(&p) = self.map.get(&(label, kids.clone())) {
            return p;
        }
        let p = self.nodes.len() as u32;
        self.map.insert((label, kids.clone()), p);
        self.nodes.push(PNode { label, kids });
        p
    }
}

impl<'a> Engine<'a> {
    fn new(db: &'a Database, check: bool) -> Self {
        Engine {
            db,
            nset: db.name_result().clone(),
            grammar: db.grammar_result().clone(),
            sp: db.stmt_parse_result().clone(),
            scope: db.scope_result().clone(),
            ar: Arena::default(),
            syn: HashMap::new(),
            vars: HashMap::new(),
            asrt_db: HashMap::new(),
            asrt_extra: HashMap::new(),
            names: Names::default(),
            check,
            index: None,
        }
    }

    /// the key of a term for the search index: root label, then each child's
    /// label or WILD for a metavariable (a concrete formula has none)
    fn skey(&self, t: Id) -> Vec<u32> {
        let n = self.ar.node(t);
        if n.flags & F_META != 0 {
            return vec![WILD];
        }
        let mut key = vec![n.label];
        for &k in self.ar.kids(t) {
            let kn = self.ar.node(k);
            key.push(if kn.flags & F_META != 0 { WILD } else { kn.label });
        }
        key
    }

    fn build_index(&mut self) -> Result<(), String> {
        let db = self.db;
        let scope = self.scope.clone();
        let mut cands: Vec<Rc<Assertion>> = vec![];
        let mut buckets: HashMap<Vec<u32>, Vec<usize>> = HashMap::new();
        for sref in db.statements() {
            if !sref.is_assertion() || sref.math_at(0).slice != b"|-" {
                continue;
            }
            let name = as_str(sref.label());
            // ProofAsstUnifySearchExclude,biigb,xxxid,dummylink
            if name == "biigb" || name == "xxxid" || name == "dummylink" {
                continue;
            }
            let frame = match scope.get(sref.label()) {
                Some(f) => f,
                None => continue,
            };
            let _ = frame;
            // ProofAsstExcludeDiscouraged defaults to true in mmj2
            if let Some(c) = sref.associated_comment() {
                let span = c.span();
                let text = span.as_ref(&c.segment().segment.buffer);
                if memfind(text, b"(New usage is discouraged.)") {
                    continue;
                }
            }
            let a = match self.assertion(name) {
                Ok(a) => a,
                Err(_) => continue,
            };
            let key = self.skey(a.concl);
            buckets.entry(key).or_default().push(cands.len());
            cands.push(a);
        }
        self.index = Some(SearchIndex { cands, buckets });
        Ok(())
    }

    /// mmj2's search for the justification of a derived ("auto") step with
    /// the concrete formula `f`: the first |- assertion in database order
    /// whose conclusion unifies with `f` and whose every hypothesis is carried
    /// by an earlier step (`recursiveAutocomplete`) or, failing that, derived
    /// again (nested, up to MAX_DERIVE_DEPTH), without a distinct-variable
    /// violation and, preferably, without any `$d` requirement ("proper");
    /// failing that the first candidate that only needs `$d` ("possible").
    /// `limit` excludes the assertions from that address on; `eterm`/`sidx`
    /// index the formulas of the steps, of which those with `opos < pg` are
    /// earlier than the derived step.
    #[allow(clippy::too_many_arguments)]
    fn autocomplete(
        &mut self,
        job: &mut Job,
        f: Id,
        step: u32,
        limit: Option<StatementAddress>,
        pg: usize,
        opos: &[usize],
        eterm: &[Id],
        sidx: &HashMap<Vec<u32>, Vec<usize>>,
        depth: u32,
        maxd: u32,
        budget: &mut u64,
    ) -> Result<Option<Deriv>, String> {
        if self.index.is_none() {
            self.build_index()?;
        }
        let cand_ix = self.lookup_keys(f, &self.index.as_ref().unwrap().buckets, usize::MAX);
        let db = self.db;
        let mut first_possible: Option<Deriv> = None;
        for &ci in &cand_ix {
            let a = self.index.as_ref().unwrap().cands[ci].clone();
            if let (Some(lim), Some(addr)) = (limit, a.addr) {
                if db.cmp_address(&addr, &lim) != std::cmp::Ordering::Less {
                    continue;
                }
            }
            // an assertion concluding a bare variable (ax-mp, mpbir, pm2.18i:
            // anything follows from anything) is never the justification of
            // a derived step: mmj2 passes them over (gourlval's nested ifex)
            if self.ar.node(a.concl).flags & F_META != 0 {
                continue;
            }
            let mark = job.trail.len();
            let b = job.alloc(&a, step);
            let concl = self.inst(a.concl, b);
            if self.unify(job, concl, f).is_ok() {
                let pats: Vec<Id> = a.ehyps.iter().map(|&h| self.inst(h, b)).collect();
                let mut chosen: Vec<Option<DHyp>> = vec![None; pats.len()];
                let mut possible: Option<Vec<Option<DHyp>>> = None;
                let r = self.auto_rec(job, &a, b, &pats, &mut chosen, step, limit, pg, opos, eterm, sidx, depth, maxd, &mut possible, budget)?;
                if r {
                    return Ok(Some(Deriv { a, b, hyps: chosen.into_iter().map(|c| c.unwrap()).collect() }));
                }
                if let (None, Some(p)) = (&first_possible, possible) {
                    first_possible = Some(Deriv { a: a.clone(), b, hyps: p.into_iter().map(|c| c.unwrap()).collect() });
                }
                if *budget == 0 {
                    return Err(format!("autocomplete search budget exhausted on |- {}", self.show(f, None)));
                }
            }
            job.undo(mark);
            job.sigma.truncate(b as usize);
            job.meta_info.truncate(b as usize);
        }
        if let Some(d) = first_possible {
            // redo the unification of the remembered candidate (its metas
            // were truncated); nested derivations are re-searched
            let mark = job.trail.len();
            let b = job.alloc(&d.a, step);
            let concl = self.inst(d.a.concl, b);
            if self.unify(job, concl, f).is_err() {
                return Err("internal: candidate stopped unifying".to_string());
            }
            let pats: Vec<Id> = d.a.ehyps.iter().map(|&h| self.inst(h, b)).collect();
            let mut hyps = vec![];
            for (j, h) in d.hyps.iter().enumerate() {
                match h {
                    DHyp::Step(t) => {
                        if self.unify(job, pats[j], eterm[*t]).is_err() {
                            job.undo(mark);
                            return Err("internal: candidate hypotheses stopped unifying".to_string());
                        }
                        hyps.push(DHyp::Step(*t));
                    }
                    DHyp::Nested(_) => {
                        let fh = self.resolve_now(job, pats[j]);
                        match self.autocomplete(job, fh, step, limit, pg, opos, eterm, sidx, depth + 1, maxd, budget)? {
                            Some(n) => hyps.push(DHyp::Nested(Box::new(n))),
                            None => return Err("internal: nested derivation stopped working".to_string()),
                        }
                    }
                }
            }
            return Ok(Some(Deriv { a: d.a, b, hyps }));
        }
        Ok(None)
    }

    /// the entries of `buckets` whose key matches `t`'s key with any subset of
    /// the child positions wildcarded (and the all-wildcard key), sorted,
    /// deduplicated, restricted to values below `max`
    fn lookup_keys(&self, t: Id, buckets: &HashMap<Vec<u32>, Vec<usize>>, max: usize) -> Vec<usize> {
        let key = self.skey(t);
        let mut out: Vec<usize> = vec![];
        let k = key.len() - 1;
        if k <= 12 {
            for mask in 0..(1u32 << k) {
                let mut q = key.clone();
                for i in 0..k {
                    if mask & (1 << i) != 0 {
                        q[i + 1] = WILD;
                    }
                }
                if let Some(v) = buckets.get(&q) {
                    out.extend(v.iter().copied().filter(|&x| x < max));
                }
            }
        } else {
            for (q, v) in buckets {
                if q.len() == key.len() && q[0] == key[0] && q.iter().zip(&key).all(|(a, b)| a == b || *a == WILD) {
                    out.extend(v.iter().copied().filter(|&x| x < max));
                }
            }
        }
        if let Some(v) = buckets.get(&vec![WILD]) {
            out.extend(v.iter().copied().filter(|&x| x < max));
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// DV status of the candidate `a` under the current sigma: 0 none, 1 needs $d, 2 violation
    fn dv_status(&mut self, job: &Job, a: &Assertion, b: u32) -> u8 {
        let mut status = 0;
        for &(i, j) in &a.dv {
            let mi = self.ar.meta(b + i);
            let mj = self.ar.meta(b + j);
            let vi = self.resolve_now(job, mi);
            let vj = self.resolve_now(job, mj);
            let xs = self.vars_of(vi);
            let ys = self.vars_of(vj);
            for &x in &xs {
                if ys.contains(&x) {
                    return 2;
                }
            }
            if !xs.is_empty() && !ys.is_empty() {
                status = 1;
            }
        }
        status
    }

    /// match the still-open hypotheses of `a` against earlier steps, the most
    /// constrained hypothesis first, deriving a hypothesis no step carries
    /// when its formula is determined; true = proper assignment found (in
    /// `chosen`, sigma bound); `possible` records the first assignment that
    /// only needs `$d`
    #[allow(clippy::too_many_arguments)]
    fn auto_rec(
        &mut self,
        job: &mut Job,
        a: &Assertion,
        b: u32,
        pats: &[Id],
        chosen: &mut Vec<Option<DHyp>>,
        step: u32,
        limit: Option<StatementAddress>,
        pg: usize,
        opos: &[usize],
        eterm: &[Id],
        sidx: &HashMap<Vec<u32>, Vec<usize>>,
        depth: u32,
        maxd: u32,
        possible: &mut Option<Vec<Option<DHyp>>>,
        budget: &mut u64,
    ) -> Result<bool, String> {
        // pick the open hypothesis with the fewest candidate steps
        let mut best: Option<(usize, Vec<usize>)> = None;
        for h in 0..pats.len() {
            if chosen[h].is_some() {
                continue;
            }
            let p = self.resolve_now(job, pats[h]);
            let cs: Vec<usize> = if self.ar.has_meta(p) {
                self.lookup_keys(p, sidx, usize::MAX).into_iter().filter(|&t| opos[t] < pg).collect()
            } else {
                match sidx.get(&self.skey(p)) {
                    Some(v) => v.iter().copied().filter(|&t| opos[t] < pg && eterm[t] == p).collect(),
                    None => vec![],
                }
            };
            if best.as_ref().map_or(true, |(_, v)| cs.len() < v.len()) {
                best = Some((h, cs));
            }
        }
        let (h, mut cs) = match best {
            Some(x) => x,
            None => {
                // all hypotheses matched
                return Ok(match self.dv_status(job, a, b) {
                    0 => true,
                    1 => {
                        if possible.is_none() {
                            *possible = Some(chosen.clone());
                        }
                        false
                    }
                    _ => false,
                });
            }
        };
        cs.sort_by_key(|&t| opos[t]);
        for t in cs {
            if *budget == 0 {
                return Ok(false);
            }
            *budget -= 1;
            let mark = job.trail.len();
            if self.unify(job, pats[h], eterm[t]).is_ok() {
                chosen[h] = Some(DHyp::Step(t));
                if self.auto_rec(job, a, b, pats, chosen, step, limit, pg, opos, eterm, sidx, depth, maxd, possible, budget)? {
                    return Ok(true);
                }
                chosen[h] = None;
            }
            job.undo(mark);
        }
        // no earlier step carries it: derive it, when it is determined and
        // the nesting depth allows
        if depth < maxd {
            let p = self.resolve_now(job, pats[h]);
            if !self.ar.has_meta(p) {
                let mark = job.trail.len();
                if let Some(d) = self.autocomplete(job, p, step, limit, pg, opos, eterm, sidx, depth + 1, maxd, budget)? {
                    chosen[h] = Some(DHyp::Nested(Box::new(d)));
                    if self.auto_rec(job, a, b, pats, chosen, step, limit, pg, opos, eterm, sidx, depth, maxd, possible, budget)? {
                        return Ok(true);
                    }
                    chosen[h] = None;
                }
                job.undo(mark);
            }
        }
        Ok(false)
    }

    /// full substitution under the current sigma, unmemoised (valid mid-way)
    fn resolve_now(&mut self, job: &Job, t: Id) -> Id {
        if !self.ar.has_meta(t) {
            return t;
        }
        let n = self.ar.node(t);
        if n.flags & F_META != 0 {
            let v = job.sigma[n.label as usize];
            return if v == NONE { t } else { self.resolve_now(job, v) };
        }
        let kids: Vec<Id> = self.ar.kids(t).to_vec();
        let new: Vec<Id> = kids.into_iter().map(|k| self.resolve_now(job, k)).collect();
        self.ar.intern(n.label, &new, n.flags & F_VAR)
    }

    // ---- database lookups

    fn syn_info(&mut self, lab: Atom) -> Result<&SynInfo, String> {
        let id = aid(lab);
        if !self.syn.contains_key(&id) {
            let nset = self.nset.clone();
            let scope = self.scope.clone();
            let name = nset.atom_name(lab);
            let frame = scope.get(name).ok_or_else(|| format!("no frame for {}", as_str(name)))?;
            let sref = self.db.statement(name).ok_or_else(|| format!("no statement {}", as_str(name)))?;
            let arity = frame.mandatory_count;
            let mut perm = vec![0u8; arity];
            let mut pos = 0usize;
            for h in frame.hypotheses.iter() {
                match h {
                    Hyp::Floating(_, k, _) => {
                        perm[*k] = pos as u8;
                        pos += 1;
                    }
                    Hyp::Essential(..) => return Err(format!("{} is not a syntax axiom", as_str(name))),
                }
            }
            let mut tmpl = vec![];
            for tok in sref.math_iter().skip(1) {
                let ls = nset.lookup_symbol(tok.slice).ok_or_else(|| format!("unknown symbol in {}", as_str(name)))?;
                if ls.stype == SymbolType::Variable {
                    let k = frame.var_list.iter().position(|&v| v == ls.atom).ok_or_else(|| format!("variable not in frame of {}", as_str(name)))?;
                    tmpl.push(Tok::K(perm[k]));
                } else {
                    tmpl.push(Tok::C(as_str(tok.slice).to_string()));
                }
            }
            self.syn.insert(id, SynInfo { name: as_str(name).to_string(), arity, perm, tmpl });
        }
        Ok(&self.syn[&id])
    }

    fn var_info(&mut self, flabel: u32, lab: Atom) -> Result<(), String> {
        if !self.vars.contains_key(&flabel) {
            let sref = self.db.statement_by_label(lab).ok_or_else(|| "unknown $f label".to_string())?;
            let sym = as_str(sref.math_at(1).slice).to_string();
            let tc = as_str(sref.math_at(0).slice).to_string();
            self.vars.insert(flabel, VarInfo { flabel: as_str(sref.label()).to_string(), sym, tc, faddr: sref.address() });
        }
        Ok(())
    }

    /// knife Formula -> arena term; variable leaves whose $f label is in `mm`
    /// become the metas mm[label]
    fn from_formula(&mut self, f: &Formula, mm: Option<&HashMap<u32, u32>>) -> Result<Id, String> {
        let mut it = f.labels_iter();
        self.build_rec(&mut it, mm)
    }

    fn build_rec(&mut self, it: &mut LabelIter<'_>, mm: Option<&HashMap<u32, u32>>) -> Result<Id, String> {
        let (lab, isvar) = it.next().ok_or_else(|| "formula tree truncated".to_string())?;
        let id = aid(lab);
        if isvar {
            if let Some(mm) = mm {
                if let Some(&k) = mm.get(&id) {
                    return Ok(self.ar.meta(k));
                }
            }
            self.var_info(id, lab)?;
            return Ok(self.ar.intern(id, &[], F_VAR));
        }
        let (arity, perm) = {
            let si = self.syn_info(lab)?;
            (si.arity, si.perm.clone())
        };
        let mut kids = vec![NONE; arity];
        for k in 0..arity {
            let c = self.build_rec(it, mm)?;
            kids[perm[k] as usize] = c;
        }
        Ok(self.ar.intern(id, &kids, 0))
    }

    fn parse_tokens(&mut self, toks: &[String]) -> Result<Id, String> {
        let mut s = String::with_capacity(toks.len() * 4 + 3);
        s.push_str("|-");
        for t in toks {
            s.push(' ');
            s.push_str(t);
        }
        let f = self.grammar.parse_string(&s, &self.nset).map_err(|e| format!("grammar: {:?}", e))?;
        let t = self.from_formula(&f, None)?;
        if self.check {
            let back = self.show(t, None);
            let orig = toks.join(" ");
            if back != orig {
                return Err(format!("round-trip mismatch:\n  in : {}\n  out: {}", orig, back));
            }
        }
        Ok(t)
    }

    fn assertion(&mut self, name: &str) -> Result<Rc<Assertion>, String> {
        if let Some(a) = self.asrt_extra.get(name) {
            return Ok(a.clone());
        }
        if let Some(a) = self.asrt_db.get(name) {
            return a.clone().ok_or_else(|| format!("{} is not an assertion", name));
        }
        let a = self.db_assertion(name)?;
        self.asrt_db.insert(name.to_string(), a.clone());
        a.ok_or_else(|| format!("{} is not an assertion of the database", name))
    }

    fn db_assertion(&mut self, name: &str) -> Result<Option<Rc<Assertion>>, String> {
        let db = self.db;
        let nset = self.nset.clone();
        let scope = self.scope.clone();
        let sp = self.sp.clone();
        let sref = match db.statement(name.as_bytes()) {
            Some(s) => s,
            None => return Ok(None),
        };
        if !sref.is_assertion() {
            return Ok(None);
        }
        let frame = scope.get(name.as_bytes()).ok_or_else(|| format!("no frame for {}", name))?;
        let provable = sref.math_at(0).slice == b"|-";
        let nv = frame.mandatory_count;
        let mut var_names = vec![];
        let mut var_tcs = vec![];
        let mut mm: HashMap<u32, u32> = HashMap::new();
        for k in 0..nv {
            let sym = frame.var_list[k];
            let lf = nset.lookup_float(nset.atom_name(sym)).ok_or_else(|| format!("no $f for a variable of {}", name))?;
            mm.insert(aid(lf.statement_atom), k as u32);
            var_names.push(as_str(nset.atom_name(sym)).to_string());
            var_tcs.push(as_str(nset.atom_name(lf.typecode_atom)).to_string());
        }
        let f = sp.get_formula(&sref).ok_or_else(|| format!("{} has no parse tree", name))?;
        let concl = self.from_formula(f, Some(&mm))?;
        let mut ehyps = vec![];
        let mut hyp_order = vec![];
        for h in frame.hypotheses.iter() {
            match h {
                Hyp::Floating(_, k, _) => hyp_order.push(HypRef::F(*k as u32)),
                Hyp::Essential(addr, _) => {
                    let es = db.statement_by_address(*addr);
                    let ef = sp.get_formula(&es).ok_or_else(|| format!("hypothesis {} of {} has no parse tree", as_str(es.label()), name))?;
                    let t = self.from_formula(ef, Some(&mm))?;
                    hyp_order.push(HypRef::E(ehyps.len() as u32));
                    ehyps.push(t);
                }
            }
        }
        let dv = frame.mandatory_dv.iter().map(|&(i, j)| (i as u32, j as u32)).collect();
        Ok(Some(Rc::new(Assertion { name: name.to_string(), addr: Some(sref.address()), nvars: nv, var_names, var_tcs, concl, ehyps, hyp_order, dv, provable })))
    }

    // ---- terms

    /// template with metas 0..n -> the same with metas base..base+n
    fn inst(&mut self, t: Id, base: u32) -> Id {
        if !self.ar.has_meta(t) {
            return t;
        }
        let n = self.ar.node(t);
        if n.flags & F_META != 0 {
            return self.ar.meta(base + n.label);
        }
        let kids: Vec<Id> = self.ar.kids(t).to_vec();
        let new: Vec<Id> = kids.into_iter().map(|k| self.inst(k, base)).collect();
        self.ar.intern(n.label, &new, n.flags & F_VAR)
    }

    #[inline]
    fn deref(&self, job: &Job, mut t: Id) -> Id {
        loop {
            let n = self.ar.node(t);
            if n.flags & F_META != 0 && job.sigma[n.label as usize] != NONE {
                t = job.sigma[n.label as usize];
            } else {
                return t;
            }
        }
    }

    fn occurs(&self, job: &Job, m: u32, t: Id) -> bool {
        let mut stack = vec![t];
        let mut seen = HashSet::new();
        while let Some(x) = stack.pop() {
            let x = self.deref(job, x);
            if !self.ar.has_meta(x) || !seen.insert(x) {
                continue;
            }
            let n = self.ar.node(x);
            if n.flags & F_META != 0 {
                if n.label == m {
                    return true;
                }
                continue;
            }
            stack.extend_from_slice(self.ar.kids(x));
        }
        false
    }

    fn unify(&mut self, job: &mut Job, a: Id, b: Id) -> Result<(), ()> {
        let mut stack = vec![(a, b)];
        while let Some((a, b)) = stack.pop() {
            let a = self.deref(job, a);
            let b = self.deref(job, b);
            if a == b {
                continue;
            }
            let na = self.ar.node(a);
            let nb = self.ar.node(b);
            if na.flags & F_META != 0 {
                if self.ar.has_meta(b) && self.occurs(job, na.label, b) {
                    return Err(());
                }
                job.sigma[na.label as usize] = b;
                job.trail.push(na.label);
                continue;
            }
            if nb.flags & F_META != 0 {
                if self.ar.has_meta(a) && self.occurs(job, nb.label, a) {
                    return Err(());
                }
                job.sigma[nb.label as usize] = a;
                job.trail.push(nb.label);
                continue;
            }
            if na.flags & F_HASMETA == 0 && nb.flags & F_HASMETA == 0 {
                return Err(()); // two concrete terms with different ids differ
            }
            if na.label != nb.label || na.nk != nb.nk || (na.flags ^ nb.flags) & F_VAR != 0 {
                return Err(());
            }
            let ka = self.ar.kids(a);
            let kb = self.ar.kids(b);
            for i in 0..ka.len() {
                stack.push((ka[i], kb[i]));
            }
        }
        Ok(())
    }

    /// full substitution under the final sigma (memoised; only after all steps)
    fn resolve(&mut self, job: &mut Job, t: Id) -> Id {
        if !self.ar.has_meta(t) {
            return t;
        }
        if let Some(&r) = job.rcache.get(&t) {
            return r;
        }
        let n = self.ar.node(t);
        let r = if n.flags & F_META != 0 {
            let v = job.sigma[n.label as usize];
            if v == NONE {
                t
            } else {
                self.resolve(job, v)
            }
        } else {
            let kids: Vec<Id> = self.ar.kids(t).to_vec();
            let new: Vec<Id> = kids.into_iter().map(|k| self.resolve(job, k)).collect();
            self.ar.intern(n.label, &new, n.flags & F_VAR)
        };
        job.rcache.insert(t, r);
        r
    }

    /// the term as a token string (without the typecode); unbound metas print
    /// as `[?k]` (k = the cited assertion's variable index)
    fn show(&self, t: Id, job: Option<&Job>) -> String {
        let mut out = String::new();
        self.show_into(t, job, &mut out);
        out
    }

    fn show_into(&self, t: Id, job: Option<&Job>, out: &mut String) {
        let t = match job {
            Some(j) => self.deref(j, t),
            None => t,
        };
        let n = self.ar.node(t);
        if n.flags & F_META != 0 {
            let k = match job {
                Some(j) => j.meta_info[n.label as usize].1,
                None => n.label,
            };
            if !out.is_empty() {
                out.push(' ');
            }
            write!(out, "[?{}]", k).unwrap();
            return;
        }
        if n.flags & F_VAR != 0 {
            if !out.is_empty() {
                out.push(' ');
            }
            out.push_str(&self.vars[&n.label].sym);
            return;
        }
        let si = &self.syn[&n.label];
        let kids = self.ar.kids(t);
        for tok in &si.tmpl {
            match tok {
                Tok::C(c) => {
                    if !out.is_empty() {
                        out.push(' ');
                    }
                    out.push_str(c);
                }
                Tok::K(p) => self.show_into(kids[*p as usize], job, out),
            }
        }
    }

    /// meta names for error messages: the assertion's own variable names
    fn show_named(&self, t: Id, job: &Job, a: &Assertion) -> String {
        let mut r = self.show(t, Some(job));
        for (k, v) in a.var_names.iter().enumerate() {
            r = r.replace(&format!("[?{}]", k), v);
        }
        r
    }

    /// variable leaves of a concrete term, deduplicated, in first-occurrence order
    fn vars_of(&self, t: Id) -> Vec<Id> {
        let mut out = vec![];
        let mut seen = HashSet::new();
        let mut stack = vec![t];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if self.ar.is_var(x) {
                out.push(x);
                continue;
            }
            let kids = self.ar.kids(x);
            for &k in kids.iter().rev() {
                stack.push(k);
            }
        }
        out
    }

    fn label_name(&self, id: u32, flags: u8) -> &str {
        if flags & F_VAR != 0 {
            &self.vars[&id].flabel
        } else {
            &self.syn[&id].name
        }
    }

    // ---- the worksheet

    fn run(&mut self, ws: &Ws) -> Result<Unified, String> {
        let n0 = ws.steps.len();
        let mut job = Job { sigma: vec![], trail: vec![], meta_info: vec![], rcache: HashMap::new() };
        // steps 0..n0 are the worksheet's; derived steps are appended after them
        let mut term: Vec<Id> = vec![NONE; n0];
        let mut base: Vec<u32> = vec![NONE; n0];
        let mut asr: Vec<Option<Rc<Assertion>>> = vec![None; n0];
        let mut cited: Vec<Vec<usize>> = vec![vec![]; n0];
        let mut failed: Vec<Option<String>> = vec![None; n0];
        let mut extras: Vec<Derived> = vec![];
        let mut derived_for: Vec<(usize, usize, bool)> = vec![]; // (parent, position, nested) per derived step
        let mut order: Vec<usize> = vec![]; // worksheet order, derived steps before their parent
        let mut greatest = ws.greatest;
        let thm_addr = self.db.statement(ws.label.as_bytes()).map(|s| s.address());
        // mmj2 names a hypothesis step `hN` by its number N: `qed:1,s3:mpd`
        let mut index: HashMap<String, usize> = HashMap::new();
        for (i, st) in ws.steps.iter().enumerate() {
            index.insert(st.name.clone(), i);
            if st.is_hyp {
                index.insert(st.name[1..].to_string(), i);
            }
        }
        let qed = *index.get("qed").ok_or_else(|| "no qed step".to_string())?;
        if ws.steps[qed].formula.is_none() {
            return Err("the qed step has no formula".to_string());
        }
        // ---- phase 1: the worksheet's steps in order
        for s in 0..n0 {
            let st = &ws.steps[s];
            if st.is_hyp {
                term[s] = self.parse_tokens(st.formula.as_ref().unwrap()).map_err(|e| format!("step {}: {}", st.name, e))?;
                order.push(s);
                continue;
            }
            let a = match self.assertion(&st.refl) {
                Ok(a) => a,
                Err(e) => {
                    failed[s] = Some(format!("step {}: {}", st.name, e));
                    order.push(s);
                    continue;
                }
            };
            if !a.provable {
                failed[s] = Some(format!("step {}: {} is a syntax axiom, not a |- assertion", st.name, a.name));
                order.push(s);
                continue;
            }
            let b = job.alloc(&a, s as u32);
            base[s] = b;
            asr[s] = Some(a.clone());
            let concl = self.inst(a.concl, b);
            term[s] = match &st.formula {
                Some(f) => {
                    let t = self.parse_tokens(f).map_err(|e| format!("step {}: {}", st.name, e))?;
                    if self.unify(&mut job, concl, t).is_err() {
                        failed[s] = Some(format!(
                            "step {}: formula does not match the conclusion of {}\n  step: |- {}\n  {}:  |- {}",
                            st.name,
                            a.name,
                            self.show(t, Some(&job)),
                            a.name,
                            self.show_named(a.concl, &job, &a)
                        ));
                        order.push(s);
                        continue;
                    }
                    t
                }
                None => concl,
            };
            let ne = a.ehyps.len();
            if st.hyps.len() > ne {
                failed[s] = Some(format!("step {}: {} takes {} hypotheses, {} given", st.name, a.name, ne, st.hyps.len()));
                order.push(s);
                continue;
            }
            let mut cs = vec![];
            let mut bad = None;
            for h in &st.hyps {
                match index.get(h.as_str()) {
                    Some(&t) if t < s && term[t] == NONE => bad = Some(format!("step {}: cites step {}, which did not unify", st.name, h)),
                    Some(&t) if t < s => cs.push(t),
                    Some(_) => bad = Some(format!("step {}: hypothesis step {} does not precede it", st.name, h)),
                    None => bad = Some(format!("step {}: unknown hypothesis step {}", st.name, h)),
                }
            }
            if let Some(m) = bad {
                failed[s] = Some(m);
                order.push(s);
                continue;
            }
            let pats: Vec<Id> = a.ehyps.iter().map(|&h| self.inst(h, b)).collect();
            let mark = job.trail.len();
            let mut first_bad = None;
            if cs.len() == ne {
                for j in 0..ne {
                    if self.unify(&mut job, pats[j], term[cs[j]]).is_err() {
                        first_bad = Some(j);
                        break;
                    }
                }
            }
            // the given hypotheses assigned to positions of the assertion's
            // hypotheses (mmj2 accepts any order and, with the Derive feature,
            // fewer hypotheses than the assertion takes)
            let mut assigned: Vec<usize> = (0..ne).collect();
            if first_bad.is_some() || cs.len() < ne {
                job.undo(mark);
                let mut used = vec![false; ne];
                let mut pos = vec![];
                if cs.len() <= 8 && self.assign(&mut job, 0, &pats, &cs, &term, &mut used, &mut pos) {
                    assigned = pos;
                } else {
                    job.undo(mark);
                    let j = first_bad.unwrap_or(0);
                    for jj in 0..j {
                        let _ = self.unify(&mut job, pats[jj], term[cs[jj]]);
                    }
                    failed[s] = Some(format!(
                        "step {}: hypothesis {} of {} does not match step {}\n  {}.{}: |- {}\n  step {}: |- {}",
                        st.name,
                        j + 1,
                        a.name,
                        ws.steps[cs[j]].name,
                        a.name,
                        j + 1,
                        self.show_named(pats[j], &job, &a),
                        ws.steps[cs[j]].name,
                        self.show(term[cs[j]], Some(&job))
                    ));
                    order.push(s);
                    continue;
                }
            }
            let mut full: Vec<usize> = vec![usize::MAX; ne];
            for (g, &p) in assigned.iter().enumerate() {
                full[p] = cs[g];
            }
            for p in 0..ne {
                if full[p] != usize::MAX {
                    continue;
                }
                // a hypothesis mmj2's Derive feature supplies: a derived step
                // before this one, resolved in phase 2
                let g = term.len();
                greatest += 1;
                extras.push(Derived { name: format!("d{}", greatest), refl: String::new() });
                derived_for.push((s, p, false));
                term.push(pats[p]);
                base.push(NONE);
                asr.push(None);
                cited.push(vec![]);
                failed.push(None);
                order.push(g);
                full[p] = g;
            }
            cited[s] = full;
            order.push(s);
        }
        // ---- phase 2: the derived steps, in creation order (all unification
        // of the worksheet's own steps is done, so their formulas are as
        // determined as they will be)
        let mut opos: Vec<usize> = vec![0; term.len()]; // position of each step in `order`
        for (i, &s) in order.iter().enumerate() {
            opos[s] = i;
        }
        let mut alias: Vec<Option<usize>> = vec![None; term.len()];
        let mut sidx: HashMap<Vec<u32>, Vec<usize>> = HashMap::new(); // key -> step ids
        let mut eterm: Vec<Id> = vec![NONE; term.len()]; // resolved formula per step (NONE if unusable)
        let mut indexed: Vec<bool> = vec![false; term.len()];
        let mut g = n0;
        while g < term.len() {
            if derived_for[g - n0].2 {
                g += 1; // a nested derivation, already justified when committed
                continue;
            }
            let (parent, p, _) = derived_for[g - n0];
            let f = self.resolve_now(&job, term[g]);
            term[g] = f;
            let a = asr[parent].clone().unwrap();
            if self.ar.has_meta(f) {
                failed[g] = Some(format!(
                    "step {}: hypothesis {} of {} is not given and not determined (mmj2 would derive it with work variables): |- {}",
                    ws.steps[parent].name, p + 1, a.name, self.show_named(f, &job, &a)
                ));
                g += 1;
                continue;
            }
            // index the steps before this one
            let pg = opos[g];
            for t in 0..term.len() {
                if indexed[t] || opos[t] >= pg {
                    continue;
                }
                indexed[t] = true;
                if failed[t].is_some() || alias[t].is_some() {
                    continue;
                }
                let ft = self.resolve_now(&job, term[t]);
                if self.ar.has_meta(ft) {
                    continue;
                }
                eterm[t] = ft;
                sidx.entry(self.skey(ft)).or_default().push(t);
            }
            // an earlier step with exactly this formula
            let mut found = None;
            if let Some(v) = sidx.get(&self.skey(f)) {
                let mut hits: Vec<usize> = v.iter().copied().filter(|&t| opos[t] < pg && eterm[t] == f).collect();
                hits.sort_by_key(|&t| opos[t]);
                found = hits.first().copied();
            }
            if let Some(t) = found {
                alias[g] = Some(t);
                cited[parent][p] = t;
                g += 1;
                continue;
            }
            // iterative deepening: the shallowest derivation, database order
            // among those of one depth
            let mut budget: u64 = 20_000_000;
            let mut found = None;
            for maxd in 0..=MAX_DERIVE_DEPTH {
                found = self.autocomplete(&mut job, f, g as u32, thm_addr, pg, &opos, &eterm, &sidx, 0, maxd, &mut budget)?;
                if found.is_some() {
                    break;
                }
            }
            match found {
                Some(d) => {
                    // commit: nested derivations become steps, numbered
                    // pre-order (a step before the steps for its
                    // hypotheses) and each inserted just before the step it
                    // justifies, as mmj2 lists them
                    let hyps = self.commit_deriv(&job, d.hyps, parent, g, g, &mut greatest, &mut extras, &mut derived_for, &mut term, &mut base, &mut asr, &mut cited, &mut failed, &mut alias, &mut eterm, &mut indexed, &mut order);
                    extras[g - n0].refl = d.a.name.clone();
                    base[g] = d.b;
                    asr[g] = Some(d.a);
                    cited[g] = hyps;
                    opos = vec![0; term.len()];
                    for (i, &s) in order.iter().enumerate() {
                        opos[s] = i;
                    }
                }
                None => {
                    failed[g] = Some(format!(
                        "step {}: hypothesis {} of {} is not given, no earlier step has its formula, and no assertion proves it from the earlier steps: |- {}",
                        ws.steps[parent].name, p + 1, a.name, self.show(f, None)
                    ));
                }
            }
            g += 1;
        }
        let n = term.len(); // including every derived step
        // ---- phase 3: reachability from qed; failures on the way are fatal
        let mut reach = vec![false; n];
        let mut stack = vec![qed];
        while let Some(s) = stack.pop() {
            if reach[s] {
                continue;
            }
            reach[s] = true;
            for &c in &cited[s] {
                if c != usize::MAX {
                    stack.push(c);
                }
            }
        }
        let name_of = |i: usize| -> &str {
            if i < n0 {
                ws.steps[i].refname()
            } else {
                &extras[i - n0].name
            }
        };
        let mut errors: Vec<String> = vec![];
        let mut warnings: Vec<String> = vec![];
        for s in 0..n {
            if let Some(m) = &failed[s] {
                if reach[s] {
                    errors.push(m.clone());
                } else {
                    warnings.push(format!("W-MMATCH unreachable {}", m.replace('\n', "\n  ")));
                }
            }
        }
        for s in 0..n {
            if failed[s].is_some() {
                continue;
            }
            term[s] = self.resolve(&mut job, term[s]);
            if self.ar.has_meta(term[s]) && reach[s] {
                let a = asr[s].as_ref().unwrap();
                errors.push(format!(
                    "step {}: formula not determined by the worksheet (mmj2 would introduce work variables): |- {}",
                    name_of(s),
                    self.show_named(term[s], &job, a)
                ));
            }
        }
        if !errors.is_empty() {
            return Err(errors.join("\nE-MMATCH "));
        }
        // the theorem's statement: hypotheses in h-step order, variables in $f order
        let hyp_steps: Vec<usize> = (0..n0).filter(|&s| ws.steps[s].is_hyp).collect();
        let mut stmt_vars: Vec<Id> = vec![];
        {
            let mut seen = HashSet::new();
            for &s in hyp_steps.iter().chain(std::iter::once(&qed)) {
                for v in self.vars_of(term[s]) {
                    if seen.insert(v) {
                        stmt_vars.push(v);
                    }
                }
            }
        }
        let db = self.db;
        stmt_vars.sort_by(|&x, &y| {
            let fx = self.vars[&self.ar.node(x).label].faddr;
            let fy = self.vars[&self.ar.node(y).label].faddr;
            db.cmp_address(&fx, &fy)
        });
        let nf = stmt_vars.len();
        let ne = hyp_steps.len();
        let mut mand: HashMap<Id, u32> = HashMap::new(); // var leaf -> $f hyp index
        for (i, &v) in stmt_vars.iter().enumerate() {
            mand.insert(v, i as u32);
        }
        let mut hyp_of_step: HashMap<usize, u32> = HashMap::new();
        for (j, &s) in hyp_steps.iter().enumerate() {
            hyp_of_step.insert(s, (nf + j) as u32);
        }
        // an existing theorem of this name: warn when the frame differs
        let scope = self.scope.clone();
        if let Some(frame) = scope.get(ws.label.as_bytes()) {
            let mut mine: Vec<String> = stmt_vars.iter().map(|&v| self.vars[&self.ar.node(v).label].sym.clone()).collect();
            mine.extend(hyp_steps.iter().map(|&s| ws.steps[s].refl.clone()));
            let mut theirs: Vec<String> = vec![];
            for h in frame.hypotheses.iter() {
                let st = db.statement_by_address(h.address());
                theirs.push(match h {
                    Hyp::Floating(..) => as_str(st.math_at(1).slice).to_string(),
                    Hyp::Essential(..) => as_str(st.label()).to_string(),
                });
            }
            if mine != theirs {
                warnings.push(format!(
                    "W-MMATCH {} is already in the database with mandatory hypotheses [{}]; this worksheet gives [{}]; the proof below fits the worksheet's",
                    ws.label,
                    theirs.join(" "),
                    mine.join(" ")
                ));
            }
        }
        // ---- distinct variables: every unified step, reachable or not (mmj2
        // accumulates the soft errors of every unified step)
        let mut req: HashSet<(String, String)> = HashSet::new();
        for s in 0..n {
            if failed[s].is_some() || alias[s].is_some() || self.ar.has_meta(term[s]) {
                continue;
            }
            let a = match &asr[s] {
                Some(a) => a.clone(),
                None => continue,
            };
            if a.dv.is_empty() {
                continue;
            }
            let b = base[s];
            let mut vals: Vec<Option<Vec<Id>>> = vec![None; a.nvars];
            for &(i, j) in &a.dv {
                for &k in &[i, j] {
                    if vals[k as usize].is_none() {
                        let m = self.ar.meta(b + k);
                        let v = self.resolve(&mut job, m);
                        vals[k as usize] = Some(self.vars_of(v));
                    }
                }
                let vi = vals[i as usize].as_ref().unwrap();
                let vj = vals[j as usize].as_ref().unwrap();
                for &u in vi {
                    for &v in vj {
                        if u == v {
                            let m = format!(
                                "step {}: {} requires $d {} {} but both are substituted with terms containing {}",
                                name_of(s),
                                a.name,
                                a.var_names[i as usize],
                                a.var_names[j as usize],
                                self.vars[&self.ar.node(u).label].sym
                            );
                            if reach[s] {
                                return Err(m);
                            }
                            warnings.push(format!("W-MMATCH unreachable {}", m));
                            continue;
                        }
                        let su = &self.vars[&self.ar.node(u).label].sym;
                        let sv = &self.vars[&self.ar.node(v).label].sym;
                        let pair = if su < sv { (su.clone(), sv.clone()) } else { (sv.clone(), su.clone()) };
                        req.insert(pair);
                    }
                }
            }
        }
        let existing: Vec<Vec<String>> = ws.lines.iter().filter_map(|l| if let Line::Dv(v) = l { Some(v.clone()) } else { None }).collect();
        let mut present: HashSet<(String, String)> = HashSet::new();
        for g in &existing {
            for i in 0..g.len() {
                for j in 0..g.len() {
                    if i != j && g[i] < g[j] {
                        present.insert((g[i].clone(), g[j].clone()));
                    }
                }
            }
        }
        let missing = req.iter().any(|p| !present.contains(p));
        let mut new_dv_lines: Vec<Vec<String>> = vec![];
        if missing {
            let mut all: Vec<(String, String)> = req.union(&present).cloned().collect();
            all.sort();
            for g in consolidate(&all) {
                let covered = existing.iter().any(|e| g.iter().all(|v| e.contains(v)));
                if !covered {
                    new_dv_lines.push(g);
                }
            }
        }
        let all_pairs: HashSet<(String, String)> = req.union(&present).cloned().collect();
        // ---- proof
        let mut pn = PArena::default();
        let mut tmemo: HashMap<Id, u32> = HashMap::new();
        let mut smemo: HashMap<usize, u32> = HashMap::new();
        let root = self.step_p(qed, &base, &asr, &cited, &mut job, &mand, &hyp_of_step, &mut pn, &mut tmemo, &mut smemo);
        let (labels, letters) = emit(&pn.nodes, root, nf + ne);
        let label_names: Vec<&str> = labels.iter().map(|&l| self.names.list[l as usize].as_str()).collect();
        // ---- output
        let mut out = String::new();
        writeln!(out, "{}", ws.header).unwrap();
        for w in &warnings {
            writeln!(out, "{}", w).unwrap();
        }
        // the derived steps printed before each worksheet step, in list order
        let mut pre: HashMap<usize, Vec<usize>> = HashMap::new();
        {
            let mut acc: Vec<usize> = vec![];
            for &t in &order {
                if t >= n0 {
                    if alias[t].is_none() {
                        acc.push(t);
                    }
                } else {
                    pre.insert(t, std::mem::take(&mut acc));
                }
            }
        }
        for l in &ws.lines {
            match l {
                Line::Raw(s) => writeln!(out, "{}", s).unwrap(),
                Line::Dv(v) => writeln!(out, "$d {} $.", v.join(" ")).unwrap(),
                Line::Step(s) => {
                    for &g in pre.get(s).map(|v| v.as_slice()).unwrap_or(&[]) {
                        let d = &extras[g - n0];
                        let hyps: Vec<&str> = cited[g].iter().map(|&c| name_of(c)).collect();
                        let f = if term[g] == NONE { "?".to_string() } else if failed[g].is_some() { self.show_work(term[g], &job) } else { self.show(term[g], None) };
                        writeln!(out, "{}:{}:{} |- {}", d.name, hyps.join(","), d.refl, f).unwrap();
                    }
                    let st = &ws.steps[*s];
                    let hyps: Vec<&str> = cited[*s].iter().map(|&c| if c == usize::MAX { "?" } else { name_of(c) }).collect();
                    let f = match &st.formula {
                        Some(f) => f.join(" "),
                        None if term[*s] == NONE => "?".to_string(),
                        None => self.show_work(term[*s], &job),
                    };
                    writeln!(out, "{}:{}:{} |- {}", st.name, hyps.join(","), st.refl, f).unwrap();
                }
            }
        }
        let proof_len = write_proof(&mut out, &label_names, &letters);
        for g in &new_dv_lines {
            writeln!(out, "$d {} $.", g.join(" ")).unwrap();
        }
        writeln!(out, "$)").unwrap();
        writeln!(out, "I-PA-0119 Theorem {}: RPN-format Metamath proof generated!", ws.label).unwrap();
        // ---- register for the batch
        let mut mm: HashMap<u32, u32> = HashMap::new();
        let mut var_names = vec![];
        let mut var_tcs = vec![];
        for (k, &v) in stmt_vars.iter().enumerate() {
            let fl = self.ar.node(v).label;
            mm.insert(fl, k as u32);
            var_names.push(self.vars[&fl].sym.clone());
            var_tcs.push(self.vars[&fl].tc.clone());
        }
        let concl = self.abstract_term(term[qed], &mm);
        let ehyps: Vec<Id> = hyp_steps.iter().map(|&s| self.abstract_term(term[s], &mm)).collect();
        let mut hyp_order = vec![];
        for k in 0..nf {
            hyp_order.push(HypRef::F(k as u32));
        }
        for j in 0..ne {
            hyp_order.push(HypRef::E(j as u32));
        }
        let mut dv = vec![];
        for i in 0..nf {
            for j in i + 1..nf {
                let (a, b) = (&var_names[i], &var_names[j]);
                let pair = if a < b { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) };
                if all_pairs.contains(&pair) {
                    dv.push((i as u32, j as u32));
                }
            }
        }
        let reg = Rc::new(Assertion { name: ws.label.clone(), addr: None, nvars: nf, var_names, var_tcs, concl, ehyps, hyp_order, dv, provable: true });
        Ok(Unified { text: out, reg, proof_len })
    }

    /// the steps for the nested derivations among `hyps` of the step `of`,
    /// numbered pre-order and inserted in `order` before `of`; returns the
    /// step ids cited for the hypotheses
    #[allow(clippy::too_many_arguments)]
    fn commit_deriv(
        &mut self,
        job: &Job,
        hyps: Vec<DHyp>,
        parent: usize,
        g: usize,
        of: usize,
        greatest: &mut u32,
        extras: &mut Vec<Derived>,
        derived_for: &mut Vec<(usize, usize, bool)>,
        term: &mut Vec<Id>,
        base: &mut Vec<u32>,
        asr: &mut Vec<Option<Rc<Assertion>>>,
        cited: &mut Vec<Vec<usize>>,
        failed: &mut Vec<Option<String>>,
        alias: &mut Vec<Option<usize>>,
        eterm: &mut Vec<Id>,
        indexed: &mut Vec<bool>,
        order: &mut Vec<usize>,
    ) -> Vec<usize> {
        let mut out = vec![];
        for (p, h) in hyps.into_iter().enumerate() {
            match h {
                DHyp::Step(t) => out.push(t),
                DHyp::Nested(nd) => {
                    let nd = *nd;
                    let ng = term.len();
                    *greatest += 1;
                    extras.push(Derived { name: format!("d{}", *greatest), refl: nd.a.name.clone() });
                    derived_for.push((g, p, true));
                    let c = self.inst(nd.a.concl, nd.b);
                    let f = self.resolve_now(job, c);
                    term.push(f);
                    base.push(nd.b);
                    asr.push(Some(nd.a.clone()));
                    cited.push(vec![]);
                    failed.push(None);
                    alias.push(None);
                    eterm.push(NONE);
                    indexed.push(false);
                    let at = order.iter().position(|&x| x == of).expect("the justified step is listed");
                    order.insert(at, ng);
                    let sub = self.commit_deriv(job, nd.hyps, parent, g, ng, greatest, extras, derived_for, term, base, asr, cited, failed, alias, eterm, indexed, order);
                    cited[ng] = sub;
                    out.push(ng);
                }
            }
        }
        out
    }

    /// a formula with its unbound metas shown as mmj2 work variables
    /// (`&W1`, `&C2`, `&S3`: numbered per typecode within the formula)
    fn show_work(&self, t: Id, job: &Job) -> String {
        let mut s = self.show(t, Some(job));
        if !s.contains("[?") {
            return s;
        }
        // the metas of the term, in order of appearance
        let mut metas: Vec<u32> = vec![];
        let mut stack = vec![t];
        while let Some(x) = stack.pop() {
            let x = self.deref(job, x);
            let n = self.ar.node(x);
            if n.flags & F_META != 0 {
                if !metas.contains(&n.label) {
                    metas.push(n.label);
                }
                continue;
            }
            for &k in self.ar.kids(x).iter().rev() {
                stack.push(k);
            }
        }
        let mut counts: HashMap<u8, u32> = HashMap::new();
        for m in metas {
            let (_step, k, tc) = job.meta_info[m as usize];
            let c = counts.entry(tc).or_insert(0);
            *c += 1;
            s = s.replace(&format!("[?{}]", k), &format!("&{}{}", tc as char, c));
        }
        s
    }

    /// assign the given hypothesis steps `cs`, in order, to distinct positions
    /// of the assertion's hypotheses `pats` (lowest positions first); on
    /// success `pos[g]` is the position of the g-th given step and sigma holds
    /// the unification
    #[allow(clippy::too_many_arguments)]
    fn assign(&mut self, job: &mut Job, g: usize, pats: &[Id], cs: &[usize], term: &[Id], used: &mut Vec<bool>, pos: &mut Vec<usize>) -> bool {
        if g == cs.len() {
            return true;
        }
        for p in 0..pats.len() {
            if used[p] {
                continue;
            }
            let mark = job.trail.len();
            if self.unify(job, pats[p], term[cs[g]]).is_ok() {
                used[p] = true;
                pos.push(p);
                if self.assign(job, g + 1, pats, cs, term, used, pos) {
                    return true;
                }
                pos.pop();
                used[p] = false;
            }
            job.undo(mark);
        }
        false
    }

    /// concrete term -> template: variable leaves in mm become metas
    fn abstract_term(&mut self, t: Id, mm: &HashMap<u32, u32>) -> Id {
        let n = self.ar.node(t);
        if n.flags & F_VAR != 0 {
            return match mm.get(&n.label) {
                Some(&k) => self.ar.meta(k),
                None => t,
            };
        }
        if n.nk == 0 {
            return t;
        }
        let kids: Vec<Id> = self.ar.kids(t).to_vec();
        let new: Vec<Id> = kids.into_iter().map(|k| self.abstract_term(k, mm)).collect();
        self.ar.intern(n.label, &new, 0)
    }

    #[allow(clippy::too_many_arguments)]
    fn step_p(
        &mut self,
        s: usize,
        base: &[u32],
        asr: &[Option<Rc<Assertion>>],
        cited: &[Vec<usize>],
        job: &mut Job,
        mand: &HashMap<Id, u32>,
        hyp_of_step: &HashMap<usize, u32>,
        pn: &mut PArena,
        tmemo: &mut HashMap<Id, u32>,
        smemo: &mut HashMap<usize, u32>,
    ) -> u32 {
        if let Some(&p) = smemo.get(&s) {
            return p;
        }
        if let Some(&h) = hyp_of_step.get(&s) {
            return h | HYP;
        }
        let a = asr[s].clone().unwrap();
        let mut kids = vec![];
        for h in &a.hyp_order {
            match h {
                HypRef::F(k) => {
                    let m = self.ar.meta(base[s] + k);
                    let v = self.resolve(job, m);
                    kids.push(self.term_p(v, mand, pn, tmemo));
                }
                HypRef::E(j) => {
                    let c = cited[s][*j as usize];
                    kids.push(self.step_p(c, base, asr, cited, job, mand, hyp_of_step, pn, tmemo, smemo));
                }
            }
        }
        let lab = self.names.get(&a.name);
        let p = pn.add(lab, kids);
        smemo.insert(s, p);
        p
    }

    fn term_p(&mut self, t: Id, mand: &HashMap<Id, u32>, pn: &mut PArena, tmemo: &mut HashMap<Id, u32>) -> u32 {
        if let Some(&p) = tmemo.get(&t) {
            return p;
        }
        if let Some(&h) = mand.get(&t) {
            let p = h | HYP;
            tmemo.insert(t, p);
            return p;
        }
        let n = self.ar.node(t);
        let kids: Vec<Id> = self.ar.kids(t).to_vec();
        let pk: Vec<u32> = kids.into_iter().map(|k| self.term_p(k, mand, pn, tmemo)).collect();
        let name = self.label_name(n.label, n.flags).to_string();
        let lab = self.names.get(&name);
        let p = pn.add(lab, pk);
        tmemo.insert(t, p);
        p
    }
}

enum Item {
    Hyp(u32),
    Lab(u32),
    Back(u32),
    Z,
}

/// RPN items for the DAG rooted at `root`, then the label list (first use)
/// and the letter string; `nh` = number of mandatory hypotheses
fn emit(pn: &[PNode], root: u32, nh: usize) -> (Vec<u32>, String) {
    let mut parents = vec![0u32; pn.len()];
    let mut seen = vec![false; pn.len()];
    let mut stack = vec![root];
    while let Some(p) = stack.pop() {
        if p & HYP != 0 || seen[p as usize] {
            continue;
        }
        seen[p as usize] = true;
        for &k in &pn[p as usize].kids {
            if k & HYP == 0 {
                parents[k as usize] += 1;
                stack.push(k);
            }
        }
    }
    let mut items: Vec<Item> = vec![];
    let mut saved = vec![0u32; pn.len()];
    let mut count = 0u32;
    let mut st: Vec<(u32, usize)> = vec![(root, 0)];
    while let Some(&(p, i)) = st.last() {
        if p & HYP != 0 {
            items.push(Item::Hyp(p & !HYP));
            st.pop();
            continue;
        }
        let node = &pn[p as usize];
        if i < node.kids.len() {
            let c = node.kids[i];
            st.last_mut().unwrap().1 += 1;
            if c & HYP == 0 && saved[c as usize] != 0 {
                items.push(Item::Back(saved[c as usize]));
            } else {
                st.push((c, 0));
            }
            continue;
        }
        items.push(Item::Lab(node.label));
        if parents[p as usize] > 1 && !node.kids.is_empty() {
            count += 1;
            saved[p as usize] = count;
            items.push(Item::Z);
        }
        st.pop();
    }
    // the label list: most used first (the first 20 - nh get one letter),
    // ties in order of first use
    let mut labels: Vec<u32> = vec![];
    let mut uses: HashMap<u32, usize> = HashMap::new();
    for it in &items {
        if let Item::Lab(l) = it {
            if !uses.contains_key(l) {
                labels.push(*l);
            }
            *uses.entry(*l).or_insert(0) += 1;
        }
    }
    labels.sort_by_key(|l| std::cmp::Reverse(uses[l]));
    let mut lpos: HashMap<u32, usize> = HashMap::new();
    for (i, &l) in labels.iter().enumerate() {
        lpos.insert(l, i);
    }
    let nl = labels.len();
    let mut letters = String::with_capacity(items.len() * 2);
    for it in &items {
        let num = match it {
            Item::Hyp(h) => *h as usize + 1,
            Item::Lab(l) => nh + lpos[l] + 1,
            Item::Back(k) => nh + nl + *k as usize,
            Item::Z => {
                letters.push('Z');
                continue;
            }
        };
        enc(num, &mut letters);
    }
    (labels, letters)
}

fn memfind(hay: &[u8], needle: &[u8]) -> bool {
    hay.windows(needle.len()).any(|w| w == needle)
}

fn enc(num: usize, out: &mut String) {
    let last = (b'A' + ((num - 1) % 20) as u8) as char;
    let mut n = (num - 1) / 20;
    let mut pre = vec![];
    while n > 0 {
        let d = (n - 1) % 5 + 1;
        pre.push((b'U' + (d - 1) as u8) as char);
        n = (n - d) / 5;
    }
    for c in pre.into_iter().rev() {
        out.push(c);
    }
    out.push(last);
}

/// `$=    ( labels ) LETTERS $.` wrapped at 79 columns with mmj2's 6-space
/// continuation indent; returns the proof length in characters
fn write_proof(out: &mut String, labels: &[&str], letters: &str) -> usize {
    const W: usize = 79;
    let mut cur = String::from("$=    (");
    let mut total = 0usize;
    let flush = |out: &mut String, cur: &mut String| {
        out.push_str(cur);
        out.push('\n');
        cur.clear();
        cur.push_str("      ");
    };
    for l in labels {
        total += l.len() + 1;
        if cur.len() + 1 + l.len() > W {
            flush(out, &mut cur);
        }
        cur.push(' ');
        cur.push_str(l);
    }
    if cur.len() + 2 > W {
        flush(out, &mut cur);
    }
    cur.push_str(" )");
    total += letters.len() + 4;
    let mut rest = letters;
    while !rest.is_empty() {
        let room = W.saturating_sub(cur.len() + 1);
        if room < 8 {
            flush(out, &mut cur);
            continue;
        }
        let take = room.min(rest.len());
        cur.push(' ');
        cur.push_str(&rest[..take]);
        rest = &rest[take..];
    }
    if cur.len() + 3 > W {
        flush(out, &mut cur);
    }
    cur.push_str(" $.");
    out.push_str(&cur);
    out.push('\n');
    total
}

/// mmj2's `ScopeFrame.consolidateDvGroups` on pairs sorted by (lo, hi)
fn consolidate(dv: &[(String, String)]) -> Vec<Vec<String>> {
    let mut groups: Vec<Vec<String>> = vec![];
    let mut done = vec![false; dv.len()];
    let mut first = 0usize;
    while first < dv.len() {
        let lo = &dv[first].0;
        let mut last = first + 1;
        loop {
            if last < dv.len() && dv[last].0 == *lo {
                last += 1;
            } else {
                last -= 1;
                break;
            }
        }
        for i in first..=last {
            if done[i] {
                continue;
            }
            let mut group = vec![dv[i].0.clone(), dv[i].1.clone()];
            done[i] = true;
            let mut before_end = true;
            for j in first..=last {
                if j == i {
                    before_end = false;
                    continue;
                }
                let mut checked = vec![];
                if all_disjoint(&dv[j].1, &group, dv, last, &mut checked) {
                    done[j] = true;
                    if before_end {
                        let idx = group.len() - 1;
                        group.insert(idx, dv[j].1.clone());
                    } else {
                        group.push(dv[j].1.clone());
                    }
                    for k in checked {
                        done[k] = true;
                    }
                }
            }
            groups.push(group);
        }
        first = last + 1;
    }
    groups
}

fn all_disjoint(v: &str, group: &[String], dv: &[(String, String)], mut idx: usize, checked: &mut Vec<usize>) -> bool {
    checked.clear();
    'outer: for g in group.iter().skip(1) {
        let (lo, hi) = if g.as_str() < v { (g.as_str(), v) } else { (v, g.as_str()) };
        loop {
            idx += 1;
            if idx >= dv.len() {
                return false;
            }
            let c = (dv[idx].0.as_str(), dv[idx].1.as_str()).cmp(&(lo, hi));
            if c == std::cmp::Ordering::Greater {
                return false;
            }
            if c == std::cmp::Ordering::Equal {
                checked.push(idx);
                continue 'outer;
            }
        }
    }
    true
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut check = false;
    let mut timing = false;
    let mut files: Vec<String> = vec![];
    for a in &args {
        match a.as_str() {
            "--batch" => {}
            "--check" => check = true,
            "--time" => timing = true,
            _ if a.starts_with("--") => {
                eprintln!("mmatch: unknown option {}", a);
                std::process::exit(3);
            }
            _ => files.push(a.clone()),
        }
    }
    if files.len() < 2 {
        eprintln!("usage: mmatch [--batch] [--check] [--time] DB WORKSHEET.mmp...");
        std::process::exit(3);
    }
    // deep recursion on long formulas: run on a big stack
    let child = std::thread::Builder::new().stack_size(1 << 30).spawn(move || real_main(files, check, timing)).unwrap();
    let code = child.join().unwrap_or(3);
    std::process::exit(code);
}

fn real_main(files: Vec<String>, check: bool, timing: bool) -> i32 {
    let t0 = Instant::now();
    let jobs = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(2).min(8);
    let mut db = Database::new(DbOptions { incremental: true, jobs, ..DbOptions::default() });
    db.parse(files[0].clone(), vec![]);
    db.name_pass();
    db.scope_pass();
    let diags = db.diag_notations();
    if !diags.is_empty() {
        for (addr, d) in diags.iter().take(10) {
            let s = db.statement_by_address(*addr);
            println!("E-MMATCH database diagnostic at {}: {:?}", as_str(s.label()), d);
        }
        println!("E-MMATCH {} does not load cleanly ({} diagnostics)", files[0], diags.len());
        return 3;
    }
    db.grammar_pass();
    db.stmt_parse_pass();
    if timing {
        eprintln!("mmatch: database loaded and parsed in {:.2?}", t0.elapsed());
    }
    let mut eng = Engine::new(&db, check);
    let mut status = 0;
    for ws_path in &files[1..] {
        let t1 = Instant::now();
        let text = match std::fs::read_to_string(ws_path) {
            Ok(t) => t,
            Err(e) => {
                println!("E-MMATCH cannot read {}: {}", ws_path, e);
                status = status.max(3);
                continue;
            }
        };
        let ws = match parse_ws(&text) {
            Ok(w) => w,
            Err((code, msg)) => {
                println!("E-MMATCH {}: {}", ws_path, msg);
                status = status.max(code);
                continue;
            }
        };
        match eng.run(&ws) {
            Ok(u) => {
                print!("{}", u.text);
                if timing {
                    eprintln!("mmatch: {} ({} steps, proof {} chars) in {:.2?}", ws.label, ws.steps.len(), u.proof_len, t1.elapsed());
                }
                eng.asrt_extra.insert(ws.label.clone(), u.reg);
            }
            Err(msg) => {
                println!("E-MMATCH {}: {}", ws.label, msg);
                status = status.max(1);
            }
        }
    }
    status
}
