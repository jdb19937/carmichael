"""Sortie Z4b helpers (Route Z: LargeSieve.lean 627-1010 and 1780-2004, the
analytic block and the window sieve).

STATEMENTS / HYPS are the frozen statements of Z4b-blueprint.md in one place,
so the blueprint, the grammar check and the generators cannot drift apart.
`MM_DB=sorties/z4b.mm python3 tools/z4blib.py [LABEL...]` grammar-checks them
(mmj2 unify on a bare `qed` worksheet).
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W
from z4alib import CR, PC, DIV, EAT, HW, ABS2, CJ, BLK, COPALL

C2 = '( 2 x. ( _i x. _pi ) )'
HWM = '( %s /\\ M e. ZZ )' % HW


def TRIG(A, t, n='n'):
    """sum_ n e. W ( ( A ` n ) x. EAT( ( n - M ) , t ) ): the trigonometric polynomial f ( t )"""
    return 'sum_ %s e. W ( ( %s ` %s ) x. %s )' % (n, A, n, EAT('( %s - M )' % n, t))


def FT(A, t='t'): return '( %s e. RR |-> %s )' % (t, TRIG(A, t))
AD = '( j e. W |-> ( ( A ` j ) x. ( %s x. ( j - M ) ) ) )' % C2      # the derivative's weights
def SW(A, n='n'): return 'sum_ %s e. W %s' % (n, ABS2('( %s ` %s )' % (A, n)))
def ITG(X, E, t='t'): return 'S. %s %s _d %s' % (X, E, t)
def IOO(a, b): return '( %s (,) %s )' % (a, b)
def ICC(a, b): return '( %s [,] %s )' % (a, b)
def JI(y, D='D'): return IOO('( %s - ( %s / 2 ) )' % (y, D), '( %s + ( %s / 2 ) )' % (y, D))
def KP(D='D'): return IOO('-u ( %s / 2 )' % D, '( -u ( %s / 2 ) + 1 )' % D)
CNR = '( RR -cn-> CC )'
HF = '( F : RR --> CC /\\ ( RR _D F ) = G /\\ G e. %s )' % CNR
def FA2(F, t): return ABS2('( %s ` %s )' % (F, t))
def FG2(t): return '( ( 2 x. ( abs ` ( F ` %s ) ) ) x. ( abs ` ( G ` %s ) ) )' % (t, t)
NF = '( t e. RR |-> ( ( F ` t ) x. ( * ` ( F ` t ) ) ) )'
DNF = '( t e. RR |-> ( ( ( G ` t ) x. ( * ` ( F ` t ) ) ) + ( ( * ` ( G ` t ) ) x. ( F ` t ) ) ) )'
SEP = 'A. a e. P A. b e. P ( a =/= b -> D <_ ( abs ` ( ( Y ` a ) - ( Y ` b ) ) ) )'
RNG = 'A. a e. P ( 0 <_ ( Y ` a ) /\\ ( Y ` a ) <_ ( 1 - D ) )'
PTS = '( P e. Fin /\\ Y : P --> RR /\\ D e. RR+ )'
FRQ = 'A. m e. W ( abs ` ( m - M ) ) <_ E'
Q0 = '( |_ ` Q )'
Q0S = '( 1 ... %s )' % Q0
COPQ = 'A. s e. %s A. m e. W ( m gcd s ) = 1' % Q0S
HWIN = '( ( Q e. RR /\\ 2 <_ Q ) /\\ %s /\\ ( E e. RR+ /\\ %s /\\ %s ) )' % (HWM, COPQ, FRQ)
FP = 'U_ q e. %s ( { q } X. %s )' % (Q0S, CR('q'))
YF = '( p e. %s |-> ( ( 2nd ` p ) / ( 1st ` p ) ) )' % FP
def RF(N, f='f'):
    """Lean's r-range at conductor f: { r in Icc 1 N | r f <= N, squarefree r, coprime r f }"""
    return '{ r e. ( 1 ... %s ) | ( ( r x. %s ) <_ %s /\\ ( ( mmu ` r ) =/= 0 /\\ ( r gcd %s ) = 1 ) ) }' % (N, f, N, f)
WR = lambda: '( ( 4 x. _pi ) x. E )'

STATEMENTS = {}
HYPS = {}

# ---- section A: integral_eAt
STATEMENTS['eatdv'] = '( V e. CC -> ( RR _D ( t e. RR |-> %s ) ) = ( t e. RR |-> ( ( %s x. V ) x. %s ) ) )' % (EAT('V', 't'), C2, EAT('V', 't'))
STATEMENTS['eatcn'] = '( V e. CC -> ( t e. RR |-> %s ) e. %s )' % (EAT('V', 't'), CNR)
STATEMENTS['eatcj'] = '( ( V e. RR /\\ B e. RR ) -> ( * ` %s ) = %s )' % (EAT('V', 'B'), EAT('-u V', 'B'))
STATEMENTS['eatper'] = '( ( V e. ZZ /\\ B e. CC ) -> %s = %s )' % (EAT('V', '( B + 1 )'), EAT('V', 'B'))
STATEMENTS['eatitg'] = '( ( V e. ZZ /\\ C e. RR ) -> %s = if ( V = 0 , 1 , 0 ) )' % ITG(IOO('C', '( C + 1 )'), EAT('V', 't'))
HYPS['lsibl'] = [('a', '( ph -> A e. RR )'), ('b', '( ph -> B e. RR )'), ('c', '( ph -> ( t e. RR |-> X ) e. %s )' % CNR)]
STATEMENTS['lsibl'] = '( ph -> ( t e. %s |-> X ) e. L^1 )' % IOO('A', 'B')
STATEMENTS['lsftc'] = '( ( ( A e. RR /\\ B e. RR /\\ A <_ B ) /\\ %s ) -> %s = ( ( F ` B ) - ( F ` A ) ) )' % (HF, ITG(IOO('A', 'B'), '( G ` t )'))

# ---- section B: parseval_period
STATEMENTS['lsdw'] = '( %s -> %s : W --> CC )' % (HWM, AD)
STATEMENTS['lstrigdv'] = '( %s -> ( RR _D %s ) = %s )' % (HWM, FT('A'), FT(AD))
STATEMENTS['lstrigcn'] = '( %s -> %s e. %s )' % (HWM, FT('A'), CNR)
STATEMENTS['lsparlem1'] = '( ( %s /\\ t e. RR ) -> %s = sum_ n e. W sum_ m e. W ( ( ( A ` n ) x. ( * ` ( A ` m ) ) ) x. %s ) )' % (
    HWM, ABS2(TRIG('A', 't')), EAT('( n - m )', 't'))
STATEMENTS['lsparlem2'] = ('( ( ( %s /\\ C e. RR ) /\\ n e. W ) -> ( ( t e. %s |-> sum_ m e. W ( ( ( A ` n ) x. ( * ` ( A ` m ) ) ) x. %s ) ) e. L^1 /\\ '
                           '%s = ( ( abs ` ( A ` n ) ) ^ 2 ) ) )' % (
    HWM, IOO('C', '( C + 1 )'), EAT('( n - m )', 't'),
    ITG(IOO('C', '( C + 1 )'), 'sum_ m e. W ( ( ( A ` n ) x. ( * ` ( A ` m ) ) ) x. %s )' % EAT('( n - m )', 't'))))
STATEMENTS['lsparper'] = '( ( %s /\\ C e. RR ) -> %s = %s )' % (HWM, ITG(IOO('C', '( C + 1 )'), ABS2(TRIG('A', 't'))), SW('A'))

# ---- section C: sobolev_sq_le
HYPS['lsitgmono'] = [('a', '( ph -> A e. RR )'), ('b', '( ph -> B e. RR )'), ('u', '( ph -> U e. RR )'), ('v', '( ph -> V e. RR )'),
                     ('au', '( ph -> A <_ U )'), ('uv', '( ph -> U <_ V )'), ('vb', '( ph -> V <_ B )'),
                     ('c', '( ph -> ( t e. RR |-> X ) e. %s )' % CNR), ('r', '( ( ph /\\ t e. RR ) -> X e. RR )'),
                     ('p', '( ( ph /\\ t e. RR ) -> 0 <_ X )')]
STATEMENTS['lsitgmono'] = '( ph -> %s <_ %s )' % (ITG(IOO('U', 'V'), 'X'), ITG(IOO('A', 'B'), 'X'))
STATEMENTS['lssoblem1'] = '( %s -> ( ( RR _D %s ) = %s /\\ %s e. %s ) )' % (HF, NF, DNF, DNF, CNR)
STATEMENTS['lssoblem2'] = '( ( %s /\\ ( U e. RR /\\ V e. RR /\\ U <_ V ) ) -> ( abs ` ( %s - %s ) ) <_ %s )' % (
    HF, FA2('F', 'V'), FA2('F', 'U'), ITG(IOO('U', 'V'), FG2('s'), 's'))
STATEMENTS['lssoblem3'] = '( ( %s /\\ ( ( A e. RR /\\ B e. RR ) /\\ ( X e. %s /\\ Y e. %s ) ) ) -> %s <_ ( %s + %s ) )' % (
    HF, ICC('A', 'B'), ICC('A', 'B'), FA2('F', 'X'), FA2('F', 'Y'), ITG(IOO('A', 'B'), FG2('s'), 's'))
STATEMENTS['lssob'] = '( ( %s /\\ ( D e. RR+ /\\ X e. RR ) ) -> %s <_ ( ( ( 1 / D ) x. %s ) + %s ) )' % (
    HF, FA2('F', 'X'), ITG(JI('X'), FA2('F', 't')), ITG(JI('X'), FG2('t')))

# ---- section D: points_large_sieve
STATEMENTS['lsdisjpt'] = '( ( %s /\\ %s /\\ ( H e. RR /\\ 0 <_ H ) ) -> sum_ i e. P if ( t e. %s , H , 0 ) <_ H )' % (PTS, SEP, JI('( Y ` i )'))
HYPS['lsdisj'] = [('p', '( ph -> %s )' % PTS), ('s', '( ph -> %s )' % SEP), ('g', '( ph -> %s )' % RNG),
                  ('c', '( ph -> ( t e. RR |-> X ) e. %s )' % CNR), ('r', '( ( ph /\\ t e. RR ) -> X e. RR )'),
                  ('n', '( ( ph /\\ t e. RR ) -> 0 <_ X )')]
STATEMENTS['lsdisj'] = '( ph -> sum_ i e. P %s <_ %s )' % (ITG(JI('( Y ` i )'), 'X'), ITG(KP(), 'X'))
STATEMENTS['lsamgm'] = '( ( ( X e. RR /\\ Y e. RR ) /\\ T e. RR+ ) -> ( ( 2 x. X ) x. Y ) <_ ( ( T x. ( X ^ 2 ) ) + ( ( 1 / T ) x. ( Y ^ 2 ) ) ) )'
STATEMENTS['lsptsg'] = '( ( %s /\\ %s /\\ ( %s /\\ %s /\\ T e. RR+ ) ) -> sum_ i e. P %s <_ ( ( ( ( 1 / D ) + T ) x. %s ) + ( ( 1 / T ) x. %s ) ) )' % (
    HF, PTS, SEP, RNG, FA2('F', '( Y ` i )'), ITG(KP(), FA2('F', 't')), ITG(KP(), FA2('G', 't')))
# ---- section D helpers (frozen with the headlines they serve)
STATEMENTS['lsptslem1'] = '( ( %s /\\ %s /\\ ( %s /\\ %s ) ) -> sum_ i e. P %s <_ ( ( ( 1 / D ) x. %s ) + %s ) )' % (
    HF, PTS, SEP, RNG, FA2('F', '( Y ` i )'), ITG(KP(), FA2('F', 't')), ITG(KP(), FG2('t')))
STATEMENTS['lsptslem2'] = '( ( %s /\\ ( D e. RR+ /\\ T e. RR+ ) ) -> %s <_ ( ( T x. %s ) + ( ( 1 / T ) x. %s ) ) )' % (
    HF, ITG(KP(), FG2('t')), ITG(KP(), FA2('F', 't')), ITG(KP(), FA2('G', 't')))
STATEMENTS['lsdwbnd'] = '( ( %s /\\ ( E e. RR /\\ %s ) ) -> %s <_ ( ( ( 4 x. ( _pi ^ 2 ) ) x. ( E ^ 2 ) ) x. %s ) )' % (HWM, FRQ, SW(AD), SW('A'))
STATEMENTS['lspts'] = '( ( %s /\\ %s /\\ ( %s /\\ %s /\\ ( E e. RR+ /\\ %s ) ) ) -> sum_ i e. P %s <_ ( ( ( 1 / D ) + %s ) x. %s ) )' % (
    HWM, PTS, SEP, RNG, FRQ, ABS2(TRIG('A', '( Y ` i )')), WR(), SW('A'))

# ---- section E: window_sieve (steps 2-5), the regrouping, and the frozen assembly
STATEMENTS['lswinmem'] = '( p e. %s -> ( p = <. ( 1st ` p ) , ( 2nd ` p ) >. /\\ ( 1st ` p ) e. %s /\\ ( 2nd ` p ) e. %s ) )' % (FP, Q0S, CR('( 1st ` p )'))
# ---- section E helpers
DQ2 = '( 1 / ( Q ^ 2 ) )'
STATEMENTS['lsblkre'] = '( ( f e. NN /\\ %s ) -> ( %s e. RR /\\ 0 <_ %s ) )' % (HW, BLK('f'), BLK('f'))
PTSF = '( %s e. Fin /\\ %s : %s --> RR /\\ %s e. RR+ )' % (FP, YF, FP, DQ2)
SEPF = 'A. a e. %s A. b e. %s ( a =/= b -> %s <_ ( abs ` ( ( %s ` a ) - ( %s ` b ) ) ) )' % (FP, FP, DQ2, YF, YF)
RNGF = 'A. a e. %s ( 0 <_ ( %s ` a ) /\\ ( %s ` a ) <_ ( 1 - %s ) )' % (FP, YF, YF, DQ2)
STATEMENTS['lswinlem1'] = '( ( Q e. RR /\\ 2 <_ Q ) -> %s )' % PTSF
STATEMENTS['lswinlem2'] = '( ( Q e. RR /\\ 2 <_ Q ) -> %s )' % SEPF
STATEMENTS['lswinlem3'] = '( ( Q e. RR /\\ 2 <_ Q ) -> %s )' % RNGF
STATEMENTS['lswinlem4'] = '( ( Q e. RR /\\ %s ) -> sum_ q e. %s sum_ u e. %s %s = sum_ i e. %s %s )' % (
    HWM, Q0S, CR('q'), ABS2(TRIG('A', '( u / q )')), FP, ABS2(TRIG('A', '( %s ` i )' % YF)))
STATEMENTS['lswin'] = '( %s -> sum_ q e. %s sum_ f e. %s ( ( f / ( phi ` q ) ) x. %s ) <_ ( ( ( Q ^ 2 ) + %s ) x. %s ) )' % (
    HWIN, Q0S, DIV('q'), BLK('f'), WR(), SW('A'))
def TG(N, f='f'):
    """the moduli q <_ N at which f is a DIV-divisor"""
    return '{ g e. ( 1 ... %s ) | %s e. %s }' % (N, f, DIV('g'))
STATEMENTS['lswinreglem1'] = '( ( N e. NN0 /\\ f e. ( 1 ... N ) ) -> ( l e. %s |-> ( l x. f ) ) : %s -1-1-onto-> %s )' % (RF('N'), RF('N'), TG('N'))
HYPS['lswinreg'] = [('n', '( ph -> N e. NN0 )'), ('b', '( ( ph /\\ f e. NN ) -> B e. CC )')]
STATEMENTS['lswinreg'] = '( ph -> sum_ f e. ( 1 ... N ) sum_ r e. %s ( ( f / ( phi ` ( r x. f ) ) ) x. B ) = sum_ q e. ( 1 ... N ) sum_ f e. %s ( ( f / ( phi ` q ) ) x. B ) )' % (
    RF('N'), DIV('q'))

# frozen for Z4c (not proved here): Lean's hstep1 and window_sieve itself
LATER = {}
LATER['lswinw'] = '( ( ( Q e. RR /\\ 2 <_ Q ) /\\ f e. %s /\\ ( B e. RR /\\ 0 <_ B ) ) -> ( ( log ` ( Q / f ) ) x. B ) <_ sum_ r e. %s ( ( f / ( phi ` ( r x. f ) ) ) x. B ) )' % (
    Q0S, RF(Q0))
LATER['lswsieve'] = '( %s -> sum_ f e. %s ( ( log ` ( Q / f ) ) x. %s ) <_ ( ( ( Q ^ 2 ) + %s ) x. %s ) )' % (HWIN, Q0S, BLK('f'), WR(), SW('A'))


def hyp(w, n, label, formula):
    w.s([], label, formula, name='h' + n)
    return n


def hyps_of(w, lab):
    return [hyp(w, n, '%s.%s' % (lab, n), f) for n, f in HYPS.get(lab, [])]


def gramcheck(labels):
    import mm as _MM
    out = {}
    for lab in labels:
        w = W('z4bg' + lab, 'grammar check of %s' % lab)
        hyps_of(w, lab)
        w.lines.append('qed:?:? |- %s' % (STATEMENTS.get(lab) or LATER[lab]))
        w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out


if __name__ == '__main__':
    labs = sys.argv[1:] or list(STATEMENTS) + list(LATER)
    for lab, bad in gramcheck(labs).items():
        print(('OK   ' if not bad else 'BAD  ') + lab)
        for l in bad[:5]:
            print('   ', l[:300])


# ------------------------------------------------------------------ worksheet helpers
from cl import Closure, ClosureError, formula_of, strip_ante, split_imp, lift, split_top
import cl as _cl
# an integral `S. A B _d x` is one top-level piece (a runtime table entry; tools/cl.py is unchanged),
# so that tools/lin.py reads it as an atom as it does a sum_
_cl.PREFIX_ARITY.setdefault('S.', 4)
import lin as _lin
_lin.FASTPATH = True


def st(w, ante, hyps, ref, concl, name=None):
    """deduction step ( ante -> concl ) by REF from HYPS"""
    return w.s(list(hyps), ref, '( %s -> %s )' % (ante, concl), name=name)


def a1(w, ante, ref, fact):
    """closed fact FACT by REF, lifted with a1i"""
    c = w.s([], ref, fact)
    return w.s([c], 'a1i', '( %s -> %s )' % (ante, fact))


def ap(w, ante, ref, hyps, concl):
    """apply the closed lemma REF (antecedent = conjunction of HYPS' formulas) in deduction form"""
    i = w.inst(ref)
    if not hyps:
        return w.s([i], 'ax-mp', concl)
    rule = {1: 'syl', 2: 'syl2anc', 3: 'syl3anc'}[len(hyps)]
    return w.s(list(hyps) + [i], rule, '( %s -> %s )' % (ante, concl))


def body(w, step, ante):
    return strip_ante(formula_of(w, step), ante)


def J(w, ante, *steps):
    """( ante -> ( f1 /\\ f2 ) ) or ( ante -> ( f1 /\\ f2 /\\ f3 ) )"""
    fs = [body(w, s, ante) for s in steps]
    if len(fs) == 2:
        return st(w, ante, steps, 'jca', '( %s /\\ %s )' % tuple(fs))
    return st(w, ante, steps, '3jca', '( %s /\\ %s /\\ %s )' % tuple(fs))


def _conj(a):
    from cl import _conjuncts
    return _conjuncts(a)


def parts(w, ante, top=None, step=None, out=None):
    """every conjunct (at any depth) of ANTE, as a dict formula -> step ( ante -> formula )"""
    if out is None:
        out = {}
    if top is None:
        top = ante
    ps = _conj(top)
    if ps is None:
        if step is not None:
            out.setdefault(top, step)
        return out
    if step is None:
        rules = {2: ['simpl', 'simpr'], 3: ['simp1', 'simp2', 'simp3']}[len(ps)]
    else:
        rules = {2: ['simpld', 'simprd'], 3: ['simp1d', 'simp2d', 'simp3d']}[len(ps)]
    if step is not None:
        out.setdefault(top, step)
    for p, r in zip(ps, rules):
        s = w.s([] if step is None else [step], r, '( %s -> %s )' % (ante, p))
        parts(w, ante, p, s, out)
    return out


def c2cl(w, ante):
    ip = w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')
    c = w.s([w.s([], '2cn', '2 e. CC'), ip], 'mulcli', '%s e. CC' % C2)
    return w.s([c], 'a1i', '( %s -> %s e. CC )' % (ante, C2))


def ctx(w, ante, leaves=None):
    """a Closure under ANTE knowing C2, _i, _pi"""
    lv = {C2: ('CC', c2cl(w, ante)), '_i': ('CC', a1(w, ante, 'ax-icn', '_i e. CC')),
          '_pi': ('RR+', a1(w, ante, 'pirp', '_pi e. RR+'))}
    if leaves:
        lv.update(leaves)
    return Closure(w, ante, lv)


def run(w):
    return w.run()


def fvmd(w, ante, v, dom, body_, a, memst, exs):
    """( ante -> ( ( v e. dom |-> body ) ` a ) = body[v:=a] ) by fvmptd; exs: ( ante -> body[v:=a] e. CC )"""
    eq = '%s = %s' % (v, a)
    idst = w.s([], 'id', '( %s -> %s )' % (eq, eq))
    s1, val = w.congr(body_, {v: a}, eq, {v: idst})
    mp = '( %s e. %s |-> %s )' % (v, dom, body_)
    sub = w.s([s1], 'adantl', '( ( %s /\\ %s ) -> %s = %s )' % (ante, eq, body_, val))
    return w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (ante, mp, mp)), sub, memst, exs], 'fvmptd', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, a, val))


def fvm2(w, ante, v, dom, body_, memst, clst):
    """( ante -> ( ( v e. dom |-> body ) ` v ) = body ) by fvmpt2, the argument being the binder itself"""
    mp = '( %s e. %s |-> %s )' % (v, dom, body_)
    e = w.s([], 'eqid', '%s = %s' % (mp, mp))
    return w.s([memst, clst, w.s([e], 'fvmpt2', '( ( %s e. %s /\\ %s e. CC ) -> ( %s ` %s ) = %s )' % (v, dom, body_, mp, v, body_))],
               'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (ante, mp, v, body_))


def ch(w, ante, steps, rel='='):
    """chain equalities a = b, b = c, ... by eqtrd"""
    cur = steps[0]
    for s in steps[1:]:
        l = body(w, cur, ante).split(' = ', 1)[0] if False else None
        cur = eqt(w, ante, cur, s)
    return cur


def _lhs_rhs(f):
    toks = f.split()
    parts = split_top(toks)
    # find top-level '=' token
    depth = 0
    for i, t in enumerate(toks):
        if t in ('(', '{', '<.'):
            depth += 1
        elif t in (')', '}', '>.'):
            depth -= 1
        elif depth == 0 and t in ('=', '<_', '<'):
            return ' '.join(toks[:i]), t, ' '.join(toks[i + 1:])
    raise ValueError(f)


def eqt(w, ante, s1, s2):
    a, _, b = _lhs_rhs(body(w, s1, ante))
    b2, _, c = _lhs_rhs(body(w, s2, ante))
    if b == b2:
        return st(w, ante, [s1, s2], 'eqtrd', '%s = %s' % (a, c))
    if a == b2:
        return st(w, ante, [s1, s2], 'eqtr3d', '%s = %s' % (b, c))
    if b == c:
        return st(w, ante, [s1, s2], 'eqtr4d', '%s = %s' % (a, b2))
    raise ValueError('cannot chain %s / %s' % (body(w, s1, ante), body(w, s2, ante)))


def eqc(w, ante, s):
    a, _, b = _lhs_rhs(body(w, s, ante))
    return st(w, ante, [s], 'eqcomd', '%s = %s' % (b, a))


def NFv(v): return '( %s e. RR |-> ( ( F ` %s ) x. ( * ` ( F ` %s ) ) ) )' % (v, v, v)
def DNFv(v): return '( %s e. RR |-> ( ( ( G ` %s ) x. ( * ` ( F ` %s ) ) ) + ( ( * ` ( G ` %s ) ) x. ( F ` %s ) ) ) )' % (v, v, v, v, v)


def fmap(w, ante, fst, F, v):
    """( ante -> ( v e. RR |-> ( F ` v ) ) e. CNR ) from fst: ( ante -> F e. CNR )"""
    ff = ap(w, ante, 'cncff', [fst], '%s : RR --> CC' % F)
    FM = '( %s e. RR |-> ( %s ` %s ) )' % (v, F, v)
    fm = st(w, ante, [ff], 'feqmptd', '%s = %s' % (F, FM))
    return st(w, ante, [fm, fst], 'eqeltrrd', '%s e. %s' % (FM, CNR))


def abscn(w, ante):
    """( ante -> abs e. ( CC -cn-> CC ) )"""
    s = w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC'), w.inst('cncfss')], 'mp2an', '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
    c = w.s([s, w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'sselii', 'abs e. ( CC -cn-> CC )')
    return w.s([c], 'a1i', '( %s -> abs e. ( CC -cn-> CC ) )' % ante)


def cnabs(w, ante, mst, X, v):
    """( ante -> ( v e. RR |-> ( abs ` X ) ) e. CNR ) from mst: ( ante -> ( v e. RR |-> X ) e. CNR )"""
    return st(w, ante, [abscn(w, ante), mst], 'cncfmpt1f', '( %s e. RR |-> ( abs ` %s ) ) e. %s' % (v, X, CNR))


def cnconst(w, ante, cst, C, v):
    """( ante -> ( v e. RR |-> C ) e. CNR ) from cst: ( ante -> C e. CC )"""
    return ap(w, ante, 'cncfmptc', [cst, a1(w, ante, 'ax-resscn', 'RR C_ CC'), a1(w, ante, 'ssid', 'CC C_ CC')],
              '( %s e. RR |-> %s ) e. %s' % (v, C, CNR))


def cnmul(w, ante, s1, X1, s2, X2, v):
    return st(w, ante, [s1, s2], 'mulcncf', '( %s e. RR |-> ( %s x. %s ) ) e. %s' % (v, X1, X2, CNR))


def cnadd(w, ante, s1, X1, s2, X2, v):
    return st(w, ante, [s1, s2], 'addcncf', '( %s e. RR |-> ( %s + %s ) ) e. %s' % (v, X1, X2, CNR))


def cnsq(w, ante, mst, X, v, xcl):
    """( ante -> ( v e. RR |-> ( ( abs ` X ) ^ 2 ) ) e. CNR ) from mst: ( v |-> X ) cn and
    xcl: ( ( ante /\\ v e. RR ) -> X e. CC )"""
    ab = cnabs(w, ante, mst, X, v)
    AX = '( abs ` %s )' % X
    m = cnmul(w, ante, ab, AX, ab, AX, v)
    Av = '( %s /\\ %s e. RR )' % (ante, v)
    sq = st(w, Av, [st(w, Av, [st(w, Av, [xcl], 'abscld', '%s e. RR' % AX)], 'recnd', '%s e. CC' % AX)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (AX, AX, AX))
    eq = st(w, ante, [sq], 'mpteq2dva', '( %s e. RR |-> ( %s ^ 2 ) ) = ( %s e. RR |-> ( %s x. %s ) )' % (v, AX, v, AX, AX))
    return st(w, ante, [eq, m], 'eqeltrd', '( %s e. RR |-> ( %s ^ 2 ) ) e. %s' % (v, AX, CNR))


def cnfg(w, ante, fm, gm, v):
    """( ante -> ( v e. RR |-> FG2(v) ) e. CNR ) from fm, gm: ( v |-> ( F ` v ) ), ( v |-> ( G ` v ) ) cn"""
    two = cnconst(w, ante, w.s([], '2cnd', '( %s -> 2 e. CC )' % ante), '2', v)
    af = cnabs(w, ante, fm, '( F ` %s )' % v, v); ag = cnabs(w, ante, gm, '( G ` %s )' % v, v)
    m1 = cnmul(w, ante, two, '2', af, '( abs ` ( F ` %s ) )' % v, v)
    return cnmul(w, ante, m1, '( 2 x. ( abs ` ( F ` %s ) ) )' % v, ag, '( abs ` ( G ` %s ) )' % v, v)


def ioore(w, ante, a, b, v='t'):
    """( ( ante /\\ v e. ( a (,) b ) ) -> v e. RR )"""
    Av = '( %s /\\ %s e. %s )' % (ante, v, IOO(a, b))
    return ap(w, Av, 'elioore', [w.s([], 'simpr', '( %s -> %s e. %s )' % (Av, v, IOO(a, b)))], '%s e. RR' % v)


def qedlast(w):
    last = w.lines.pop()
    name = last.split(':', 1)[0]
    w.lines.append('qed' + last[len(name):])


def concl(lab):
    return split_imp(STATEMENTS[lab])[1]


def qpos(w, ante, qr, q2, Q='Q'):
    """( ante -> 0 < Q ) from qr: Q e. RR, q2: 2 <_ Q"""
    return st(w, ante, [w.s([], '0red', '( %s -> 0 e. RR )' % ante), a1(w, ante, '2re', '2 e. RR'), qr,
                        a1(w, ante, '2pos', '0 < 2'), q2], 'ltletrd', '0 < %s' % Q)
