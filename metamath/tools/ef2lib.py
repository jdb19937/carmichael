"""Sortie EF2: helpers and the frozen statements (ExplicitFormula 1584-2711: DiskData on squares,
the disk zeros, the Landau expansion, exists_good_height, the rectangle residues, rectInt_strip).
Built on tools/zc1lib.py.

    python3 tools/ef2lib.py print                                   # the frozen table
    MM_DB=sorties/ef2.mm python3 tools/ef2lib.py check [LABEL...]   # grammar check (mmatch)
"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'gen'))
sys.path.insert(0, HERE)
from zc1lib import *
import zc1lib as _zc1
import c10lib as _c10


def stmt(label):
    """the assertion of LABEL from sorties/ef2.mm or carmichael.mm, without |-"""
    for fn in ('sorties/ef2.mm', 'carmichael.mm'):
        txt = open(os.path.join(HERE, '..', fn)).read()
        m = re.search(r'\s%s \$[pa] \|- (.*?) \$[=.]' % re.escape(label), txt, re.S)
        if m:
            return ' '.join(m.group(1).split())
    raise KeyError(label)


def patch(*mods):
    for m in mods:
        m.stmt = stmt


patch(_c10, _zc1)

# ---- objects -----------------------------------------------------------------------
KNUM = '; ; ; ; ; ; ; 1 7 5 0 0 0 0 0'          # Landau 17500000 (lndk)
KGH = '; ; ; ; ; ; ; 2 1 0 0 0 0 0 0'           # good-height log-derivative 21000000 (Lean 10^6)
GAP = '; ; ; 4 0 0 0'                           # good-height gap 1 / ( 4000 log ) (Lean 2000)
TPI = '( 2 x. ( _i x. _pi ) )'


def XA(t='T', A='A'):
    """Lean's scale X = A ( abs t + 2 )"""
    return '( %s x. ( ( abs ` %s ) + 2 ) )' % (A, t)


def DD(F='F', A='A'):
    """DiskData f A on squares: holomorphic on HP0, 1 <_ A, centre bound 1/4 and the bound 25 A ( abs t + 2 )
    on RCT(t) for every real t, no zeros on Re > 1.  Bound letters t x w."""
    return ('( %s /\\ ( %s e. RR /\\ 1 <_ %s ) /\\ ( A. t e. RR ( ( 1 / 4 ) <_ ( abs ` ( %s ` %s ) ) /\\ '
            'A. x e. %s ( abs ` ( %s ` x ) ) <_ ( ; 2 5 x. %s ) ) /\\ A. w e. %s ( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 ) ) )') % (
        HOLF(F, HP0), A, A, F, CT('t'), RCT('t'), F, XA('t', A), HP0, F)


def LHSF(F, t, S_='S'):
    Z = ZS(F, t)
    return '( abs ` ( ( ( ( CC _D %s ) ` %s ) / ( %s ` %s ) ) - sum_ q e. %s ( ( %s holord q ) / ( %s - q ) ) ) )' % (F, S_, F, S_, Z, F, S_)


def LDI(F='F', Y='Y'):
    """the strip integrand ( F' / F ) ( u ) Y ^ u / u on the zero-free part of HP0"""
    return '( u e. { v e. %s | ( %s ` v ) =/= 0 } |-> ( ( ( ( CC _D %s ) ` u ) / ( %s ` u ) ) x. ( ( %s ^c u ) / u ) ) )' % (HP0, F, F, F, Y)


PKF = lambda Y='Y': '( o e. ( CC \\ { 0 } ) |-> ( ( %s ^c o ) / o ) )' % Y


def KP(P='P', D=None, Y='Y'):
    """PKF ( z ) / ( z - P ) as a mapping on D (default: the punctured rectangle is supplied by the caller)"""
    return '( z e. %s |-> ( ( %s ` z ) / ( z - %s ) ) )' % (D, PKF(Y), P)


def INS(p, A, B):
    """p strictly inside the rectangle A crect B (Re and Im strictly between)"""
    return ('( ( ( Re ` %s ) < ( Re ` %s ) /\\ ( Re ` %s ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` %s ) /\\ ( Im ` %s ) < ( Im ` %s ) ) )'
            % (A, p, p, B, A, p, p, B))


def SIN(p, S_='S', C='C', L='L', H='H'):
    """p strictly inside the strip rectangle [S, C] x [L, H]"""
    return '( ( %s < ( Re ` %s ) /\\ ( Re ` %s ) < %s ) /\\ ( %s < ( Im ` %s ) /\\ ( Im ` %s ) < %s ) )' % (S_, p, p, C, L, p, p, H)


SA_, SB_ = '( S + ( _i x. L ) )', '( C + ( _i x. H ) )'
TAU = '( ( L + H ) / 2 )'
ZI = '{ p e. %s | %s }' % (ZS('F', TAU), SIN('p'))
LT4 = '( log ` ( A x. ( T + 4 ) ) )'

# ---- frozen statements ---------------------------------------------------------------
S = {}
DT = '( %s /\\ T e. RR )' % DD()
Z13 = ZS('F', 'T')
S['ef2x2'] = '( %s -> 2 <_ %s )' % (DT, XA())
S['ef2cnz'] = '( %s -> ( F ` %s ) =/= 0 )' % (DT, CT('T'))
S['ef2zs'] = '( %s -> ( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN /\\ %s <_ ( ; ; 8 0 0 x. ( log ` %s ) ) ) )' % (
    DT, Z13, Z13, MASS(Z13, 'F'), XA())
S['ef2zss'] = '( ( %s /\\ G C_ %s ) -> %s <_ ( ; ; 8 0 0 x. ( log ` %s ) ) )' % (DT, Z13, MASS('G', 'F'), XA())
S['ef2reb'] = ('( ( T e. RR /\\ P e. %s ) -> ( ( 3 / 8 ) <_ ( Re ` P ) /\\ ( Re ` P ) <_ ( ; 2 9 / 8 ) /\\ '
               '( abs ` ( ( Im ` P ) - T ) ) <_ ( ; 1 3 / 8 ) ) )') % Z13
SDF = '( S e. CC /\\ ( abs ` ( S - %s ) ) <_ ( 3 / 2 ) /\\ ( F ` S ) =/= 0 )' % CT('T')
S['ef2lnd'] = '( ( %s /\\ %s ) -> %s <_ ( %s x. ( log ` %s ) ) )' % (DT, SDF, LHSF('F', 'T'), KNUM, XA())
S['ef2ddl'] = '( %s -> %s )' % (CHI, DD(LFN, 'N'))
S['ef2dde'] = DD(ETA, '1')
S['ef2ddg'] = DD(GF, '1')
SV = '( v + ( _i x. u ) )'
S['ef2gh'] = ('( ( ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) /\\ ( G e. Fin /\\ G C_ RR /\\ ( # ` G ) <_ ( ; 1 6 x. %s ) ) ) -> '
              'E. u e. ( T [,] ( T + 1 ) ) ( A. g e. G ( 1 / ( %s x. %s ) ) <_ ( abs ` ( u - g ) ) /\\ '
              'A. v e. ( ( 1 / 2 ) [,] 3 ) ( ( F ` %s ) =/= 0 /\\ ( abs ` ( ( ( CC _D F ) ` %s ) / ( F ` %s ) ) ) <_ ( %s x. ( %s ^ 2 ) ) ) ) )') % (
    DD(), LT4, GAP, LT4, SV, SV, SV, KGH, LT4)
S['ef2dvh'] = '( %s -> %s )' % (HOLF('F', 'D'), HOLF('( CC _D F )', 'D'))
S['ef2pole'] = ('( ( Y e. RR+ /\\ ( ( A e. CC /\\ B e. CC ) /\\ 0 < ( Re ` A ) ) /\\ ( P e. CC /\\ %s ) ) -> '
                '( %s rectint <. A , B >. ) = ( %s x. ( ( Y ^c P ) / P ) ) )') % (INS('P', 'A', 'B'), KP('P', '( ( A crect B ) \\ { P } )'), TPI)
S['ef2nopole'] = ('( ( Y e. RR+ /\\ ( ( A e. CC /\\ B e. CC ) /\\ ( 0 < ( Re ` A ) /\\ ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) ) /\\ '
                  '( P e. CC /\\ -. P e. ( A crect B ) ) ) -> ( %s rectint <. A , B >. ) = 0 )') % KP('P', '( ( CC \\ { 0 } ) \\ { P } )')
SH = ('( ( Y e. RR /\\ 1 < Y ) /\\ ( ( S e. RR /\\ C e. RR ) /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S < C /\\ C <_ ( 5 / 4 ) ) ) /\\ '
      '( ( L e. RR /\\ H e. RR ) /\\ ( L < H /\\ ( H - L ) <_ 1 ) ) )')
FRH = 'A. p e. ( %s crect %s ) ( ( F ` p ) = 0 -> %s )' % (SA_, SB_, SIN('p'))
S['ef2strip'] = '( ( %s /\\ %s /\\ %s ) -> ( %s rectint <. %s , %s >. ) = ( %s x. sum_ q e. %s ( ( F holord q ) x. ( ( Y ^c q ) / q ) ) ) )' % (
    DD(), SH, FRH, LDI(), SA_, SB_, TPI, ZI)

ORDER = list(S)


def check(labels):
    d = os.path.join(HERE, '..', 'scratch', 'ef2gc')
    os.makedirs(d, exist_ok=True)
    bad = 0
    for lab in labels:
        p = os.path.join(d, 'ef2gc%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=ef2gc%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            f.write('h1::ef2gc%s.1 |- %s\n' % (lab, S[lab]))
            f.write('qed:1:idi |- %s\n$)\n' % S[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, os.path.join(HERE, 'mm.py'), 'unify', p], cwd=os.path.join(HERE, '..'),
                           capture_output=True, text=True, env=env)
        out = r.stdout + r.stderr
        ok = r.returncode == 0 and 'rror' not in out
        if not ok:
            bad += 1
            print('GRAMMAR FAIL', lab, out[-600:])
    print('grammar checked %d, failures %d' % (len(labels), bad))


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in ORDER:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    elif 'check' in sys.argv:
        check([a for a in sys.argv[2:]] or ORDER)


# ---- worksheet helpers -----------------------------------------------------------------
def dd_parts(w, A0, dd, F='F', A='A'):
    """from dd : ( A0 -> DD(F, A) ): steps hol, ar ( A e. RR ), a1 ( 1 <_ A ), allt, nz"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    P1, P2, P3 = top_and(DD(F, A))
    hol = s([dd, w.inst('simp1')], 'syl', P1)
    p2 = s([dd, w.inst('simp2')], 'syl', P2)
    p3 = s([dd, w.inst('simp3')], 'syl', P3)
    ar = s([p2, w.inst('simpl')], 'syl', '%s e. RR' % A)
    a1 = s([p2, w.inst('simpr')], 'syl', '1 <_ %s' % A)
    Q1, Q2 = top_and(P3)
    allt = s([p3, w.inst('simpl')], 'syl', Q1)
    nz = s([p3, w.inst('simpr')], 'syl', Q2)
    return hol, ar, a1, allt, nz


def DDT(t, F='F', A='A'):
    """the body of the t-quantifier of DD at the point t"""
    return '( ( 1 / 4 ) <_ ( abs ` ( %s ` %s ) ) /\\ A. x e. %s ( abs ` ( %s ` x ) ) <_ ( ; 2 5 x. %s ) )' % (
        F, CT(t), RCT(t), F, XA(t, A))


def dd_at(w, A0, allt, T, tr, F='F', A='A'):
    """( A0 -> DDT(T) ) from allt and tr : ( A0 -> T e. RR ); returns (low, bd)"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    eq, _ = w.wcongr(DDT('t', F, A), {'t': T}, 't = %s' % T, {'t': w.s([], 'id', '( t = %s -> t = %s )' % (T, T))})
    body = s([eq, allt, tr], 'rspcdva', DDT(T, F, A))
    lo, bd = top_and(DDT(T, F, A))
    return s([body, w.inst('simpl')], 'syl', lo), s([body, w.inst('simpr')], 'syl', bd)


def xr_of(w, A0, le, a, b, side):
    """( A0 -> a e. RR* ) (side 0) or ( A0 -> b e. RR* ) (side 1) from le : ( A0 -> a <_ b )"""
    lx = w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')
    brl = w.s([lx], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (a, b, a, b))
    both = w.s([le, brl], 'syl', '( %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (A0, a, b))
    return w.s([both, w.inst('simpl' if side == 0 else 'simpr')], 'syl', '( %s -> %s e. RR* )' % (A0, (a, b)[side]))


def le_tr(w, A0, le1, a, b, le2, c, name=None):
    """( A0 -> a <_ c ) from a <_ b and b <_ c, extended reals read off the hypotheses"""
    h = [xr_of(w, A0, le1, a, b, 0), xr_of(w, A0, le1, a, b, 1), xr_of(w, A0, le2, b, c, 1), le1, le2]
    if name == 'qed':
        return w.qed(h, 'xrletrd', '( %s -> %s <_ %s )' % (A0, a, c))
    return w.s(h, 'xrletrd', '( %s -> %s <_ %s )' % (A0, a, c))


def crect_bounds(w, A0, ast, bst, ust, A, B, U):
    """from ( A0 -> A e. CC ), ( A0 -> B e. CC ), ( A0 -> U e. ( A crect B ) ): dict
    'le': [Re A <_ Re U, Re U <_ Re B, Im A <_ Im U, Im U <_ Im B], 'cl': closures of the six parts, 'cc': U e. CC"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ec = s([ast, bst, w.inst('elcrect')], 'syl2anc', '( %s e. ( %s crect %s ) <-> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )' % (U, A, B, U, U, A, B, U, A, B))
    ins = s([ust, ec], 'mpbid', '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (U, U, A, B, U, A, B))
    uc = s([ins, w.inst('simp1')], 'syl', '%s e. CC' % U)
    cl = {}
    for x, st in ((A, ast), (B, bst), (U, uc)):
        cl['( Re ` %s )' % x] = s([st], 'recld', '( Re ` %s ) e. RR' % x)
        cl['( Im ` %s )' % x] = s([st], 'imcld', '( Im ` %s ) e. RR' % x)
    le = []
    for part, k in (('Re', 'simp2'), ('Im', 'simp3')):
        mem = s([ins, w.inst(k)], 'syl', '( %s ` %s ) e. ( ( %s ` %s ) [,] ( %s ` %s ) )' % (part, U, part, A, part, B))
        e2 = s([cl['( %s ` %s )' % (part, A)], cl['( %s ` %s )' % (part, B)], w.inst('elicc2')], 'syl2anc',
               '( ( %s ` %s ) e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( ( %s ` %s ) e. RR /\\ ( %s ` %s ) <_ ( %s ` %s ) /\\ ( %s ` %s ) <_ ( %s ` %s ) ) )'
               % (part, U, part, A, part, B, part, U, part, A, part, U, part, U, part, B))
        tri = s([mem, e2], 'mpbid', '( ( %s ` %s ) e. RR /\\ ( %s ` %s ) <_ ( %s ` %s ) /\\ ( %s ` %s ) <_ ( %s ` %s ) )' % (part, U, part, A, part, U, part, U, part, B))
        le.append(s([tri, w.inst('simp2')], 'syl', '( %s ` %s ) <_ ( %s ` %s )' % (part, A, part, U)))
        le.append(s([tri, w.inst('simp3')], 'syl', '( %s ` %s ) <_ ( %s ` %s )' % (part, U, part, B)))
    return {'le': le, 'cl': cl, 'cc': uc}


def ct_facts(w, A0, t, tr):
    """( A0 -> CT(t) e. CC ), ( A0 -> ( Re ` CT(t) ) = 2 ), ( A0 -> ( Im ` CT(t) ) = t ) from tr : ( A0 -> t e. RR )"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    C = CT(t)
    two = s([w.s([], '2re', '2 e. RR')], 'a1i', '2 e. RR')
    cc = s([s([], '2cnd', '2 e. CC'), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([tr], 'recnd', '%s e. CC' % t)], 'mulcld', '( _i x. %s ) e. CC' % t)],
           'addcld', '%s e. CC' % C)
    re_ = s([two, tr], 'crred', '( Re ` %s ) = 2' % C)
    im_ = s([two, tr], 'crimd', '( Im ` %s ) = %s' % (C, t))
    return cc, re_, im_


def sq_data(w, A0, t, tr, r=R138):
    """corner facts of SQ(CT(t), r): dict a, b (e. CC), eqs (lin hypotheses), lv (leaves -> closure steps)"""
    from c8_n import sqparts, sqre_at, sqcc
    from c8_o import numst
    s = lambda h, rf, f: w.s(h, rf, '( %s -> %s )' % (A0, f))
    C = CT(t)
    cc, re_, im_ = ct_facts(w, A0, t, tr)
    rr = numst(w, A0, r, 'RR')
    ps = sqparts(w, A0, sqre_at(w, A0, cc, rr, c=C, r=r), c=C, r=r)
    a, b = sqcc(w, A0, cc, rr, c=C, r=r)
    A, B = SQA(C, r), SQB(C, r)
    lv = {} if t.startswith('(') else {t: tr}
    for x, st in ((A, a), (B, b), (C, cc)):
        lv['( Re ` %s )' % x] = s([st], 'recld', '( Re ` %s ) e. RR' % x)
        lv['( Im ` %s )' % x] = s([st], 'imcld', '( Im ` %s ) e. RR' % x)
    return {'a': a, 'b': b, 'A': A, 'B': B, 'eqs': ps + [re_, im_], 'lv': lv}


def zs_unpack(w, A0, F, t, tr, q, qin):
    """from qin : ( A0 -> q e. ZS(F, t) ): dict cc, fz ( F q = 0 ), hy (lin facts incl. corner eqs), lv"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    d = sq_data(w, A0, t, tr)
    Z = ZS(F, t)
    sq = SQ(CT(t), R138)
    e1 = w.s([w.s([], 'fveq2', '( r = %s -> ( %s ` r ) = ( %s ` %s ) )' % (q, F, F, q))], 'eqeq1d', '( r = %s -> ( ( %s ` r ) = 0 <-> ( %s ` %s ) = 0 ) )' % (q, F, F, q))
    el = w.s([e1], 'elrab', '( %s e. %s <-> ( %s e. %s /\\ ( %s ` %s ) = 0 ) )' % (q, Z, q, sq, F, q))
    both = s([qin, el], 'sylib', '( %s e. %s /\\ ( %s ` %s ) = 0 )' % (q, sq, F, q))
    qsq = s([both, w.inst('simpl')], 'syl', '%s e. %s' % (q, sq))
    fz = s([both, w.inst('simpr')], 'syl', '( %s ` %s ) = 0' % (F, q))
    bnd = crect_bounds(w, A0, d['a'], d['b'], qsq, d['A'], d['B'], q)
    lv = dict(d['lv']); lv.update(bnd['cl'])
    return {'cc': bnd['cc'], 'fz': fz, 'hy': d['eqs'] + bnd['le'], 'lv': lv, 'sq': qsq}


def zs_mem(w, A0, F, t, tr, q, qcc, hy, lv, fz):
    """( A0 -> q e. ZS(F, t) ) from q e. CC, lin facts hy (bounds of Re q, Im q in terms of t) and fz : F q = 0"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    d = sq_data(w, A0, t, tr)
    lv = dict(lv); lv.update(d['lv'])
    for p in ('Re', 'Im'):
        k = '( %s ` %s )' % (p, q)
        if k not in lv:
            lv[k] = s([qcc], 'recld' if p == 'Re' else 'imcld', '%s e. RR' % k)
    hy = hy + d['eqs']
    A, B = d['A'], d['B']
    parts = []
    for p in ('Re', 'Im'):
        k = '( %s ` %s )' % (p, q)
        lo = lin8(w, A0, hy, '( %s ` %s ) <_ %s' % (p, A, k), lv)
        hi = lin8(w, A0, hy, '%s <_ ( %s ` %s )' % (k, p, B), lv)
        e2 = s([lv['( %s ` %s )' % (p, A)], lv['( %s ` %s )' % (p, B)], w.inst('elicc2')], 'syl2anc',
               '( %s e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( %s e. RR /\\ ( %s ` %s ) <_ %s /\\ %s <_ ( %s ` %s ) ) )' % (k, p, A, p, B, k, p, A, k, k, p, B))
        parts.append(s([s([lv[k], lo, hi], '3jca', '( %s e. RR /\\ ( %s ` %s ) <_ %s /\\ %s <_ ( %s ` %s ) )' % (k, p, A, k, k, p, B)), e2], 'mpbird',
                       '%s e. ( ( %s ` %s ) [,] ( %s ` %s ) )' % (k, p, A, p, B)))
    tri = '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (q, q, A, B, q, A, B)
    ec = s([d['a'], d['b'], w.inst('elcrect')], 'syl2anc', '( %s e. ( %s crect %s ) <-> %s )' % (q, A, B, tri))
    qsq = s([s([qcc, parts[0], parts[1]], '3jca', tri), ec], 'mpbird', '%s e. ( %s crect %s )' % (q, A, B))
    e1 = w.s([w.s([], 'fveq2', '( r = %s -> ( %s ` r ) = ( %s ` %s ) )' % (q, F, F, q))], 'eqeq1d', '( r = %s -> ( ( %s ` r ) = 0 <-> ( %s ` %s ) = 0 ) )' % (q, F, F, q))
    return s([e1, qsq, fz], 'elrabd', '%s e. %s' % (q, ZS(F, t)))


def conj(w, C, f, have):
    """( C -> f ) for a conjunction tree f whose leaves are keys of have (formula -> step proving ( C -> leaf ))"""
    f = ' '.join(f.split())
    if f in have:
        return have[f]
    parts = top_and(f)
    if len(parts) == 1:
        raise KeyError('no step for leaf: ' + f)
    steps = [conj(w, C, p, have) for p in parts]
    return w.s(steps, 'jca' if len(parts) == 2 else '3jca', '( %s -> %s )' % (C, f))


def up(w, st, C):
    """lift ( C0 -> f ) to ( C -> f ) where C = ( C0 /\\ x ) or ( ( C0 /\\ x ) /\\ y ) ...: one adantr per level"""
    f = [l for l in w.lines if l.startswith(st + ':')][0].split(' |- ', 1)[1]
    a, body = ante_of(f)
    cur, levels = C, []
    while cur != a:
        parts = top_and(cur)
        if len(parts) != 2:
            raise ValueError('context %s is not an extension of %s' % (C, a))
        levels.append(cur)
        cur = parts[0]
    for ctx in reversed(levels):
        st = w.s([st], 'adantr', '( %s -> %s )' % (ctx, body))
    return st


def body_of(w, st):
    f = [l for l in w.lines if l.startswith(st + ':')][0].split(' |- ', 1)[1]
    return ante_of(f)[1]


def crect_in(w, C, A, B, ast, bst, U, ucc, hy, lv):
    """( C -> U e. ( A crect B ) ) from U e. CC and lin facts hy (leaves lv) giving the four bounds"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    lv = dict(lv)
    for x, st in ((A, ast), (B, bst), (U, ucc)):
        for p in ('Re', 'Im'):
            k = '( %s ` %s )' % (p, x)
            if k not in lv:
                lv[k] = s([st], 'recld' if p == 'Re' else 'imcld', '%s e. RR' % k)
    parts = []
    for p in ('Re', 'Im'):
        k = '( %s ` %s )' % (p, U)
        lo = lin8(w, C, hy, '( %s ` %s ) <_ %s' % (p, A, k), lv)
        hi = lin8(w, C, hy, '%s <_ ( %s ` %s )' % (k, p, B), lv)
        e2 = s([lv['( %s ` %s )' % (p, A)], lv['( %s ` %s )' % (p, B)], w.inst('elicc2')], 'syl2anc',
               '( %s e. ( ( %s ` %s ) [,] ( %s ` %s ) ) <-> ( %s e. RR /\\ ( %s ` %s ) <_ %s /\\ %s <_ ( %s ` %s ) ) )' % (k, p, A, p, B, k, p, A, k, k, p, B))
        parts.append(s([s([lv[k], lo, hi], '3jca', '( %s e. RR /\\ ( %s ` %s ) <_ %s /\\ %s <_ ( %s ` %s ) )' % (k, p, A, k, k, p, B)), e2], 'mpbird',
                       '%s e. ( ( %s ` %s ) [,] ( %s ` %s ) )' % (k, p, A, p, B)))
    tri = '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )' % (U, U, A, B, U, A, B)
    ec = s([ast, bst, w.inst('elcrect')], 'syl2anc', '( %s e. ( %s crect %s ) <-> %s )' % (U, A, B, tri))
    return s([s([ucc, parts[0], parts[1]], '3jca', tri), ec], 'mpbird', '%s e. ( %s crect %s )' % (U, A, B))


def BL(P='P', R='( E / 4 )'):
    return '( %s ( ball ` ( abs o. - ) ) %s )' % (P, R)
