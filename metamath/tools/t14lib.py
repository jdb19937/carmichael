"""Sortie T14 helpers: the machine's main theorem, arithmetic half
(Overhead.lean's ExpB kit, the window facts of the natural scales ScTM,
MainProof.lean's searchBound_ExpB, exists_timeFun).

Statements live in STMTS14 (label -> text, or label -> (hyps, concl) for a
theorem with $e hypotheses); tools/gen/t14_freeze.py prints them, grammar
checks them and compares the database with them.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm import W, ROOT
from v5lib import mkst, Proj, lit
from lin import linarith, nlinarith
from cl import Closure, lift
import num

ONLY = [a for a in sys.argv[1:] if not a.startswith('-')]


def run(w):
    if ONLY and w.label not in ONLY:
        return True
    ok = w.run()
    assert ok, w.label
    return ok


def want(label):
    return (not ONLY) or label in ONLY


# ------------------------------------------------------------------ texts
def EXP(c, m):
    """exp ( c x. m )"""
    return '( exp ` ( %s x. %s ) )' % (c, m)


def XB(a, c, m='M'):
    """Lean's ExpB n c a with M = ell2 n ell3 n: a <_ exp ( c x. M )"""
    return '%s <_ %s' % (a, EXP(c, m))


def L2(n): return '( ell2 ` %s )' % n
def L3(n): return '( ell3 ` %s )' % n
def MM(n): return '( %s x. %s )' % (L2(n), L3(n))
def LOG(x): return '( log ` %s )' % x
def NL(x): return '( 2 Nlog %s )' % x


# the machine's scales (tools/t12lib.py SCA_ ... SCTH_, copied: t12lib imports the machine)
def SCA_(n): return '( 2 Nlog ( 2 Nlog %s ) )' % n
def SCB_(n): return '( 2 Nlog %s )' % SCA_(n)
def SCZ_(c, n): return '( ( %s x. %s ) x. %s )' % (c, SCA_(n), SCB_(n))
def BZ_(z): return '( ( 2 Nlog %s ) + 1 )' % z
def W99_(z): return '( 2 ^ ( |_ ` ( ( ( ; 9 9 x. %s ) + ; 9 9 ) / ; ; 1 0 0 ) ) )' % BZ_(z)
def YK_(z, k): return '( 2 ^ ( |_ ` ( ( ( ( ( %s - 1 ) x. %s ) + %s ) - 1 ) / %s ) ) )' % (k, BZ_(z), k, k)
def TH_(x): return '( 2 ^ ( |_ ` ( ( ( 6 x. ( ( 2 Nlog %s ) + 1 ) ) + 4 ) / 5 ) ) )' % x


def SC(c='C', k='K', n='N'): return '( ( %s ScTM %s ) ` %s )' % (c, k, n)
PZ = lambda s: '( 1st ` ( 1st ` ( 1st ` %s ) ) )' % s
PZ99 = lambda s: '( 2nd ` ( 1st ` ( 1st ` %s ) ) )' % s
PY = lambda s: '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % s
PT = lambda s: '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % s
PTH = lambda s: '( 2nd ` %s )' % s


def SE_(c='C', k='K', n='N'): return '( %s Search %s )' % (SC(c, k, n), n)


def SBS_(c='C', k='K', n='N'):
    s = SC(c, k, n)
    return '( ( 2 Nlog ( ( ( ( ( %s + %s ) + %s ) + %s ) + %s ) + %s ) ) + 2 )' % (PZ(s), PZ99(s), PY(s), PT(s), c, k)


def SBN_(c='C', k='K', n='N'):
    return '( ( 2 Nlog ( %s + %s ) ) + 1 )' % (n, PTH(SC(c, k, n)))


def SB1_(t, bs, bn): return '( ( ( ( 5 x. ( ( %s x. %s ) + 1 ) ) + %s ) + %s ) + 1 )' % (t, bs, bs, bn)
def SX_(t, p, b1): return '( ( ( ( ( ; ; 1 1 1 x. ( %s + 1 ) ) + ( ; 1 3 x. ( %s + 2 ) ) ) x. %s ) + ( 4 x. %s ) ) + ; ; 2 0 0 )' % (t, p, b1, t)


def SPOLY_(t, bs, bn):
    p2t = '( 2 ^ %s )' % t
    return ('( ; ; 3 0 0 x. ( ( ( ( 2 ^ ( ( %s x. %s ) + 1 ) ) ^ 2 ) x. ( %s + 2 ) ) x. ( TMB ` %s ) ) )'
            % (t, bs, p2t, SX_(t, p2t, SB1_(t, bs, bn))))


def SBOUND(c='C', k='K', n='N'):
    """tmisrch's step bound ( ( search.2 + 1 ) x. searchPoly ) (MainProof's searchBound)"""
    return '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (SE_(c, k, n), SPOLY_(PT(SC(c, k, n)), SBS_(c, k, n), SBN_(c, k, n)))


# ------------------------------------------------------------------ statements
STMTS14 = {}
ORDER14 = []


def reg(label, stmt, hyps=None):
    stmt = ' '.join(stmt.split())
    if hyps is None:
        STMTS14[label] = stmt
    else:
        STMTS14[label] = ([' '.join(h.split()) for h in hyps], stmt)
    if label not in ORDER14:
        ORDER14.append(label)
    return stmt


def ph(x): return '( ph -> %s )' % x


# --- (a) the ExpB kit, over a real M (Lean: ExpB n c a = a <_ exp ( c ell2 n ell3 n ), M = ell2 n ell3 n)
reg('xbmul', ph(XB('( A x. B )', 'F')),
    [ph(x) for x in ('M e. RR', '0 <_ M', 'C e. RR', 'D e. RR', 'F e. RR', '( C + D ) <_ F', 'A e. RR', '0 <_ A',
                     'B e. RR', '0 <_ B', XB('A', 'C'), XB('B', 'D'))])
reg('xbadd', ph(XB('( A + B )', 'F')),
    [ph(x) for x in ('M e. RR', '1 <_ M', 'C e. RR', 'D e. RR', 'G e. RR', 'F e. RR', 'C <_ G', 'D <_ G',
                     '( G + 1 ) <_ F', 'A e. RR', 'B e. RR', XB('A', 'C'), XB('B', 'D'))])
reg('xblin', ph(XB('A', 'C')),
    [ph(x) for x in ('M e. RR', 'C e. RR', 'A e. RR', '0 <_ ( C x. M )', 'A <_ ( C x. M )')])
reg('xblin2', ph(XB('A', '2')),
    [ph(x) for x in ('M e. RR', '1 <_ M', 'K e. RR', '0 <_ K', 'K <_ M', 'A e. RR', 'A <_ ( K x. M )')])
reg('xbcon', ph(XB('A', 'K')),
    [ph(x) for x in ('M e. RR', '1 <_ M', 'K e. RR', '0 <_ K', 'A e. RR', 'A <_ K')])
reg('xbpow', ph(XB('( A ^ N )', 'F')),
    [ph(x) for x in ('M e. RR', '0 <_ M', 'C e. RR', 'F e. RR', 'N e. NN0', '( N x. C ) <_ F', 'A e. RR', '0 <_ A',
                     XB('A', 'C'))])
reg('xbtmb', ph(XB('( TMB ` B )', 'F')),
    [ph(x) for x in ('M e. RR', '1 <_ M', 'C e. RR', '0 <_ C', 'F e. RR', '( ( 3 x. C ) + ; 1 1 ) <_ F', 'B e. NN0',
                     XB('B', 'C'))])
reg('xb2pow', ph(XB('( 2 ^ T )', 'C')),
    [ph(x) for x in ('M e. RR', 'C e. RR', 'T e. NN0', 'T <_ ( C x. M )')])

# --- (c) the window facts of the natural scales (ScalesTM.lean, Overhead.lean, MainProof.lean 57-70)
G2 = '( log ` 2 )'
reg('ln2ge23', '( 2 / 3 ) <_ ( log ` 2 )')
reg('nlogbr', '( X e. NN -> ( ( %s x. %s ) <_ %s /\\ %s < ( ( %s + 1 ) x. %s ) ) )'
    % (NL('X'), G2, LOG('X'), LOG('X'), NL('X'), G2))
reg('nlog2log', '( X e. NN -> %s <_ ( 2 x. %s ) )' % (NL('X'), LOG('X')))
reg('nloglay', '( ( X e. NN /\\ ( L e. RR /\\ D e. RR ) /\\ ( 3 <_ L /\\ L <_ %s /\\ %s <_ ( L + D ) ) ) -> '
    '( L <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( L + D ) ) ) )' % (LOG('X'), LOG('X'), NL('X'), NL('X')))
reg('ceildv', '( ( R e. ZZ /\\ Q e. NN ) -> ( ( ( R - Q ) + 1 ) <_ ( Q x. ( |_ ` ( R / Q ) ) ) /\\ '
    '( Q x. ( |_ ` ( R / Q ) ) ) <_ R ) )')
BX = '( %s + 1 )' % NL('X')
reg('p2sw', '( ( ( X e. NN /\\ E e. NN0 ) /\\ ( A e. RR /\\ 0 <_ A /\\ R e. RR ) /\\ '
    '( ( A x. %s ) <_ E /\\ E <_ ( ( A x. %s ) + R ) ) ) -> '
    '( ( X ^c A ) <_ ( 2 ^ E ) /\\ ( 2 ^ E ) <_ ( ( 2 ^c ( A + R ) ) x. ( X ^c A ) ) ) )' % (BX, BX))
C99 = '( ; 9 9 / ; ; 1 0 0 )'
reg('sctmw', '( Z e. NN -> ( ( Z ^c %s ) <_ %s /\\ %s <_ ( 4 x. ( Z ^c %s ) ) ) )' % (C99, W99_('Z'), W99_('Z'), C99))
AK = '( 1 - ( 1 / K ) )'
reg('sctmy', '( ( Z e. NN /\\ K e. NN ) -> ( ( Z ^c %s ) <_ %s /\\ %s <_ ( 4 x. ( Z ^c %s ) ) ) )'
    % (AK, YK_('Z', 'K'), YK_('Z', 'K'), AK))
C65 = '( 6 / 5 )'
reg('sctmth', '( X e. NN -> ( ( X ^c %s ) <_ %s /\\ %s <_ ( 4 x. ( X ^c %s ) ) ) )' % (C65, TH_('X'), TH_('X'), C65))
WN = lambda n: '( %s e. ( ZZ>= ` 3 ) /\\ ; ; 2 0 0 <_ %s /\\ 3 <_ %s )' % (n, L2(n), L3(n))
reg('sctmab', '( %s -> ( ( %s <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( %s + 0 ) ) ) /\\ '
    '( %s <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( %s + ( 1 / 2 ) ) ) ) /\\ '
    '( %s <_ %s /\\ %s <_ ( ( 3 / 2 ) x. ( %s + ( ; 5 1 / ; ; 1 0 0 ) ) ) ) ) )'
    % (WN('N'), LOG('N'), NL('N'), NL('N'), LOG('N'), L2('N'), SCA_('N'), SCA_('N'), L2('N'),
       L3('N'), SCB_('N'), SCB_('N'), L3('N')))


def WIN(c, k, n):
    """searchw's window antecedent at v := ( ( c ScTM k ) ` n ), E := 1 / k, with v e. Scales"""
    s = SC(c, k, n)
    return ('( %s e. Scales /\\ ( <. <. %s , ( 1 / %s ) >. , %s >. InWindow ( 1st ` %s ) /\\ '
            '( ( ( log ` %s ) ^c ( 6 / 5 ) ) <_ ( 2nd ` %s ) /\\ ( 2nd ` %s ) <_ ( ; 1 6 x. ( ( log ` %s ) ^c ( 6 / 5 ) ) ) ) ) )'
            % (s, c, k, n, s, n, s, s, n))


CK = '( ( C e. NN0 /\\ ; ; ; 1 0 0 0 <_ C ) /\\ K e. NN )'
reg('sctmwin', '( ( %s /\\ %s ) -> %s )' % (CK, WN('N'), WIN('C', 'K', 'N')))
reg('sctmwinev', '( %s -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s )' % (CK, WIN('C', 'K', 'n')))


# ------------------------------------------------------------------ worksheet helpers
from cl import formula_of, strip_ante


def fof(w, step, ante):
    return strip_ante(formula_of(w, step), ante)


def cj(w, ante, steps):
    """( ante -> ( P1 /\\ P2 ) ) or the 3-conjunction from the steps ( ante -> Pi )"""
    fs = [fof(w, s, ante) for s in steps]
    if len(steps) == 2:
        return w.s(steps, 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, fs[0], fs[1]))
    assert len(steps) == 3
    return w.s(steps, '3jca', '( %s -> ( %s /\\ %s /\\ %s ) )' % (ante, fs[0], fs[1], fs[2]))


def use(w, ante, lemma, parts, concl):
    """( ante -> concl ) from the closed lemma ( H -> concl ): parts is the nested
    list of steps building H (lists of 2 or 3 become jca / 3jca)"""
    def build(p):
        if isinstance(p, str):
            return p
        return cj(w, ante, [build(q) for q in p])
    h = build(parts)
    return w.s([h, w.inst(lemma)], 'syl', '( %s -> %s )' % (ante, concl))


def conjs(text):
    """the top-level conjuncts of ( A /\\ B ) or ( A /\\ B /\\ C )"""
    from cl import split_sep
    toks = text.split()
    assert toks[0] == '(' and toks[-1] == ')', text
    parts = split_sep(toks[1:-1], ('/\\',))
    return [p if isinstance(p, str) else ' '.join(p) for p in parts]


def proj(w, ante, step, i):
    """( ante -> Pi ) from ( ante -> ( P1 /\\ P2 [/\\ P3] ) )"""
    f = fof(w, step, ante)
    ps = conjs(f)
    lem = {2: ('simpld', 'simprd'), 3: ('simp1d', 'simp2d', 'simp3d')}[len(ps)][i]
    return w.s([step], lem, '( %s -> %s )' % (ante, ps[i]))


# --- (b) the step bound in the window (MainProof.lean: searchBound_ExpB) and the typing of the search cost
reg('srchcst', '( ( V e. Scales /\\ N e. NN0 ) -> ( 2nd ` ( V Search N ) ) e. NN0 )')
WN12 = lambda n: '( %s e. ( ZZ>= ` 3 ) /\\ ; ; 2 0 0 <_ %s /\\ ; 1 2 <_ %s )' % (n, L2(n), L3(n))
ACON = '( ( ( ; 3 7 x. C ) + K ) + 5 )'
COST = lambda n: '( 2nd ` %s ) <_ ( exp ` ( ( ; ; 1 0 0 x. %s ) x. %s ) )' % (SE_('C', 'K', n), L2(n), L3(n))
SBX = lambda n: '( %s + 1 ) <_ %s' % (SBOUND('C', 'K', n), EXP('; ; ; 2 0 0 0', MM(n)))
reg('sbexpb', '( ( %s /\\ %s /\\ ( ( log ` %s ) <_ %s /\\ %s ) ) -> %s )'
    % (CK, WN12('N'), ACON, L3('N'), COST('N'), SBX('N')))
reg('sbexpbev', '( ( %s /\\ E. m e. NN0 A. n e. ( ZZ>= ` m ) %s ) -> E. m e. NN0 A. n e. ( ZZ>= ` m ) '
    '( 1 <_ %s /\\ ; ; ; 2 4 0 0 <_ %s /\\ %s ) )'
    % (CK, COST('n'), L2('n'), MM('n'), SBX('n')))

# --- (d) the time function (Overhead.lean: exists_timeFun, exists_timeFun_of_ExpB)
def TF(g='G', c='C', m='M'):
    return ('( k e. NN0 |-> if ( ( %s + 3 ) <_ k , ( |_ ` ( exp ` ( ( %s x. ( log ` k ) ) x. ( log ` ( log ` k ) ) ) ) ) , '
            'sum_ j e. ( 0 ..^ ( 2 ^ k ) ) ( %s ` j ) ) )' % (m, c, g))


reg('tmfun', '( ( ( G : NN0 --> NN0 /\\ C e. RR+ /\\ M e. NN0 ) /\\ A. n e. ( ZZ>= ` M ) ( 1 <_ %s /\\ ( G ` n ) <_ %s ) ) -> '
    '( %s : NN0 --> NN0 /\\ A. n e. NN0 ( G ` n ) <_ ( %s ` ( # ` ( encodeNat ` n ) ) ) /\\ '
    'A. n e. ( ZZ>= ` ( M + 3 ) ) ( %s ` n ) <_ ( exp ` ( ( C x. ( log ` n ) ) x. ( log ` ( log ` n ) ) ) ) ) )'
    % (L2('n'), EXP('C', MM('n')), TF(), TF(), TF()))


def dbstmt(label):
    """the statement of LABEL from the assertion index (for texts read, never retyped)"""
    import re as _re
    idx = os.path.join(ROOT, 'scratch', 'assertions-t14.idx')
    with open(idx) as f:
        for l in f:
            if l.startswith(label + ' '):
                return l.split(' |- ', 1)[1].strip()
    raise KeyError(label)


def ante_of(stmt):
    from cl import split_imp
    a, b = split_imp(stmt)
    return a, b


LET13, _SV13 = ante_of(dbstmt('t13srcv'))
reg('srchcstl', '( %s -> ( 2nd ` ( V\' Search N ) ) e. NN0 )' % LET13)
# srchcstl precedes srchcst in the file
ORDER14.remove('srchcstl'); ORDER14.insert(ORDER14.index('srchcst'), 'srchcstl')


# --- (e) the algorithmic main theorem at the machine's natural parameters (for T15: carmsw is stated at the
#         real-parameter scales ( c ScalesOf t ); the machine runs at ( ( C ScTM K ) ` n ) )
def _sw():
    import a5lib
    s = a5lib.dbstmt('searchw')
    a, b = ante_of(s)
    assert a == 'ph'
    pre = 'E. m e. NN0 A. n e. ( ZZ>= ` m ) A. v e. Scales '
    assert b.startswith(pre)
    body = b[len(pre):]
    wv, r3 = ante_of(body)
    return wv, r3


SW_WV, SW_R3 = _sw()                     # searchw's window antecedent and its three-part consequent (at v, n, C, E, A)


def R3AT(c, k, n, a):
    from tm import sub
    return sub(SW_R3, {'v': SC(c, k, n), 'C': c, 'E': '( 1 / %s )' % k, 'A': a, 'n': n})


def SUCC(c, k, n, e):
    ps = conjs(R3AT(c, k, n, e))
    assert len(ps) == 3
    return '( %s /\\ %s )' % (ps[0], ps[1])


def CARMSWN_BODY(c, k):
    return ('( ( ; ; ; 1 0 0 0 <_ %s /\\ 2 <_ %s ) /\\ ( E. m e. NN0 A. n e. ( ZZ>= ` m ) %s /\\ '
            'A. e e. RR ( 0 < e -> E. m e. NN0 A. n e. ( ZZ>= ` m ) %s ) ) )'
            % (c, k, COST('n').replace('( ( C ScTM K )', '( ( %s ScTM %s )' % (c, k)), SUCC(c, k, 'n', 'e')))


def _carmsw_hyps():
    import a5lib
    return a5lib.dbhyps('carmsw')


reg('carmswn', '( ph -> E. c e. NN0 E. k e. NN %s )' % CARMSWN_BODY('c', 'k'), _carmsw_hyps())


# --- the small-input boundary (for T15's route beta): from n >= 16 on the scales are a tuple of Scales with 1 <_ z
reg('sctm16', '( ( ( C e. NN0 /\\ 1 <_ C ) /\\ K e. NN /\\ N e. ( ZZ>= ` ; 1 6 ) ) -> ( %s e. Scales /\\ 1 <_ %s ) )'
    % (SC(), PZ(SC())))
ORDER14.remove('sctm16'); ORDER14.insert(ORDER14.index('sctmwinev') + 1, 'sctm16')


# --- the full type of the search value and of its getD (for T15's f : NN0 --> ( NN0 X. Word NN0 ))
DJT14 = '( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )'
reg('srchtypl', '( %s -> ( V\' Search N ) e. %s )' % (LET13, DJT14))
reg('srchtyp', '( ( V e. Scales /\\ N e. NN0 ) -> ( V Search N ) e. %s )' % DJT14)
GETDV = 'if ( ( 1st ` ( V Search N ) ) = ( inr ` (/) ) , <. 0 , (/) >. , ( 2nd ` ( 1st ` ( V Search N ) ) ) )'
reg('srchgetd', '( ( V e. Scales /\\ N e. NN0 ) -> %s e. ( NN0 X. Word NN0 ) )' % GETDV)
for _l in ('srchtypl', 'srchtyp', 'srchgetd'):
    ORDER14.remove(_l)
_i = ORDER14.index('srchcst') + 1
ORDER14[_i:_i] = ['srchtypl', 'srchtyp', 'srchgetd']
