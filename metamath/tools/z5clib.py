"""Sortie Z5c helpers (Route Z: Detector.lean Lemmas 3.1 and 3.4).

STATEMENTS / HYPS are the frozen statements of Z5c-blueprint.md, one place,
so that the blueprint, the grammar check and the generators cannot drift apart.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5blib import *          # PF, FMP, SQF, PSI, DV, HAB0, W, mkst, sy, lift, ...
from c0lib import hyp

# ---- the objects of Detector.lean 576-1276 (campaign conventions)
QS = lambda D, R: '{ q e. Prime | ( q || %s /\\ -. q || %s ) }' % (R, D)     # (tOf D R).primeFactors
QSU = lambda D, R: '{ u e. Prime | ( u || %s /\\ -. u || %s ) }' % (R, D)    # the same set, letter u (sqfprod's $d)
TT = lambda D, R: 'prod_ w e. %s w' % QSU(D, R)                             # tOf D R (letters w u: free of the engine's $d)
GK = lambda T, e: 'if ( %s || %s , prod_ p e. %s ( %s - 1 ) , 0 )' % (e, T, PF(e), FMP('p'))   # Gker T e
EF = lambda p, S='S': '( 1 + ( ( ( %s - 1 ) x. ( C ` %s ) ) x. ( %s ^c -u %s ) ) )' % (FMP(p), p, p, S)  # Euler factor
EU = lambda Q, S='S': 'prod_ p e. %s %s' % (Q, EF('p', S))                   # eulerT over the prime set Q
MUL = lambda G: 'A. i e. NN A. j e. NN ( %s ` ( i x. j ) ) = ( ( %s ` i ) x. ( %s ` j ) )' % (G, G, G)
CHR = '( C : NN --> CC /\\ ( C ` 1 ) = 1 /\\ %s )' % MUL('C')                  # a completely multiplicative C, C(1) = 1
CB = 'A. j e. NN ( abs ` ( C ` j ) ) <_ 1'                                    # chi.norm_le_one
LS = lambda S='S': 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u %s ) )' % S         # L ( s , chi ) on Re s > 1
MRT = lambda d, R='R', S='S': ('( ( ( ( ( ( A bvLam B ) ` %s ) x. %s ) x. ( C ` %s ) ) x. ( %s ^c -u %s ) ) x. %s )'
                               % (d, FMP('( %s gcd %s )' % (R, d)), d, d, S, EU(QS(d, R), S)))
MR = lambda S='S', R='R': '( ( <. A , B >. Mr <. C , %s >. ) ` %s )' % (R, S)
SRE1 = '( S e. CC /\\ 1 < ( Re ` S ) )'
SRE0 = '( S e. CC /\\ 0 <_ ( Re ` S ) )'
CV = lambda n: '( sum_ d e. %s ( ( A ` d ) x. ( B ` ( %s / d ) ) ) x. ( %s ^c -u Z ) )' % (DV(n), n, n)
LT = lambda n: '( ( ( ( ( A bvA B ) ` %s ) x. %s ) x. ( C ` %s ) ) x. ( %s ^c -u S ) )' % (n, PSI('R', n), n, n)
CPS = lambda T, n: '( ( ( C ` %s ) x. %s ) x. ( %s ^c -u S ) )' % (n, PSI(T, n), n)
SB = lambda D, n: '( if ( %s || %s , ( ( C ` %s ) x. %s ) , 0 ) x. ( %s ^c -u S ) )' % (D, n, n, PSI(TT(D, 'R'), '( %s / %s )' % (n, D)), n)
CFN = '( C : NN --> CC /\\ %s )' % CB
MR1 = lambda R='R': MR('1', R)

STATEMENTS = {
    # section T: tOf and the gcd splitting (Detector.lean 583-652)
    'z5tofsq': '( R e. NN -> ( ( %s e. NN /\\ ( mmu ` %s ) =/= 0 ) /\\ %s = %s ) )' % (TT('D', 'R'), TT('D', 'R'), PF(TT('D', 'R')), QS('D', 'R')),
    'z5tofcop': '( ( R e. NN /\\ D e. NN ) -> ( D gcd %s ) = 1 )' % TT('D', 'R'),
    'z5gcdcop': '( ( R e. NN /\\ ( D e. NN /\\ M e. NN ) ) -> ( ( R gcd D ) gcd ( %s gcd M ) ) = 1 )' % TT('D', 'R'),
    'z5gcdspl': '( ( %s /\\ ( D e. NN /\\ M e. NN ) ) -> ( R gcd ( D x. M ) ) = ( ( R gcd D ) x. ( %s gcd M ) ) )' % (SQF('R'), TT('D', 'R')),
    'z5psispl': '( ( %s /\\ ( D e. NN /\\ M e. NN ) ) -> %s = ( %s x. %s ) )' % (SQF('R'), PSI('R', '( D x. M )'), FMP('( R gcd D )'), PSI(TT('D', 'R'), 'M')),
    # section G: the kernel Gker (Detector.lean 654-688)
    'z5psigk': '( ( %s /\\ M e. NN ) -> %s = sum_ d e. %s %s )' % (SQF('T'), PSI('T', 'M'), DV('M'), GK('T', 'd')),
    # section F: the L-series factorisation (Detector.lean 690-972)
    'z5mulprod': '( ( ( G : NN --> CC /\\ ( G ` 1 ) = 1 /\\ %s ) /\\ ( A e. Fin /\\ A C_ NN ) ) -> ( G ` prod_ p e. A p ) = prod_ p e. A ( G ` p ) )' % MUL('G'),
    'z5cxpprod': '( ( ( A e. Fin /\\ A C_ NN ) /\\ S e. CC ) -> ( prod_ p e. A p ^c S ) = prod_ p e. A ( p ^c S ) )',
    'z5fconv': ('( ( ( ( A : NN --> CC /\\ F e. Fin /\\ F C_ NN ) /\\ A. l e. ( NN \\ F ) ( A ` l ) = 0 ) /\\ '
                '( ( B : NN --> CC /\\ C e. RR /\\ A. m e. NN ( abs ` ( B ` m ) ) <_ C ) /\\ ( Z e. CC /\\ 1 < ( Re ` Z ) ) ) ) -> '
                'seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( sum_ d e. F ( ( A ` d ) x. ( d ^c -u Z ) ) x. sum_ k e. NN ( ( B ` k ) x. ( k ^c -u Z ) ) ) )' % CV('n')),
    'z5gkeul': '( ( %s /\\ ( %s /\\ S e. CC ) ) -> sum_ d e. %s ( ( %s x. ( C ` d ) ) x. ( d ^c -u S ) ) = %s )' % (SQF('T'), CHR, DV('T'), GK('T', 'd'), EU(PF('T'))),
    'z5chpsi': '( ( %s /\\ ( ( %s /\\ %s ) /\\ %s ) ) -> seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( %s x. %s ) )' % (SQF('T'), CHR, CB, SRE1, CPS('T', 'n'), EU(PF('T')), LS()),
    'z5pmconv': ('( ( ( D e. NN /\\ N e. NN ) /\\ ( X e. CC /\\ G : NN --> CC ) ) -> sum_ d e. %s ( ( ( m e. NN |-> if ( m = D , X , 0 ) ) ` d ) x. ( G ` ( N / d ) ) ) '
                 '= if ( D || N , ( X x. ( G ` ( N / D ) ) ) , 0 ) )' % DV('N')),
    'z5stepb': '( ( ( R e. NN /\\ D e. NN ) /\\ ( ( %s /\\ %s ) /\\ %s ) ) -> seq 1 ( + , ( n e. NN |-> %s ) ) ~~> ( ( ( C ` D ) x. ( D ^c -u S ) ) x. ( %s x. %s ) ) )'
               % (CHR, CB, SRE1, SB('D', 'n'), EU(QS('D', 'R')), LS()),
    'z5pwise': ('( ( %s /\\ ( ( %s /\\ C : NN --> CC ) /\\ N e. NN ) ) -> ( ( ( ( A bvA B ) ` N ) x. %s ) x. ( C ` N ) ) = '
                'sum_ d e. ( 1 ... ( |_ ` B ) ) ( ( ( ( A bvLam B ) ` d ) x. %s ) x. if ( d || N , ( ( C ` N ) x. %s ) , 0 ) ) )'
                % (HAB0, SQF('R'), PSI('R', 'N'), FMP('( R gcd d )'), PSI(TT('d', 'R'), '( N / d )'))),
    'z5finser': '( ph -> seq 1 ( + , ( m e. NN |-> sum_ k e. A ( E x. ( G ` m ) ) ) ) ~~> sum_ k e. A ( E x. L ) )',
    'z5mrval': '( ( ( ( A e. U /\\ B e. V ) /\\ ( C e. W /\\ R e. X ) ) /\\ S e. CC ) -> %s = sum_ d e. ( 1 ... ( |_ ` B ) ) %s )' % (MR(), MRT('d')),
    'z5lser': ('( ( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ %s ) ) -> ( seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> /\\ sum_ n e. NN %s = ( %s x. %s ) ) )'
               % (HAB0, SQF('R'), CHR, CB, SRE1, LT('n'), LT('n'), LS(), MR())),
    # section N: Lemma 3.4 (Detector.lean 973-1276)
    'z5efabs': '( ( P e. Prime /\\ ( ( ( C ` P ) e. CC /\\ ( abs ` ( C ` P ) ) <_ 1 ) /\\ %s ) ) -> ( abs ` %s ) <_ ( P + 1 ) )' % (SRE0, EF('P')),
    'z5eunorm': '( ( ( Q e. Fin /\\ Q C_ Prime ) /\\ ( %s /\\ %s ) ) -> ( abs ` %s ) <_ prod_ p e. Q ( p + 1 ) )' % (CFN, SRE0, EU('Q')),
    'z5pp1ss': '( ( R e. NN /\\ Q C_ %s ) -> prod_ p e. Q ( p + 1 ) <_ prod_ p e. %s ( p + 1 ) )' % (PF('R'), PF('R')),
    'z5pp1sq': '( %s -> prod_ p e. %s ( p + 1 ) <_ ( R ^ 2 ) )' % (SQF('R'), PF('R')),
    'z5mrtabs': '( ( ( %s /\\ %s ) /\\ ( ( %s /\\ %s ) /\\ D e. NN ) ) -> ( abs ` %s ) <_ ( R ^ 3 ) )' % (HAB0, SQF('R'), CFN, SRE0, MRT('D')),
    'z5mrnorm': '( ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) -> ( abs ` %s ) <_ ( B x. ( R ^ 3 ) ) )' % (HAB0, SQF('R'), CFN, SRE0, MR()),
    'z5mrsum': ('( ( ( %s /\\ ( N e. V /\\ ( Y e. RR /\\ 1 <_ Y ) ) ) /\\ ( %s /\\ %s ) ) -> sum_ r e. ( N RSet Y ) ( ( 1 / r ) x. ( abs ` %s ) ) <_ ( B x. ( Y ^ 3 ) ) )'
                % (HAB0, CFN, SRE0, MR('S', 'r'))),
    'z5invmul': '( ( R e. NN /\\ ( Z e. RR /\\ 1 <_ Z ) ) -> sum_ d e. { x e. ( 1 ... ( |_ ` Z ) ) | R || x } ( 1 / d ) <_ ( ( 1 / R ) x. ( 1 + ( log ` Z ) ) ) )',
    'z5mrtcl': '( ( ( %s /\\ R e. NN ) /\\ ( ( C : NN --> CC /\\ S e. CC ) /\\ D e. NN ) ) -> %s e. CC )' % (HAB0, MRT('D')),
    'z5mrcl': '( ( ( %s /\\ R e. NN ) /\\ ( C : NN --> CC /\\ S e. CC ) ) -> %s e. CC )' % (HAB0, MR()),
    'z5sqfpdvd': '( ( %s /\\ ( D e. NN /\\ A. p e. Prime ( p || R -> p || D ) ) ) -> R || D )' % SQF('R'),
    'z5mrt1': ('( ( ( %s /\\ %s ) /\\ ( ( %s /\\ A. c e. Prime ( c || R -> ( C ` c ) = 1 ) ) /\\ D e. NN ) ) -> ( abs ` %s ) <_ if ( R || D , ( ( phi ` R ) x. ( 1 / D ) ) , 0 ) )'
               % (HAB0, SQF('R'), CFN, MRT('D', 'R', '1'))),
    'z5mr1': ('( ( ( %s /\\ 1 <_ B ) /\\ ( %s /\\ ( %s /\\ A. c e. Prime ( c || R -> ( C ` c ) = 1 ) ) ) ) -> ( abs ` %s ) <_ ( ( ( phi ` R ) / R ) x. ( 1 + ( log ` B ) ) ) )'
              % (HAB0, SQF('R'), CFN, MR1())),
    'z5mr1sum': ('( ( ( %s /\\ 1 <_ B ) /\\ ( ( N e. NN /\\ Y e. RR ) /\\ ( %s /\\ A. c e. Prime ( ( c gcd N ) = 1 -> ( C ` c ) = 1 ) ) ) ) -> '
                 'sum_ r e. ( N RSet Y ) ( ( 1 / r ) x. ( abs ` %s ) ) <_ ( sum_ r e. ( N RSet Y ) ( ( phi ` r ) / ( r ^ 2 ) ) x. ( 1 + ( log ` B ) ) ) )'
                 % (HAB0, CFN, MR1('r'))),
}

HYPS = {
    'z5finser': [('1', '( ph -> A e. Fin )'), ('2', '( ( ph /\\ ( k e. A /\\ m e. NN ) ) -> ( G ` m ) e. CC )'),
                 ('3', '( ( ph /\\ k e. A ) -> seq 1 ( + , G ) ~~> L )'), ('4', '( ( ph /\\ k e. A ) -> E e. CC )')],
}

ORDER = ['z5tofsq', 'z5tofcop', 'z5gcdcop', 'z5gcdspl', 'z5psispl',
         'z5psigk',
         'z5mulprod', 'z5cxpprod', 'z5fconv', 'z5gkeul', 'z5chpsi', 'z5pmconv', 'z5stepb', 'z5pwise', 'z5finser', 'z5mrval', 'z5lser',
         'z5efabs', 'z5eunorm', 'z5pp1ss', 'z5pp1sq', 'z5mrtabs', 'z5mrnorm', 'z5mrsum', 'z5invmul', 'z5mrtcl', 'z5mrcl', 'z5sqfpdvd', 'z5mrt1', 'z5mr1', 'z5mr1sum']

# ---- section P: the pole term and Proposition 4.4's assembly (Detector.lean 1448-1753)
PRIN = lambda N, v='n': '( %s e. NN |-> if ( ( %s gcd %s ) = 1 , 1 , 0 ) )' % (v, v, N)
EPV = lambda S='S': '( ( <. A , B , X >. EPole <. C , N , R >. ) ` %s )' % S
EPB = lambda S='S': ('( ( ( ( _G ` ( 1 - %s ) ) x. ( X ^c ( 1 - %s ) ) ) x. ( ( phi ` N ) / N ) ) x. sum_ r e. ( N RSet R ) ( ( 1 / r ) x. ( ( <. A , B >. Mr <. C , r >. ) ` 1 ) ) )'
                     % (S, S))
SETS6 = '( ( A e. U /\\ B e. V /\\ X e. W ) /\\ ( C e. T /\\ N e. Y /\\ R e. Z ) )'
P1D = 'sum_ r e. ( N RSet ( D ^c ( 1 / ; ; 1 0 0 ) ) ) ( 1 / r )'
XPD = '( D ^c ( 6 / 5 ) )'
STATEMENTS['z5epval'] = '( ( %s /\\ S e. CC ) -> %s = if ( C = %s , %s , 0 ) )' % (SETS6, EPV(), PRIN('N', 'h'), EPB())
STATEMENTS['z5ep0'] = '( ( ( %s /\\ S e. CC ) /\\ C =/= %s ) -> %s = 0 )' % (SETS6, PRIN('N', 'h'), EPV())
STATEMENTS['z5dlb'] = ('( ( ( ( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) ) /\\ N e. NN ) /\\ ( ( F e. CC /\\ E e. CC ) /\\ '
                       '( ( ( ( 1 / ; ; 2 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ %s /\\ '
                       '( ( abs ` ( ( F + ( ( exp ` ( -u 1 / %s ) ) x. %s ) ) - E ) ) <_ ( %s / 8 ) /\\ ( abs ` E ) <_ ( %s / 8 ) ) ) ) ) -> '
                       '( ( ( 1 / ; ; 4 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ ( abs ` F ) )' % (P1D, XPD, P1D, P1D, P1D))
ORDER += ['z5epval', 'z5ep0', 'z5dlb']

# ---- Lemma 4.3 in the corrected form of Detection.lean (norm_Epole_le')
PRN = PRIN('N')
HPN = 'A. c e. Prime ( ( c gcd N ) = 1 -> ( C ` c ) = 1 )'
MR1P = lambda r: '( ( <. A , B >. Mr <. %s , %s >. ) ` 1 )' % (PRN, r)
GAMH = ('A. z e. CC ( ( 0 <_ ( Re ` z ) /\\ ( Re ` z ) <_ 1 /\\ ( 1 / 2 ) <_ ( abs ` ( Im ` z ) ) ) -> '
        '( abs ` ( _G ` z ) ) <_ ( K x. ( exp ` -u ( abs ` ( Im ` z ) ) ) ) )')
Z1D = '( D ^c ( ; 3 1 / ; 5 0 ) )'; Z2D = '( D ^c ( ; 6 3 / ; ; 1 0 0 ) )'; RPD = '( D ^c ( 1 / ; ; 1 0 0 ) )'
LAM0 = '( ( ( log ` ( log ` D ) ) + ( ( 6 / 5 ) x. ( ( 1 - T ) x. ( log ` D ) ) ) ) + ( log ` ( ( ; ; ; 3 2 0 0 x. ( exp ` 1 ) ) x. K ) ) )'
EPD = '( ( <. %s , %s , %s >. EPole <. %s , N , %s >. ) ` S )' % (Z1D, Z2D, XPD, PRN, RPD)
STATEMENTS['z5prin'] = ('( N e. NN -> ( ( %s : NN --> CC /\\ A. j e. NN ( abs ` ( %s ` j ) ) <_ 1 ) /\\ A. c e. Prime ( ( c gcd N ) = 1 -> ( %s ` c ) = 1 ) ) )'
                        % (PRN, PRN, PRN))
STATEMENTS['z5phip1'] = ('( ( N e. V /\\ Y e. RR ) -> sum_ r e. ( N RSet Y ) ( ( phi ` r ) / ( r ^ 2 ) ) <_ sum_ r e. ( N RSet Y ) ( 1 / r ) )')
STATEMENTS['z5mrsp'] = ('( ( ( %s /\\ 1 <_ B ) /\\ ( N e. NN /\\ Y e. RR ) ) -> ( abs ` sum_ r e. ( N RSet Y ) ( ( 1 / r ) x. %s ) ) <_ '
                        '( sum_ r e. ( N RSet Y ) ( 1 / r ) x. ( 1 + ( log ` B ) ) ) )' % (HAB0, MR1P('r')))
STATEMENTS['z5gam1'] = ('( ( ( K e. RR /\\ %s ) /\\ ( S e. CC /\\ ( ( 0 <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) /\\ ( 1 / 2 ) <_ ( abs ` ( Im ` S ) ) ) ) ) -> '
                        '( abs ` ( _G ` ( 1 - S ) ) ) <_ ( K x. ( exp ` -u ( abs ` ( Im ` S ) ) ) ) )' % GAMH)
STATEMENTS['z5xabs'] = ('( ( ( X e. RR /\\ 1 <_ X ) /\\ ( T e. RR /\\ ( S e. CC /\\ T <_ ( Re ` S ) ) ) ) -> ( abs ` ( X ^c ( 1 - S ) ) ) <_ ( X ^c ( 1 - T ) ) )')
STATEMENTS['z5epole'] = ('( ( ( ( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) ) /\\ N e. NN ) /\\ ( ( ( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) ) /\\ ( K e. RR /\\ 1 <_ K ) ) /\\ '
                         '( ( %s /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) /\\ %s <_ ( abs ` ( Im ` S ) ) ) ) ) -> ( abs ` %s ) <_ ( %s / 8 ) )'
                         % (GAMH, LAM0, EPD, P1D))
ORDER += ['z5prin', 'z5phip1', 'z5mrsp', 'z5gam1', 'z5xabs', 'z5epole']

EPC = '( ( <. %s , %s , %s >. EPole <. C , N , %s >. ) ` S )' % (Z1D, Z2D, XPD, RPD)
HZD3 = '( D e. RR /\\ 1 < D /\\ ; ; 2 0 0 <_ ( log ` D ) )'
STATEMENTS['z5epcl'] = ('( ( ( %s /\\ N e. NN ) /\\ ( S e. CC /\\ ( C : NN --> CC /\\ ( C = %s -> ( 1 / 2 ) <_ ( abs ` ( Im ` S ) ) ) ) ) ) -> %s e. CC )'
                        % (HZD3, PRN, EPC))
A1_ = ('( ( %s /\\ N e. NN ) /\\ ( ( ( T e. RR /\\ ( 0 <_ T /\\ T <_ 1 ) ) /\\ ( K e. RR /\\ 1 <_ K ) ) /\\ ( %s /\\ ( S e. CC /\\ ( T <_ ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) ) ) )'
       % (HZD3, GAMH))
HP1_ = '( ( ( 1 / ; ; 2 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ %s' % P1D
HDET_ = '( abs ` ( ( F + ( ( exp ` ( -u 1 / %s ) ) x. %s ) ) - %s ) ) <_ ( %s / 8 )' % (XPD, P1D, EPC, P1D)
A2_ = '( ( C : NN --> CC /\\ ( C = %s -> %s <_ ( abs ` ( Im ` S ) ) ) ) /\\ ( F e. CC /\\ ( %s /\\ %s ) ) )' % (PRN, LAM0, HP1_, HDET_)
STATEMENTS['z5dlbe'] = '( ( %s /\\ %s ) -> ( ( ( 1 / ; ; 4 0 0 ) x. ( ( phi ` N ) / N ) ) x. ( log ` D ) ) <_ ( abs ` F ) )' % (A1_, A2_)
ORDER += ['z5epcl', 'z5dlbe']


def gramcheck(labels):
    import mm as _MM, re as _re
    out = {}
    for lab in labels:
        w = W('z5cg' + lab, 'grammar check of %s' % lab)
        for n, f in HYPS.get(lab, []):
            hyp(w, n, '%s.%s' % (lab, n), f)
        w.lines.append('qed:?:? |- %s' % STATEMENTS[lab])
        w.write()
        ok, text = _MM.run_mmj2(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        bad = [l for l in text.split('\n') if _re.match(r'^E-', l) and 'incomplete' not in l.lower() and 'E-PA-0410' not in l]
        out[lab] = bad
        try:
            os.remove(os.path.join(_MM.WSDIR, w.label + '.mmp'))
        except OSError:
            pass
    return out


def hyps_of(w, lab):
    return [hyp(w, n, '%s.%s' % (lab, n), f) for n, f in HYPS.get(lab, [])]


def run(w):
    return (runh if HYPS.get(w.label) else (lambda x: x.run()))(w)


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])


# ---- step helpers (from tools/gen/z5b_l.py, which is not importable as a module)
def pp(w, a, mem, v='p'):
    """( a -> v e. Prime ) from mem: ( a -> v e. { q e. Prime | ... } )"""
    return w.s([mem, w.inst('elrabi')], 'syl', '( %s -> %s e. Prime )' % (a, v))


def fmpre(w, a, pnn, p='p'):
    """( a -> FMP(p) e. RR ) from pnn: ( a -> p e. NN )"""
    st = mkst(w, a)
    mu = st([sy(w, a, pnn, 'mucl', '( mmu ` %s ) e. ZZ' % p)], 'zred', '( mmu ` %s ) e. RR' % p)
    ph = st([sy(w, a, pnn, 'phicl', '( phi ` %s ) e. NN' % p)], 'nnred', '( phi ` %s ) e. RR' % p)
    return st([mu, ph], 'remulcld', '%s e. RR' % FMP(p))


def elpf(w, X, v='p'):
    """closed: ( v e. PF(X) <-> ( v e. Prime /\\ v || X ) )"""
    return w.s([w.s([], 'breq1', '( q = %s -> ( q || %s <-> %s || %s ) )' % (v, X, v, X))], 'elrab', '( %s e. %s <-> ( %s e. Prime /\\ %s || %s ) )' % (v, PF(X), v, v, X))


def pfdvd(w, a, mem, X, v='p'):
    """( a -> v || X ) from mem: ( a -> v e. PF(X) )"""
    e = w.s([elpf(w, X, v)], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. Prime /\\ %s || %s ) ) )' % (a, v, PF(X), v, v, X))
    m = w.s([mem, e], 'mpbid', '( %s -> ( %s e. Prime /\\ %s || %s ) )' % (a, v, v, X))
    return w.s([m], 'simprd', '( %s -> %s || %s )' % (a, v, X))


def eldv(w, X, v='d'):
    """closed: ( v e. DV(X) <-> ( v e. NN /\\ v || X ) )"""
    return w.s([w.s([], 'breq1', '( x = %s -> ( x || %s <-> %s || %s ) )' % (v, X, v, X))], 'elrab', '( %s e. %s <-> ( %s e. NN /\\ %s || %s ) )' % (v, DV(X), v, v, X))


def dvparts(w, a, mem, X, v='d'):
    """steps ( a -> v e. NN ), ( a -> v || X ) from mem: ( a -> v e. DV(X) )"""
    e = w.s([eldv(w, X, v)], 'a1i', '( %s -> ( %s e. %s <-> ( %s e. NN /\\ %s || %s ) ) )' % (a, v, DV(X), v, v, X))
    m = w.s([mem, e], 'mpbid', '( %s -> ( %s e. NN /\\ %s || %s ) )' % (a, v, v, X))
    return w.s([m], 'simpld', '( %s -> %s e. NN )' % (a, v)), w.s([m], 'simprd', '( %s -> %s || %s )' % (a, v, X))


def cns(lab):
    """the consequent of a closed frozen statement ( ante -> concl )"""
    from cl import split_imp
    return split_imp(STATEMENTS[lab])[1]


def mulinst(w, a, G, I, J, gm, imem, jmem):
    """( a -> ( G ` ( I x. J ) ) = ( ( G ` I ) x. ( G ` J ) ) ) from gm: ( a -> MUL(G) ), imem: ( a -> I e. NN ), jmem: ( a -> J e. NN )"""
    MB = lambda i, j: '( %s ` ( %s x. %s ) ) = ( ( %s ` %s ) x. ( %s ` %s ) )' % (G, i, j, G, i, G, j)
    r1 = w.s([w.s([w.s([], 'oveq1', '( i = %s -> ( i x. j ) = ( %s x. j ) )' % (I, I))], 'fveq2d', '( i = %s -> ( %s ` ( i x. j ) ) = ( %s ` ( %s x. j ) ) )' % (I, G, G, I)),
              w.s([w.s([], 'fveq2', '( i = %s -> ( %s ` i ) = ( %s ` %s ) )' % (I, G, G, I))], 'oveq1d',
                  '( i = %s -> ( ( %s ` i ) x. ( %s ` j ) ) = ( ( %s ` %s ) x. ( %s ` j ) ) )' % (I, G, G, G, I, G))],
             'eqeq12d', '( i = %s -> ( %s <-> %s ) )' % (I, MB('i', 'j'), MB(I, 'j')))
    r2 = w.s([w.s([w.s([], 'oveq2', '( j = %s -> ( %s x. j ) = ( %s x. %s ) )' % (J, I, I, J))], 'fveq2d', '( j = %s -> ( %s ` ( %s x. j ) ) = ( %s ` ( %s x. %s ) ) )' % (J, G, I, G, I, J)),
              w.s([w.s([], 'fveq2', '( j = %s -> ( %s ` j ) = ( %s ` %s ) )' % (J, G, G, J))], 'oveq2d',
                  '( j = %s -> ( ( %s ` %s ) x. ( %s ` j ) ) = ( ( %s ` %s ) x. ( %s ` %s ) ) )' % (J, G, I, G, G, I, G, J))],
             'eqeq12d', '( j = %s -> ( %s <-> %s ) )' % (J, MB(I, 'j'), MB(I, J)))
    return w.s([r1, r2, gm, imem, jmem], 'rspc2dv', '( %s -> %s )' % (a, MB(I, J)))


def chrparts(w, a, chr_):
    """steps ( a -> C : NN --> CC ), ( a -> ( C ` 1 ) = 1 ), ( a -> MUL(C) ) from chr_: ( a -> CHR )"""
    return (w.s([chr_], 'simp1d', '( %s -> C : NN --> CC )' % a), w.s([chr_], 'simp2d', '( %s -> ( C ` 1 ) = 1 )' % a),
            w.s([chr_], 'simp3d', '( %s -> %s )' % (a, MUL('C'))))
