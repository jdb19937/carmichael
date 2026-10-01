"""Sortie Z6b helpers (Route Z: DetectionShift.lean sections 3-5).

Statements of Z6b-blueprint.md, one place.  They are added to z6alib's
STATEMENTS dict (in memory only; tools/z6alib.py is not edited), so that
z6alib's `ante`/`cns` and z6a_e3's `apply` see them.
`MM_DB=sorties/z6b.mm python3 tools/z6blib.py [LABEL...]` grammar-checks them.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6alib import *
from z6alib import STATEMENTS, HYPS, gramcheck, LATER

QPX = lambda X: QP % (X, X, X, X)

# ================================================================== section 3: Goursat and Cauchy with continuity-only points
ANT2 = ('( ( A e. CC /\\ B e. CC ) /\\ ( ( P e. CC /\\ %s ) /\\ ( Q e. CC /\\ %s ) ) /\\ '
        '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ ( ( A crect B ) \\ { P , Q } ) C_ dom ( CC _D F ) ) )' % (QPX('P'), QPX('Q')))
RI0 = '( F rectint <. A , B >. ) = 0'
# z6gsub: a sub-rectangle avoiding Q (set theory)
STATEMENTS['z6gsub'] = '( ( X C_ Y /\\ -. Q e. X ) -> ( X \\ { P } ) C_ ( Y \\ { P , Q } ) )'
# z6gour2h / z6gour2v: the cut between P and Q, vertical (Re P < Re Q) and horizontal (Im P < Im Q)
STATEMENTS['z6gour2h'] = '( ( %s /\\ ( Re ` P ) < ( Re ` Q ) ) -> %s )' % (ANT2, RI0)
STATEMENTS['z6gour2v'] = '( ( %s /\\ ( Im ` P ) < ( Im ` Q ) ) -> %s )' % (ANT2, RI0)
STATEMENTS['z6gour2a'] = '( ( %s /\\ ( ( Re ` P ) < ( Re ` Q ) \\/ ( Im ` P ) < ( Im ` Q ) ) ) -> %s )' % (ANT2, RI0)
# z6cneq: two distinct complex numbers differ in the real or the imaginary part
STATEMENTS['z6cneq'] = ('( ( ( P e. CC /\\ Q e. CC ) /\\ P =/= Q ) -> ( ( ( Re ` P ) < ( Re ` Q ) \\/ ( Im ` P ) < ( Im ` Q ) ) \\/ '
                        '( ( Re ` Q ) < ( Re ` P ) \\/ ( Im ` Q ) < ( Im ` P ) ) ) )')

# ================================================================== section 5: the rectangle identity and the shift
U5 = "( `' Re \" ( -u ( Re ` S ) (,) +oo ) )"                      # the half-plane Re w > -Re S, where E ( S + w ) lives
HMX = lambda w: '( ( %s ^c %s ) x. ( ( E ` ( S + %s ) ) x. %s ) )' % (XPD, w, w, MRr('R', '( S + %s )' % w))   # H_1 ( w )
HM = '( w e. %s |-> %s )' % (U5, HMX('w'))
DSM = '( a e. %s |-> if ( a = 0 , ( ( CC _D %s ) ` 0 ) , ( ( ( %s ` a ) - ( %s ` 0 ) ) / ( a - 0 ) ) ) )' % (U5, HM, HM, HM)   # dslope H_1 0
FF = '( b e. %s |-> ( ( _G ` ( b + 1 ) ) x. ( %s ` b ) ) )' % (U5, DSM)        # Gone = Gamma ( w + 1 ) dslope H_1 0 w
CB = 'A. j e. NN ( abs ` ( C ` j ) ) <_ 1'
# the deviation: A5 with CB next to C : NN --> CC (Z6b-blueprint section 3)
A5B = ('( ( ( %s /\\ N e. NN ) /\\ ( ( ( C : NN --> CC /\\ %s ) /\\ ( R e. NN /\\ ( mmu ` R ) =/= 0 ) ) /\\ ( %s /\\ S =/= 1 ) ) ) /\\ ( %s /\\ ( E ` S ) = 0 ) )'
       % (HZD3, CB, SRNG, LIF))
RES5 = '( ( ( _G ` ( 1 - S ) ) x. ( %s ^c ( 1 - S ) ) ) x. ( %s x. %s ) )' % (XPD, RESV, MRr('R', '1'))
K5 = '( %s x. %s )' % (TPI, RES5)
Y5 = '( ( abs ` ( Im ` S ) ) + 1 )'
OMGN = OMG()
LB0 = '( ( ; ; ; ; ; 4 0 0 0 0 0 x. %s ) x. ( ( N x. ( ( abs ` ( Im ` S ) ) + 3 ) ) ^ 2 ) )' % OMGN
M5 = '( ( ( ; ; ; 1 6 3 2 x. ; ; 1 2 8 ) x. ( %s ^c 3 ) ) x. ( %s x. ( %s x. ( R ^ 3 ) ) ) )' % (XPD, LB0, Z2D)
HB5 = '( ( %s /\\ ( C : NN --> CC /\\ R e. NN ) ) /\\ ( S e. CC /\\ %s ) )' % (HZD3, EHOL)
HF5 = '( ( %s /\\ ( C : NN --> CC /\\ R e. NN ) ) /\\ ( ( S e. CC /\\ ( 0 < ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) /\\ %s ) )' % (HZD3, EHOL)
HV5 = ('( ( %s /\\ ( C : NN --> CC /\\ R e. NN ) ) /\\ ( ( S e. CC /\\ ( 0 < ( Re ` S ) /\\ ( Re ` S ) <_ 1 ) ) /\\ ( %s /\\ ( E ` S ) = 0 ) ) )'
       % (HZD3, EHOL))
CVX4 = lambda W: '( ( ; ; ; ; ; 4 0 0 0 0 0 x. %s ) x. ( ( N x. ( ( abs ` ( Im ` %s ) ) + 3 ) ) ^ 2 ) )' % (OMGN, W)

# z6dvoff: a product is differentiable where both factors are
STATEMENTS['z6dvoff'] = ('( ( ( G e. ( U -cn-> CC ) /\\ U C_ dom ( CC _D G ) ) /\\ ( H e. ( U -cn-> CC ) /\\ V C_ dom ( CC _D H ) ) ) -> '
                         'V C_ dom ( CC _D ( z e. U |-> ( ( G ` z ) x. ( H ` z ) ) ) ) )')
# z6hm: H_1 is holomorphic on Re w > -Re S (Lean differentiable_Hone)
STATEMENTS['z6hm'] = '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (HB5, HM, U5, U5, HM)
# z6ff: Gone is continuous on Re w > -Re S and differentiable off 0 (Lean differentiableAt_Gone, dscn/dsdv)
STATEMENTS['z6ff'] = '( %s -> ( %s e. ( %s -cn-> CC ) /\\ ( %s \\ { 0 } ) C_ dom ( CC _D %s ) ) )' % (HF5, FF, U5, U5, FF)
# z6ffv: off 0, Gone ( W ) = Gamma ( W ) H_1 ( W ) (Lean Gone_eq_of_ne, with Hone_zero)
STATEMENTS['z6ffv'] = ('( ( %s /\\ ( W e. %s /\\ ( W e. %s /\\ W =/= 0 ) ) ) -> ( %s ` W ) = ( ( _G ` W ) x. %s ) )'
                       % (HV5, U5, DG, FF, HMX('W')))
# z6rect: the rectangle identity (Lean rectInt_Ghat_principal, one statement for every character)
RECT5 = lambda T: '( %s rectint <. ( %s + ( _i x. -u %s ) ) , ( 3 + ( _i x. %s ) ) >. )' % (GR('R'), CL, T, T)
STATEMENTS['z6rect'] = '( ( %s /\\ ( T e. RR /\\ %s <_ T ) ) -> %s = %s )' % (A5B, Y5, RECT5('T'), K5)
# z6gstrip: Gamma on -99/100 <_ Re W <_ 3 , | Im W | >_ 1 (z6gam1632 and one step of the functional equation)
STATEMENTS['z6gstrip'] = ('( ( W e. CC /\\ ( ( -u ( ; 9 9 / ; ; 1 0 0 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ 3 ) /\\ 1 <_ ( abs ` ( Im ` W ) ) ) ) -> '
                          '( abs ` ( _G ` W ) ) <_ ( ; ; ; 1 6 3 2 x. %s ) )' % E2('( abs ` ( Im ` W ) )'))
# z6cvxb: the convexity bound CVXB is polynomial (Lean norm_LFunction_strip_le, generic in the value)
STATEMENTS['z6cvxb'] = ('( ( N e. NN /\\ ( W e. CC /\\ ( 0 <_ ( Re ` W ) /\\ 1 <_ ( abs ` ( W - 1 ) ) ) ) /\\ ( V e. RR /\\ V <_ %s ) ) -> V <_ %s )'
                        % (CVXB('W'), CVX4('W')))
# z6lstrip: | E ( W ) / ( W - 1 ) | on Re W >_ 1/100 , | Im W | >_ 1 (CVXH below Re 2 , DSER and dserbnd above)
STATEMENTS['z6lstrip'] = ('( ( ( ( N e. NN /\\ ( C : NN --> CC /\\ %s ) ) /\\ ( %s /\\ %s ) ) /\\ ( W e. CC /\\ ( ( 1 / ; ; 1 0 0 ) <_ ( Re ` W ) /\\ 1 <_ ( abs ` ( Im ` W ) ) ) ) ) -> '
                          '( abs ` ( ( E ` W ) / ( W - 1 ) ) ) <_ %s )' % (CB, DSER, CVXH, CVX4('W')))
# z6grsd, z6grmaj: the strip hypotheses of z6shift for GR(R) (Lean integrable_Ghat_line, norm_Ghat_le, tendsto_Ghat_horiz)
STATEMENTS['z6grsd'] = ('( %s -> A. z e. CC ( ( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 ) /\\ ( ( ( Re ` z ) = %s \\/ ( Re ` z ) = 3 ) \\/ %s <_ ( abs ` ( Im ` z ) ) ) ) -> z e. %s ) )'
                        % (A5B, CL, CL, Y5, DS))
STATEMENTS['z6grmaj'] = ('( %s -> A. z e. CC ( ( ( %s <_ ( Re ` z ) /\\ ( Re ` z ) <_ 3 ) /\\ %s <_ ( abs ` ( Im ` z ) ) ) -> ( abs ` ( %s ` z ) ) <_ ( %s x. %s ) ) )'
                         % (A5B, CL, Y5, GR('R'), M5, E4('( abs ` ( Im ` z ) )')))
# z6rdg: a point right of Re = -1 other than 0 is in the domain of Gamma
STATEMENTS['z6rdg'] = '( ( U e. CC /\\ ( -u 1 < ( Re ` U ) /\\ U =/= 0 ) ) -> U e. %s )' % DG
# z6pdg: the pole 1 - S of L ( S + w ) is in the domain of Gamma
STATEMENTS['z6pdg'] = '( ( %s /\\ S =/= 1 ) -> ( 1 - S ) e. %s )' % (SRNG, DG)
# z6gmaj: the product of the four factor bounds of GR against the majorant (real algebra)
STATEMENTS['z6gmaj'] = ('( ( ( ( ( ( G e. RR /\\ 0 <_ G ) /\\ G <_ ( A x. E ) ) /\\ ( ( X e. RR /\\ 0 <_ X ) /\\ X <_ K ) ) /\\ '
                        '( ( ( V e. RR /\\ 0 <_ V ) /\\ V <_ ( B x. Q ) ) /\\ ( ( M e. RR /\\ 0 <_ M ) /\\ M <_ Z ) ) ) /\\ '
                        '( ( ( ( A e. RR /\\ 0 <_ A ) /\\ K e. RR ) /\\ ( ( B e. RR /\\ 0 <_ B ) /\\ Z e. RR ) ) /\\ '
                        '( ( E e. RR /\\ Q e. RR ) /\\ ( F e. RR /\\ ( Q x. E ) <_ ( ; ; 1 2 8 x. F ) ) ) ) ) -> '
                        '( ( G x. X ) x. ( V x. M ) ) <_ ( ( ( ( A x. ; ; 1 2 8 ) x. K ) x. ( B x. Z ) ) x. F ) )')
# z6shiftr as frozen in z6alib LATER, with the deviation CB (A5B)
STATEMENTS['z6shiftr_frozen'] = STATEMENTS['z6shiftr']
STATEMENTS['z6shiftr'] = '( %s -> ( %s - %s ) = %s )' % (A5B, VL(GR('R'), '3'), VL(GR('R'), CL), K5)

# ================================================================== section 4: the anchor identity
CNU = '( U -cn-> CC )'
STATEMENTS['z6cnadd'] = '( ( F e. %s /\\ G e. %s ) -> ( F oF + G ) e. %s )' % (CNU, CNU, CNU)
PSN = lambda N: '( seq 1 ( oF + , F ) ` %s )' % N
STATEMENTS['z6lps'] = ('( ( F : NN --> %s /\\ N e. NN ) -> ( %s e. %s /\\ A. z e. U ( %s ` z ) = sum_ i e. ( 1 ... N ) ( ( F ` i ) ` z ) ) )'
                       % (CNU, PSN('N'), CNU, PSN('N')))
MTEST = '( M : NN --> RR /\\ seq 1 ( + , M ) e. dom ~~> /\\ A. j e. NN A. y e. U ( abs ` ( ( F ` j ) ` y ) ) <_ ( M ` j ) )'
STATEMENTS['z6lsum'] = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( ( A cseg B ) C_ U /\\ ( F : NN --> %s /\\ %s ) ) ) -> '
                        'seq 1 ( + , ( k e. NN |-> ( ( F ` k ) lint <. A , B >. ) ) ) ~~> ( ( z e. U |-> sum_ k e. NN ( ( F ` k ) ` z ) ) lint <. A , B >. ) )'
                        % (CNU, MTEST))


# the anchor-specific objects
COEFG = lambda A, B, R, K: '( ( ( ( %s bvA %s ) ` %s ) x. ( ( mmu ` ( %s gcd %s ) ) x. ( phi ` ( %s gcd %s ) ) ) ) x. ( C ` %s ) )' % (A, B, K, R, K, R, K, K)
CNG = lambda A, B, R, K: '( %s x. ( %s ^c -u S ) )' % (COEFG(A, B, R, K), K)
STATEMENTS['z6acoef'] = ('( ( ( ( %s /\\ R e. NN ) /\\ ( ( C : NN --> CC /\\ %s ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) ) /\\ K e. NN ) -> ( abs ` %s ) <_ ( K x. R ) )'
                         % (HAB0, CB, CNG('A', 'B', 'R', 'K')))
STATEMENTS['z6aterm'] = ('( ( ( Y e. RR+ /\\ X e. RR+ ) /\\ ( S e. CC /\\ W e. CC ) /\\ ( A e. CC /\\ G e. CC ) ) -> '
                         '( ( G x. ( X ^c W ) ) x. ( A x. ( Y ^c -u ( S + W ) ) ) ) = ( ( A x. ( Y ^c -u S ) ) x. ( G x. ( ( Y / X ) ^c -u W ) ) ) )')
STATEMENTS['z6nx'] = '( ( N e. RR+ /\\ X e. RR+ ) -> ( N x. ( ( N / X ) ^c -u 3 ) ) = ( ( X ^c 3 ) x. ( N ^c -u 2 ) ) )'
SA = '( 3 + ( _i x. -u T ) )'; SB = '( 3 + ( _i x. T ) )'; SEG = '( %s cseg %s )' % (SA, SB)
CNK = lambda K: CNG(Z1D, Z2D, 'R', K)
FBODY = lambda K, V: '( %s x. ( ( _G ` %s ) x. ( ( %s / %s ) ^c -u %s ) ) )' % (CNK(K), V, K, XPD, V)
FNS = '( n e. NN |-> ( v e. %s |-> %s ) )' % (SEG, FBODY('n', 'v'))
K0A = '( ( ; 3 2 x. R ) x. ( %s ^c 3 ) )' % XPD
K1A = '( ( R x. ( %s ^c 3 ) ) x. ( ; ; 2 5 6 / ( log ` 2 ) ) )' % XPD
A4T = '( %s /\\ T e. RR+ )' % A4
A4K = '( %s /\\ ( T e. RR+ /\\ K e. NN ) )' % A4
LFK = '( ( %s ` K ) lint <. %s , %s >. )' % (FNS, SA, SB)
STATEMENTS['z6anp'] = ('( ( %s /\\ ( T e. RR+ /\\ ( K e. NN /\\ V e. %s ) ) ) -> ( ( ( Re ` V ) = 3 /\\ V e. %s ) /\\ ( ( ( %s ` K ) ` V ) = %s /\\ '
                       '( abs ` %s ) <_ ( %s x. ( K ^c -u 2 ) ) ) ) )' % (A4, SEG, DG, FNS, FBODY('K', 'V'), FBODY('K', 'V'), K0A))
STATEMENTS['z6anl'] = '( %s -> seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) ~~> %s )' % (A4T, FNS, SA, SB, LI(G3('R'), '3', 'T'))
STATEMENTS['z6anv'] = '( %s -> %s = ( %s x. %s ) )' % (A4K, LFK, CNK('K'), LI(GY('( K / %s )' % XPD), '3', 'T'))
STATEMENTS['z6anb'] = '( %s -> ( abs ` %s ) <_ ( ( %s x. ( K ^c -u 2 ) ) x. ( 2 x. T ) ) )' % (A4K, LFK, K0A)
STATEMENTS['z6aerr'] = ('( %s -> ( abs ` ( %s - ( %s x. %s ) ) ) <_ ( ( %s x. %s ) x. ( K ^c -u 2 ) ) )'
                        % (A4K, LFK, TPI, STERM('R', 'K'), K1A, E4('T')))


class LZ(dict):
    """facts lifted lazily from src (formula -> step under another antecedent) to ctx"""
    def __init__(self, w, src, ctx):
        dict.__init__(self); self.w = w; self.src = src; self.ctx = ctx

    def __contains__(self, k):
        return dict.__contains__(self, k) or k in self.src

    def __getitem__(self, k):
        if not dict.__contains__(self, k):
            from cl import lift
            dict.__setitem__(self, k, lift(self.w, self.src[k], self.ctx))
        return dict.__getitem__(self, k)


STF = '( n e. NN |-> %s )' % STERM('R', 'n')
TSF = '( n e. NN |-> ( %s x. %s ) )' % (TPI, STERM('R', 'n'))
Z2S = 'sum_ m e. NN ( m ^c -u 2 )'
STATEMENTS['z6ancv'] = '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ seq 1 ( + , %s ) e. dom ~~> ) )' % (A4, STF, TSF)
STATEMENTS['z6anbd'] = ('( %s -> ( abs ` ( %s - ( %s x. sum_ m e. NN %s ) ) ) <_ ( ( %s x. %s ) x. %s ) )'
                        % (A4T, LI(G3('R'), '3', 'T'), TPI, STERM('R', 'm'), K1A, Z2S, E4('T')))


def need(*labels):
    """load the statements of database theorems into STATEMENTS (for apply/ante)"""
    import a5lib
    for l in labels:
        if l not in STATEMENTS:
            STATEMENTS[l] = a5lib.dbstmt(l)


def applyn(w, a, lab, m, facts):
    """z6a_e3.apply with the statement loaded from the database when needed"""
    need(lab)
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
    from z6a_e3 import apply
    return apply(w, a, lab, m, facts)


ORDER3 = ['z6gsub', 'z6gour2h', 'z6gour2v', 'z6gour2a', 'z6cneq', 'z6gour2', 'z6cau2']
ORDER5 = ['z6dvoff', 'z6hm', 'z6ff', 'z6ffv', 'z6rdg', 'z6pdg', 'z6rect', 'z6gstrip', 'z6cvxb', 'z6lstrip', 'z6grsd', 'z6gmaj', 'z6grmaj', 'z6shiftr']
ORDER4 = ['z6cnadd', 'z6lps', 'z6lsum', 'z6acoef', 'z6aterm', 'z6nx', 'z6anp', 'z6anl', 'z6anv', 'z6anb', 'z6aerr', 'z6ancv', 'z6anbd', 'z6anchor']

if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or (ORDER3 + ORDER5 + ORDER4))
    for k, v in r.items():
        print(('OK   ' if not v else 'FAIL ') + k)
        for l in v:
            print('   ', l[:300])
