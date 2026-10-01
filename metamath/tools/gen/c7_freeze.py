"""C7: the frozen statements, and a grammar check of every one of them through
mmj2 (one worksheet whose steps are the statements; parse errors are reported
per step, unification is not attempted).

    MM_DB=sorties/c7.mm python3 tools/gen/c7_freeze.py         # grammar check
    MM_DB=sorties/c7.mm python3 tools/gen/c7_freeze.py print   # the table
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7lib import *
import mm as _MM

S = {}
# ---- section 1: the Perron far regime -----------------------------------------
S['rectintco'] = '( ( F e. V /\\ ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ R e. RR ) ) -> ( F rectint <. %s , %s >. ) = %s )' % (
    CPT('P', 'S'), CPT('Q', 'R'), FOUR('F', 'P', 'Q', 'S', 'R'))
PQSR = '( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ R e. RR ) )'
S['pkrecidc'] = '( ( U e. RR+ /\\ %s /\\ ( ( P < 0 /\\ 0 < Q ) /\\ ( S < 0 /\\ 0 < R ) ) ) -> %s = %s )' % (PQSR, FOUR(PK0, 'P', 'Q', 'S', 'R'), TPI)
S['pkrecid0c'] = '( ( U e. RR+ /\\ %s /\\ ( ( P <_ Q /\\ S <_ R ) /\\ 0 < P ) ) -> %s = 0 )' % (PQSR, FOUR(PK0, 'P', 'Q', 'S', 'R'))
HB = '( ( 1 / ( abs ` S ) ) x. ( ( ( U ^c Q ) - ( U ^c P ) ) / %s ) )' % LGU
S['hedgbndr'] = '( ( ( ( U e. RR+ /\\ U =/= 1 ) /\\ ( P e. RR /\\ Q e. RR ) ) /\\ ( ( S e. RR /\\ S =/= 0 ) /\\ P <_ Q ) ) -> ( abs ` %s ) <_ %s )' % (
    E(CPT('Q', 'S'), CPT('P', 'S')), HB)
S['edgesol'] = '( ( ( ( X e. CC /\\ Y e. CC ) /\\ ( V e. CC /\\ K e. CC ) ) /\\ W e. CC ) -> ( ( ( X + Y ) + ( V + K ) ) = W -> ( abs ` ( K - W ) ) <_ ( ( abs ` X ) + ( ( abs ` Y ) + ( abs ` V ) ) ) ) )'
S['farabs'] = '( ( %s /\\ T e. RR+ ) -> ( 1 <_ %s /\\ ( ( T ^ 2 ) x. %s ) <_ ( U ^c %s ) ) )' % (UGT1, FA, LGU, FA)
S['farabs0'] = '( ( %s /\\ %s ) -> ( ( C + 1 ) <_ %s /\\ ( U ^c %s ) <_ ( ( U ^c C ) / ( ( T ^ 2 ) x. %s ) ) ) )' % (ULT1, CT, FB, FB, NLGU)
HS = '( S e. RR /\\ ( abs ` S ) = T )'
S['pkgt1h'] = '( ( ( %s /\\ %s ) /\\ %s ) -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (
    UGT1, CT, HS, E(CPT('-u ' + FA, 'S'), CPT('C', 'S')), BND1, E(CPT('C', 'S'), CPT('-u ' + FA, 'S')), BND1)
S['pkgt1v'] = '( ( %s /\\ %s ) -> ( abs ` %s ) <_ %s )' % (UGT1, CT, E(CPT('-u ' + FA, 'T'), CPT('-u ' + FA, '-u T')), BND1)
S['pkgt1'] = '( ( %s /\\ %s ) -> ( abs ` ( %s - %s ) ) <_ ( ( 6 x. ( U ^c C ) ) / ( T x. %s ) ) )' % (UGT1, CT, PK, TPI, LGU)
S['pklt1h'] = '( ( ( %s /\\ %s ) /\\ %s ) -> ( ( abs ` %s ) <_ %s /\\ ( abs ` %s ) <_ %s ) )' % (
    ULT1, CT, HS, E(CPT('C', 'S'), CPT(FB, 'S')), BND0, E(CPT(FB, 'S'), CPT('C', 'S')), BND0)
S['pklt1v'] = '( ( %s /\\ %s ) -> ( abs ` %s ) <_ %s )' % (ULT1, CT, E(CPT(FB, '-u T'), CPT(FB, 'T')), BND0)
S['pklt1'] = '( ( %s /\\ %s ) -> ( abs ` %s ) <_ ( ( 6 x. ( U ^c C ) ) / ( T x. ( abs ` %s ) ) ) )' % (ULT1, CT, PK, LGU)
S['pkind'] = '( ( ( U e. RR+ /\\ U =/= 1 ) /\\ %s ) -> ( abs ` ( %s - if ( 1 < U , %s , 0 ) ) ) <_ ( ( 6 x. ( U ^c C ) ) / ( T x. ( abs ` %s ) ) ) )' % (CT, PK, TPI, LGU)
X01 = '( 0 (,) 1 )'
WT = '( P + ( t x. ( Q - P ) ) )'
LQ = '( ( Q - P ) / %s )' % WT
PQ = '( P e. RR+ /\\ Q e. RR+ )'
S['logaffdv'] = '( %s -> ( RR _D ( t e. %s |-> ( log ` %s ) ) ) = ( t e. %s |-> %s ) )' % (PQ, X01, WT, X01, LQ)
S['logaffibl'] = '( %s -> ( ( t e. %s |-> %s ) e. ( %s -cn-> CC ) /\\ ( t e. %s |-> %s ) e. L^1 ) )' % (PQ, X01, LQ, X01, X01, LQ)
S['logaffitg'] = '( %s -> S. %s %s _d t = ( ( log ` Q ) - ( log ` P ) ) )' % (PQ, X01, LQ)
S['pkvlog'] = '( ( ( U e. RR+ /\\ C e. RR ) /\\ ( %s /\\ P <_ Q ) ) -> ( abs ` %s ) <_ ( ( U ^c C ) x. ( ( log ` Q ) - ( log ` P ) ) ) )' % (
    PQ, E(CPT('C', 'P'), CPT('C', 'Q')))
S['pkvlogn'] = '( ( ( U e. RR+ /\\ C e. RR ) /\\ ( %s /\\ Q <_ P ) ) -> ( abs ` %s ) <_ ( ( U ^c C ) x. ( ( log ` P ) - ( log ` Q ) ) ) )' % (
    PQ, E(CPT('C', '-u P'), CPT('C', '-u Q')))
S['pkbnd'] = '( ( ( U e. RR+ /\\ C e. RR+ /\\ T e. RR+ ) /\\ C <_ T ) -> ( abs ` %s ) <_ ( ( 2 x. ( U ^c C ) ) x. ( 1 + ( log ` ( T / C ) ) ) ) )' % PK
# ---- section 2: the line moment ------------------------------------------------
S['pol2exp'] = '( ( W e. RR /\\ 0 <_ W ) -> ( ( ( 1 + W ) ^ 2 ) x. ( 2 ^c -u ( W / 2 ) ) ) <_ ( ; ; 1 2 8 x. ( 2 ^c -u ( W / 4 ) ) ) )'
UK = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( K e. RR /\\ ( A e. RR /\\ B e. RR ) ) )'
UKL = '( ( U e. RR+ /\\ U =/= 1 ) /\\ ( ( K e. RR /\\ K =/= 0 ) /\\ ( A e. RR /\\ B e. RR /\\ A <_ B ) ) )'
AB_ = '( A (,) B )'
S['cxpaffdv2'] = '( %s -> ( RR _D ( u e. %s |-> ( ( U ^c ( K x. u ) ) / %s ) ) ) = ( u e. %s |-> ( ( U ^c ( K x. u ) ) x. K ) ) )' % (UK, AB_, LGU, AB_)
S['cxpaffibl2'] = '( %s -> ( ( u e. %s |-> ( U ^c ( K x. u ) ) ) e. ( %s -cn-> CC ) /\\ ( u e. %s |-> ( U ^c ( K x. u ) ) ) e. L^1 ) )' % (UK, AB_, AB_, AB_)
S['cxpaffitg2'] = '( %s -> S. %s ( U ^c ( K x. u ) ) _d u = ( ( ( U ^c ( K x. B ) ) - ( U ^c ( K x. A ) ) ) / ( K x. %s ) ) )' % (UKL, AB_, LGU)
S['exp4itg'] = '( T e. RR+ -> S. ( 0 (,) T ) ( 2 ^c -u ( u / 4 ) ) _d u <_ ( 4 / ( log ` 2 ) ) )'
S['exp4itgn'] = '( T e. RR+ -> S. ( -u T (,) 0 ) ( 2 ^c ( u / 4 ) ) _d u <_ ( 4 / ( log ` 2 ) ) )'
S['gamlmom.x'] = '( ph -> ( X e. RR /\\ %s <_ X /\\ X <_ 3 ) )' % HUND
S['gamlmom.t'] = '( ph -> T e. RR+ )'
S['gamlmom.h'] = '( ph -> ( H e. RR+ /\\ %s ) )' % GSB
S['gamlmom.i'] = '( ph -> ( u e. ( -u T (,) T ) |-> %s ) e. L^1 )' % GML
S['gamlmom'] = '( ph -> S. ( -u T (,) T ) %s _d u <_ ( ( ; ; ; 1 0 2 4 x. H ) / ( log ` 2 ) ) )' % GML
S['gamcnl'] = '( ( X e. RR /\\ 0 < X ) -> ( u e. RR |-> ( _G ` ( X + ( _i x. u ) ) ) ) e. ( RR -cn-> CC ) )'
S['gamlibl'] = '( ( ( X e. RR /\\ 0 < X ) /\\ T e. RR+ ) -> ( u e. ( -u T (,) T ) |-> %s ) e. L^1 )' % GML
S['gamlmomx'] = 'E. h e. RR+ A. c e. RR A. b e. RR+ ( ( %s <_ c /\\ c <_ 3 ) -> S. ( -u b (,) b ) ( ( abs ` ( _G ` ( c + ( _i x. u ) ) ) ) x. ( ( 1 + ( abs ` u ) ) ^ 2 ) ) _d u <_ h )' % HUND
# ---- section 3: the eta series -------------------------------------------------
S['mod2abs'] = '( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 )' % (SM2, SM2)
S['etacvg'] = '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (ZP0, ETT('n', 'Z'))
S['etabnd'] = '( %s -> ( abs ` %s ) <_ ( ( abs ` Z ) x. ( 1 + ( 1 / ( Re ` Z ) ) ) ) )' % (ZP0, ETA('Z'))
S['etabnd4'] = '( ( Z e. CC /\\ ( 1 / 4 ) <_ ( Re ` Z ) ) -> ( abs ` %s ) <_ ( 5 x. ( 2 + ( abs ` Z ) ) ) )' % ETA('Z')
ETAF = '( z e. %s |-> %s )' % (HP(), ETA('z'))
S['etahol'] = '( ( T e. RR /\\ 0 <_ T ) -> %s )' % HOLG2(ETAF, HP())
S['altps'] = '( K e. NN -> sum_ i e. ( 1 ... K ) %s = ( K mod 2 ) )' % ALTT('i')
S['altabs'] = '( ( %s : NN --> CC /\\ 1 e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ 1 ) /\\ A. m e. NN ( abs ` sum_ i e. ( 1 ... m ) ( %s ` i ) ) <_ 1 )' % (ALT, ALT, ALT)
S['etaalt'] = '( %s -> %s = sum_ k e. NN ( %s x. ( k ^c -u Z ) ) )' % (ZP1, ETA('Z'), ALTT('k'))
S['zsereven'] = '( %s -> sum_ k e. NN if ( 2 || k , ( k ^c -u Z ) , 0 ) = ( ( 2 ^c -u Z ) x. %s ) )' % (ZP1, ZS('Z'))
S['zseralt'] = '( %s -> sum_ k e. NN ( %s x. ( k ^c -u Z ) ) = ( %s x. %s ) )' % (ZP1, ALTT('k'), GF, ZS('Z'))
S['etazser'] = '( %s -> %s = ( %s x. %s ) )' % (ZP1, ETA('Z'), GF, ZS('Z'))
S['gfunne0'] = '( %s -> %s =/= 0 )' % (ZP1, GF)

ORDER = list(S)


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'c7gc'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'c7gc', 'c7gc.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=c7gc  LOC_AFTER=?\n\n* grammar check of the frozen statements of C7\n\n')
        for i, lab in enumerate(ORDER, 1):
            f.write('%d:: |- %s\n' % (i, S[lab]))
        f.write('qed:: |- ( 1 = 1 -> 1 = 1 )\n$)\n')
    ok, text = _MM.run_mmj2(path)
    errs = re.findall(r'Step (\d+)[^\n]*grammatical', text)
    for e in errs:
        print('GRAMMAR ERROR in', ORDER[int(e) - 1])
    if not errs:
        print('grammar OK for %d statements' % len(ORDER))
    return text


if __name__ == '__main__':
    if 'print' in sys.argv:
        for lab in ORDER:
            print('| `%s` | `%s` |' % (lab, S[lab]))
    else:
        t = check()
        if 'dump' in sys.argv:
            print(t[-4000:])
