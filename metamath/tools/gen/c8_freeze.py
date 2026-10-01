"""C8: the frozen statements, and a grammar check of every one of them
through mmj2 (one worksheet whose steps are the statements; parse errors are
reported per step, unification is not attempted).

    MM_DB=sorties/c8.mm python3 tools/gen/c8_freeze.py         # grammar check
    MM_DB=sorties/c8.mm python3 tools/gen/c8_freeze.py print   # the table
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c8lib import *
import mm as _MM

S = {}
# ---- section 1: bounds on a compact rectangle --------------------------------------
BNDH = '( ( A e. CC /\\ B e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )'
S['crectbnd'] = '( %s -> E. m e. RR A. u e. ( A crect B ) ( abs ` ( G ` u ) ) <_ m )' % BNDH
S['crectlbd'] = '( ( ( A e. CC /\\ B e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) /\\ A. y e. ( A crect B ) ( G ` y ) =/= 0 ) -> E. m e. RR+ A. u e. ( A crect B ) m <_ ( abs ` ( G ` u ) ) )'
RQ = RE('Q'); IQ = IM('Q')
INTQ = '( Q e. CC /\\ ( ( %s < %s /\\ %s < %s ) /\\ ( %s < %s /\\ %s < %s ) ) )' % (RA, RQ, RQ, RB, IA, IQ, IQ, IB)
ALF = 'A. u e. %s ( abs ` ( F ` u ) ) <_ M' % FR
S['rectintlip'] = ('( ( ( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s ) /\\ ( ( %s /\\ 0 < R ) /\\ ( %s /\\ 0 < S ) ) /\\ ( M e. RR /\\ %s ) ) -> '
                   '( ( ( 2 x. _pi ) x. ( abs ` ( ( F ` Q ) - ( F ` P ) ) ) ) x. ( R x. S ) ) <_ ( ( ( 2 x. M ) x. %s ) x. ( abs ` ( Q - P ) ) ) )') % (
    AB, INTP, INTQ, HOLO, RBD('P', 'R'), RBD('Q', 'S'), ALF, PER)
S['hollip'] = '( %s -> E. l e. RR+ A. p e. ( A crect B ) A. q e. ( A crect B ) ( abs ` ( ( F ` p ) - ( F ` q ) ) ) <_ ( l x. ( abs ` ( p - q ) ) ) )' % ABGEO

# ---- section 2: the grid of principal logarithms ------------------------------------
S['slitq'] = '( ( ( U e. CC /\\ V e. CC ) /\\ ( M e. RR+ /\\ M <_ ( abs ` V ) /\\ ( abs ` ( U - V ) ) < M ) ) -> ( U / V ) e. %s )' % SLIT
S['crectpa'] = '( ( ( A e. CC /\\ B e. CC ) /\\ Z e. ( A crect B ) ) -> ( abs ` ( Z - A ) ) <_ %s )' % PER
S['crectaff'] = '( ( ( ( A e. CC /\\ B e. CC ) /\\ %s ) /\\ ( Z e. ( A crect B ) /\\ T e. ( 0 [,] 1 ) ) ) -> %s e. ( A crect B ) )' % (GEO, AFF('T', 'Z'))
S['hlogn'] = '( ( %s /\\ %s ) -> E. n e. NN %s )' % (ABGEO, NZ0, SLITP('n'))
S['dvfaff'] = ('( ( %s /\\ ( E e. %s /\\ ( A e. CC /\\ T e. CC ) ) /\\ A. v e. E %s e. D ) -> '
               '( CC _D ( w e. E |-> %s ) ) = ( w e. E |-> ( ( ( CC _D F ) ` %s ) x. T ) ) )') % (HOL, TOP, AFF('T', 'v'), FA('T', 'w'), AFF('T', 'w'))
S['hlogtdv'] = ('( ( %s /\\ ( E e. %s /\\ ( A e. CC /\\ ( U e. CC /\\ T e. CC ) ) ) /\\ A. v e. E ( ( %s e. D /\\ %s e. D ) /\\ ( %s =/= 0 /\\ %s e. %s ) ) ) -> '
                '( CC _D ( w e. E |-> ( log ` %s ) ) ) : E --> CC )') % (
    HOL, TOP, AFF('U', 'v'), AFF('T', 'v'), FA('T', 'v'), QT('U', 'T', 'v'), SLIT, QT('U', 'T', 'w'))
S['hlogh'] = '( ( ( %s /\\ %s ) /\\ ( N e. NN /\\ %s ) /\\ ( %s /\\ ( A crect B ) C_ D ) ) -> %s )' % (ABG, NZ0, SLITP('N'), EOPN, HOLE(LAM('N')))
S['eftel'] = ('( ( N e. NN0 /\\ V : ( 0 ... N ) --> ( CC \\ { 0 } ) ) -> ( exp ` sum_ k e. ( 0 ..^ N ) ( log ` ( ( V ` ( k + 1 ) ) / ( V ` k ) ) ) ) '
              '= ( ( V ` N ) / ( V ` 0 ) ) )')
S['hlogexp'] = '( ( ( %s /\\ %s ) /\\ ( N e. NN /\\ ( A crect B ) C_ D ) /\\ X e. ( A crect B ) ) -> ( exp ` %s ) = ( F ` X ) )' % (ABG, NZ0, LAMB('N', 'X'))
S['hollogex'] = '( ( %s /\\ ( %s /\\ %s ) ) -> E. g ( %s /\\ A. z e. E ( exp ` ( g ` z ) ) = ( F ` z ) ) )' % (ABGEO, NZ0, EOPN, HOLE('g'))
S['hollogdv'] = ('( ( ( %s /\\ ( %s /\\ E C_ D ) ) /\\ A. v e. E ( exp ` ( G ` v ) ) = ( F ` v ) ) -> '
                 'A. z e. E ( ( CC _D G ) ` z ) = ( ( ( CC _D F ) ` z ) / ( F ` z ) ) )') % (HOL, HOLE('G'))
S['hollog'] = ('( ( %s /\\ ( %s /\\ %s ) ) -> E. g ( %s /\\ A. z e. E ( ( ( CC _D g ) ` z ) = ( ( ( CC _D F ) ` z ) / ( F ` z ) ) '
               '/\\ ( exp ` ( g ` z ) ) = ( F ` z ) ) ) )') % (ABGEO, NZ0, EOPN, HOLE('g'))
S['orectopn'] = '%s e. %s' % (ORECT('A', 'B'), TOP)
S['orectss'] = '( ( A e. CC /\\ B e. CC ) -> %s C_ ( A crect B ) )' % ORECT('A', 'B')
S['crectorect'] = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( P e. CC /\\ Q e. CC ) /\\ ( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` Q ) < ( Re ` B ) ) /\\ '
                   '( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` Q ) < ( Im ` B ) ) ) ) -> ( P crect Q ) C_ %s )') % ORECT('A', 'B')

# ---- section 3: the log-derivative bound ----------------------------------------------
EXC = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ ( ( A crect B ) \\ { P } ) C_ dom ( CC _D F ) )'
EXO = '( ( F e. ( D -cn-> CC ) /\\ D e. %s ) /\\ ( ( D \\ { P } ) C_ dom ( CC _D F ) /\\ ( A crect B ) C_ D ) )' % TOP
S['rectintce0x'] = '( ( ( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s ) /\\ ( %s /\\ 0 < R ) /\\ ( M e. RR /\\ %s ) ) -> ( ( _pi x. R ) x. ( abs ` ( F ` Q ) ) ) <_ ( M x. %s ) )' % (
    AB, INTP, INTQ, EXC, RBD('Q', 'R'), ALF, PER)
S['rectintmmnx'] = '( ( ( ( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s ) /\\ ( %s /\\ 0 < R ) /\\ ( M e. RR /\\ %s ) ) /\\ N e. NN ) -> ( ( _pi x. R ) x. ( ( abs ` ( F ` Q ) ) ^ N ) ) <_ ( ( M ^ N ) x. %s ) )' % (
    AB, INTP, INTQ, EXO, RBD('Q', 'R'), ALF, PER)
S['rectintmmx'] = '( ( ( %s /\\ ( %s /\\ %s /\\ P =/= Q ) /\\ %s ) /\\ ( M e. RR /\\ %s ) ) -> ( abs ` ( F ` Q ) ) <_ M )' % (AB, INTP, INTQ, EXO, ALF)
S['rectintschx'] = '( ( ( %s /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( A crect B ) C_ D ) ) /\\ ( ( %s /\\ 0 < R ) /\\ ( ( M e. RR /\\ %s ) /\\ ( F ` P ) = 0 ) ) ) -> ( ( abs ` ( F ` Q ) ) x. R ) <_ ( M x. ( abs ` ( Q - P ) ) ) )' % (
    AB, INTP, INTQ, HOL, RBD('P', 'R'), ALF)
S['rectintbcx'] = ('( ( ( %s /\\ ( %s /\\ %s ) /\\ ( %s /\\ ( A crect B ) C_ D ) ) /\\ ( ( M e. RR /\\ 0 < M /\\ A. y e. D ( Re ` ( F ` y ) ) <_ M ) /\\ ( F ` P ) = 0 ) /\\ '
                   '( ( %s /\\ 0 < R ) /\\ ( abs ` ( Q - P ) ) < R ) ) -> ( abs ` ( F ` Q ) ) <_ ( ( ( 2 x. M ) x. ( abs ` ( Q - P ) ) ) / ( R - ( abs ` ( Q - P ) ) ) ) )') % (
    AB, INTP, INTQ, HOL, RBD('P', 'R'))
S['dvlipbnd'] = ('( ( %s /\\ ( X e. D /\\ ( K e. RR /\\ S e. RR+ ) ) /\\ A. y e. D ( ( abs ` ( y - X ) ) < S -> ( abs ` ( ( F ` y ) - ( F ` X ) ) ) <_ ( K x. ( abs ` ( y - X ) ) ) ) ) '
                 '-> ( abs ` ( ( CC _D F ) ` X ) ) <_ K )') % HOL
SQ2 = SQ('C', '2'); SQ138 = SQ('C', '( ; 1 3 / 8 )')
S['logdvbnd'] = ('( ( ( %s /\\ ( C e. CC /\\ %s C_ D ) ) /\\ ( A. y e. %s ( F ` y ) =/= 0 /\\ ( M e. RR+ /\\ A. y e. %s ( ( log ` ( abs ` ( F ` y ) ) ) - ( log ` ( abs ` ( F ` C ) ) ) ) <_ M ) ) '
                 '/\\ ( S e. CC /\\ ( abs ` ( S - C ) ) <_ ( 3 / 2 ) ) ) -> ( abs ` ( ( ( CC _D F ) ` S ) / ( F ` S ) ) ) <_ ( ; ; ; 6 2 7 2 x. M ) )') % (HOL, SQ2, SQ138, SQ138)

ORDER = list(S)


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'c8gc'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'c8gc', 'c8gc.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=c8gc  LOC_AFTER=?\n\n* grammar check of the frozen statements of C8\n\n')
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
