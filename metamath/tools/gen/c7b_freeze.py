"""C7b: the frozen statements, and a grammar check of every one of them
through mmj2 (one worksheet whose steps are the statements; parse errors are
reported per step, unification is not attempted).

    MM_DB=sorties/c7b.mm python3 tools/gen/c7b_freeze.py         # grammar check
    MM_DB=sorties/c7b.mm python3 tools/gen/c7b_freeze.py print   # the table
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import mm as _MM

S = {}
# ---- section 1: the Dirichlet-series product ------------------------------------
ABZN = '( ( A : NN --> CC /\\ B : NN --> CC ) /\\ ( Z e. CC /\\ N e. NN ) )'
S['dconvfin'] = '( %s -> %s = sum_ e e. ( 1 ... N ) ( %s x. %s ) )' % (ABZN, CPS('N'), TRM('A', 'e'), PS('B', '( |_ ` ( N / e ) )'))
BZ = '( %s /\\ %s )' % (CFBB, ZP1)
S['dconvblk'] = '( ( %s /\\ ( M e. NN /\\ N e. ( ZZ>= ` M ) ) ) -> ( abs ` ( %s - %s ) ) <_ ( C x. ( ( M ^c ( 1 - %s ) ) / %s ) ) )' % (
    BZ, PS('B', 'N'), PS('B', 'M'), RZ, E1)
S['dconvfl'] = '( ( ( N e. NN /\\ D e. ( 1 ... N ) ) /\\ E e. RR+ ) -> ( %s ^c -u E ) <_ ( ( ( 2 ^c E ) x. ( D ^c E ) ) x. ( N ^c -u E ) ) )' % FLD
S['dconvtm'] = '( ( %s /\\ ( N e. NN /\\ D e. ( 1 ... N ) ) ) -> ( ( abs ` ( %s - %s ) ) x. ( D ^c -u %s ) ) <_ ( %s x. ( ( N ^c -u %s ) / D ) ) )' % (
    BZ, PS('B', FLD), PS('B', 'N'), RZ, DK, E1)
S['dconvdif'] = '( %s -> ( %s - ( %s x. %s ) ) = sum_ e e. ( 1 ... N ) ( %s x. ( %s - %s ) ) )' % (
    ABZN, CPS('N'), PS('A', 'N'), PS('B', 'N'), TRM('A', 'e'), PS('B', '( |_ ` ( N / e ) )'), PS('B', 'N'))
S['dconvdifb'] = '( ( %s /\\ N e. NN ) -> ( abs ` ( %s - ( %s x. %s ) ) ) <_ ( %s x. ( ( N ^c -u %s ) x. ( ( log ` N ) + K ) ) ) )' % (
    DCH, CPS('N'), PS('A', 'N'), PS('B', 'N'), DK, E1)
S['cxpnegcvg'] = '( E e. RR+ -> ( n e. NN |-> ( n ^c -u E ) ) ~~> 0 )'
S['cxplogcvg'] = '( E e. RR+ -> ( n e. NN |-> ( ( log ` n ) x. ( n ^c -u E ) ) ) ~~> 0 )'
S['dconvmaj'] = '( ( ( D e. RR /\\ K e. RR ) /\\ E e. RR+ ) -> %s ~~> 0 )' % MJ()
S['dconvdif0'] = '( %s -> ( n e. NN |-> ( %s - ( %s x. %s ) ) ) ~~> 0 )' % (DCH, CPS('n'), PS('A', 'n'), PS('B', 'n'))
S['dconvlim1'] = '( %s -> seq 1 ( + , %s ) ~~> ( %s x. %s ) )' % (DCH, CMAP(), SER('A'), SER('B'))
S['dconvlim'] = '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ %s = ( %s x. %s ) ) )' % (DCH, CMAP(), CSER(), SER('A'), SER('B'))

# ---- section 2: the real von Mangoldt series ---------------------------------------
S['vmtmb'] = '( ( K e. NN /\\ E e. RR+ ) -> ( ( Lam ` K ) x. ( K ^c -u ( 1 + E ) ) ) <_ ( ( 2 / E ) x. ( K ^c -u ( 1 + ( E / 2 ) ) ) ) )'
S['vmsercvg'] = '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (T1, RVT('n'))
S['vmbndlem'] = '( ( E e. RR+ /\\ E <_ 1 ) -> ( ( 2 / E ) x. ( 1 + ( 1 / ( E / 2 ) ) ) ) <_ ( 6 / ( E ^ 2 ) ) )'
S['vmbnd'] = '( ( T e. RR /\\ 1 < T /\\ T <_ 2 ) -> sum_ k e. NN %s <_ ( 6 / ( ( T - 1 ) ^ 2 ) ) )' % RVT('k')

# ---- section 3: the character instances, chi Lambda ---------------------------------
NXZ = '( %s /\\ %s )' % (NX, ZP1)
S['lchvmval'] = '( K e. NN -> ( %s ` K ) = ( %s x. ( Lam ` K ) ) )' % (AXL, CHV('K'))
S['lchvmf'] = '( %s -> %s : NN --> CC )' % (NX, AXL)
S['lchvmlav'] = '( %s -> %s )' % (NX, LAV(AXL, K4))
S['lchvmtm'] = '( ( %s /\\ ( K e. NN /\\ Z e. CC ) ) -> ( abs ` %s ) <_ %s )' % (NX, VMT('K'), RVT('K', RZ))
S['lchvmacvg'] = '( %s -> seq 1 ( + , ( n e. NN |-> ( abs ` %s ) ) ) e. dom ~~> )' % (NXZ, VMT('n'))
S['lchvmcvg'] = '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (NXZ, VMT('n'))
S['lchvmcv'] = '( ( %s /\\ K e. NN ) -> %s = ( %s x. ( log ` K ) ) )' % (NX, CV('K', AXL, AX), CHV('K'))
S['lchrconvlem'] = '( %s -> ( seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> /\\ ( sum_ k e. NN %s x. sum_ k e. NN %s ) = sum_ k e. NN %s ) )' % (
    NXZ, LGT('n'), VMT('k'), CHT('k'), LGT('k'))
S['lchlgcvg'] = '( %s -> seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~> )' % (NXZ, LGT('n'))
S['lchrconv'] = '( %s -> ( sum_ k e. NN %s x. sum_ k e. NN %s ) = sum_ k e. NN %s )' % (NXZ, VMT('k'), CHT('k'), LGT('k'))
S['lvmbnd'] = '( ( %s /\\ ( Z e. CC /\\ ( 1 < %s /\\ %s <_ 2 ) ) ) -> ( abs ` sum_ k e. NN %s ) <_ ( 6 / ( %s ^ 2 ) ) )' % (NX, RZ, RZ, VMT('k'), E1)

# ---- section 4: chi mu, the nonvanishing ----------------------------------------
S['lchmuval'] = '( K e. NN -> ( %s ` K ) = ( %s x. ( mmu ` K ) ) )' % (AXM, CHV('K'))
S['lchmucfb'] = '( %s -> %s )' % (NX, CFBX(AXM, '1'))
S['lchmulav'] = '( %s -> %s )' % (NX, LAV(AXM, '1'))
S['lchmucv'] = '( ( %s /\\ K e. NN ) -> %s = if ( K = 1 , 1 , 0 ) )' % (NX, CV('K', AXM, AX))
S['lchmuser'] = '( Z e. CC -> sum_ k e. NN ( if ( k = 1 , 1 , 0 ) x. ( k ^c -u Z ) ) = 1 )'
S['lchrmu'] = '( %s -> ( sum_ k e. NN %s x. sum_ k e. NN %s ) = 1 )' % (NXZ, MUT('k'), CHT('k'))
S['lchrne0'] = '( %s -> sum_ k e. NN %s =/= 0 )' % (NXZ, CHT('k'))

# ---- section 5: the logarithmic derivative ---------------------------------------
NXT = '( %s /\\ ( %s /\\ Z e. %s ) )' % (NX, T1, HP())
S['lchrdvval'] = '( %s -> ( ( CC _D %s ) ` Z ) = -u sum_ k e. NN %s )' % (NXT, LSFX, LGT('k'))
S['lchrlogdv'] = '( %s -> ( ( ( CC _D %s ) ` Z ) / sum_ k e. NN %s ) = -u sum_ k e. NN %s )' % (NXT, LSFX, CHT('k'), VMT('k'))

# ---- section 6 (provisional, C7a): the log-derivative of the finite product -------
FPR = 'prod_ q e. S ( ( z - q ) ^ ( O ` q ) )'
FPRZ = 'prod_ q e. S ( ( Z - q ) ^ ( O ` q ) )'
S['fprodlogdv'] = '( ( ( S e. Fin /\\ S C_ CC /\\ O : S --> NN ) /\\ Z e. ( CC \\ S ) ) -> ( ( CC _D ( z e. ( CC \\ S ) |-> %s ) ) ` Z ) = ( %s x. sum_ q e. S ( ( O ` q ) / ( Z - q ) ) ) )' % (FPR, FPRZ)

ORDER = list(S)


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'c7bgc'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'c7bgc', 'c7bgc.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=c7bgc  LOC_AFTER=?\n\n* grammar check of the frozen statements of C7b\n\n')
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
