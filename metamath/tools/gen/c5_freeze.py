"""C5: the frozen statements, and a grammar check of every one of them through
mmj2 (one worksheet whose steps are the statements; parse errors are reported
per step, unification is not attempted).

    MM_DB=sorties/c5.mm python3 tools/gen/c5_freeze.py         # grammar check
    MM_DB=sorties/c5.mm python3 tools/gen/c5_freeze.py print   # the table
"""
import sys, os, re, subprocess
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c5lib import *
import mm as _MM

RZ = '( Re ` Z )'
TRMK = TRM('A', 'k', 'z')
G = GSUM(); H = HSUM(); PS = PSQ('F'); PSD = PSQ(DF())
E = EH

S = {}
# ---- the generic uniform-limit block ----------------------------------------
S['uhps'] = '( ( %s /\\ N e. NN ) -> ( %s ` N ) = %s )' % (FMAP('F'), PS, PSMAP('F', 'N'))
S['uhpsf'] = '( %s -> %s : NN --> ( CC ^m U ) )' % (FMAP('F'), PS)
S['uhmt'] = '( %s -> %s e. dom ( ~~>u ` U ) )' % (UHS(), PS)
S['uhcvg'] = '( ( %s /\\ Z e. U ) -> seq 1 ( + , ( h e. NN |-> ( ( F ` h ) ` Z ) ) ) e. dom ~~> )' % UHS()
S['uhcl'] = '( ( %s /\\ Z e. U ) -> sum_ k e. NN ( ( F ` k ) ` Z ) e. CC )' % UHS()
S['uhf'] = '( %s -> %s : U --> CC )' % (UHS(), G)
S['uhptl'] = '( ( %s /\\ w e. U ) -> ( i e. NN |-> ( ( %s ` i ) ` w ) ) ~~> ( %s ` w ) )' % (UHS(), PS, G)
S['uhlimv'] = '( ( %s /\\ w e. U ) -> ( ( ( ~~>u ` U ) ` %s ) ` w ) = sum_ k e. NN ( ( F ` k ) ` w ) )' % (UHS(), PS)
S['uhlim'] = '( %s -> %s ( ~~>u ` U ) %s )' % (UHS(), PS, G)
S['uhdf'] = '( %s -> %s )' % (UH(), UHS(DF(), 'R'))
S['uhdps'] = '( ( %s /\\ N e. NN ) -> ( CC _D ( %s ` N ) ) = ( %s ` N ) )' % (UH(), PS, PSD)
S['uhdv'] = '( %s -> ( CC _D %s ) = %s )' % (UH(), G, H)
S['uhhol'] = '( %s -> %s )' % (UH(), HOLG2(G, 'U'))
# ---- the Dirichlet instance -------------------------------------------------
S['cxpnegdv'] = '( ( K e. RR+ /\\ U e. %s ) -> ( CC _D ( z e. U |-> ( K ^c -u z ) ) ) = ( z e. U |-> -u ( ( log ` K ) x. ( K ^c -u z ) ) ) )' % TOP
S['dsqfv'] = '( K e. NN -> ( %s ` K ) = ( z e. %s |-> %s ) )' % (SQF(), HP(), TRM('A', 'K', 'z'))
S['dsqfvv'] = '( ( K e. NN /\\ Z e. %s ) -> ( ( %s ` K ) ` Z ) = %s )' % (HP(), SQF(), TRM('A', 'K', 'Z'))
S['dsqff'] = '( A : NN --> CC -> %s : NN --> ( CC ^m %s ) )' % (SQF(), HP())
S['dsertdv'] = '( ( A : NN --> CC /\\ K e. NN ) -> ( CC _D ( z e. %s |-> %s ) ) = ( z e. %s |-> -u %s ) )' % (
    HP(), TRM('A', 'K', 'z'), HP(), LTRM('A', 'K', 'z'))
S['dserthol'] = '( ( A : NN --> CC /\\ K e. NN ) -> %s )' % HOLG2('( z e. %s |-> %s )' % (HP(), TRM('A', 'K', 'z')), HP())
S['dsertdvb'] = '( ( %s /\\ ( K e. NN /\\ Z e. %s ) ) -> ( abs ` -u %s ) <_ ( ( C / %s ) x. ( K ^c -u ( T - %s ) ) ) )' % (
    HYP, HP(), LTRM('A', 'K', 'Z'), E, E)
S['dseruh'] = '( %s -> %s )' % (HYP, UH(SQF(), MAJ, MAJD, HP()))
S['dsergeq'] = '%s = %s' % (GSUM(SQF(), HP()), LSF())
S['dserhol'] = '( %s -> %s )' % (HYP, HOLG2(LSF(), HP()))
S['dserdv'] = '( %s -> ( CC _D %s ) = %s )' % (HYP, LSF(), DSF())
S['dserval'] = '( Z e. %s -> ( %s ` Z ) = sum_ k e. NN %s )' % (HP(), LSF(), TRM('A', 'k', 'Z'))
S['dserdvval'] = '( ( %s /\\ Z e. %s ) -> ( ( CC _D %s ) ` Z ) = -u sum_ k e. NN %s )' % (HYP, HP(), LSF(), LTRM('A', 'k', 'Z'))
S['dserdvbnd'] = '( ( %s /\\ ( Z e. %s /\\ E e. RR+ /\\ ( 1 + E ) < %s ) ) -> ( abs ` ( ( CC _D %s ) ` Z ) ) <_ ( ( C / E ) x. ( 1 + ( 1 / ( ( %s - E ) - 1 ) ) ) ) )' % (
    HYP, HP(), RZ, LSF(), RZ)
LCH = '( z e. %s |-> sum_ k e. NN ( %s x. ( k ^c -u z ) ) )' % (HP(), CHV('k'))
S['lchrhol'] = '( ( ( N e. NN /\\ X e. %s ) /\\ ( T e. RR /\\ 1 < T ) ) -> %s )' % (DC, HOLG2(LCH, HP()))
# ---- the character partial sums ---------------------------------------------
S['chrtrl'] = '( ( N e. NN /\\ J e. ZZ /\\ K e. ZZ ) -> ( %s ` ( J + K ) ) = ( ( %s ` J ) %s ( %s ` K ) ) )' % (LH, LH, PG, LH)
S['chrblk'] = '( ( %s /\\ J e. NN0 ) -> sum_ i e. ( ( J + 1 ) ... ( J + N ) ) %s = 0 )' % (CHR, CHV('i'))
S['chrsper'] = '( ( %s /\\ J e. NN0 ) -> %s = %s )' % (CHR, CSUM('( J + N )'), CSUM('J'))
S['chrsmod'] = '( ( %s /\\ ( P e. NN0 /\\ Q e. NN0 ) ) -> %s = %s )' % (CHR, CSUM('( P + ( N x. Q ) )'), CSUM('P'))
S['chrsbnd'] = '( ( %s /\\ M e. NN0 ) -> ( abs ` %s ) <_ N )' % (CHR, CSUM('M'))
S['lchrcsf'] = '( %s -> ( %s : NN --> CC /\\ N e. RR /\\ A. m e. NN ( abs ` ( %s ` m ) ) <_ N ) )' % (CHR, CSF(), CSF())
# ---- the agreement on Re > 1 --------------------------------------------------
ZP1 = '( Z e. CC /\\ 1 < %s )' % RZ
S['abagr1'] = '( ( %s /\\ %s ) -> ( n e. NN |-> ( ( S ` ( n + 1 ) ) x. ( ( n + 1 ) ^c -u Z ) ) ) ~~> 0 )' % (ABS, ZP1)
S['abagr2'] = '( ( ( A : NN --> CC /\\ Z e. CC ) /\\ N e. NN ) -> sum_ k e. ( 1 ... ( N + 1 ) ) %s = ( ( ( %s ` ( N + 1 ) ) x. ( ( N + 1 ) ^c -u Z ) ) + sum_ k e. ( 1 ... N ) %s ) )' % (
    TRM('A', 'k', 'Z'), PSF(), ATM(PSF(), 'k', 'Z'))
ABSP = '( B e. RR /\\ A. m e. NN ( abs ` %s ) <_ B )' % PSUM('A', 'm')
S['abagr'] = '( ( ( %s /\\ %s ) /\\ %s ) -> sum_ k e. NN %s = sum_ k e. NN %s )' % (CFB, ZP1, ABSP, ATMS('A', 'k', 'Z'), TRM('A', 'k', 'Z'))
CATM = '( %s x. ( ( k ^c -u Z ) - ( ( k + 1 ) ^c -u Z ) ) )' % CSUM('k')
S['lchragr'] = '( ( %s /\\ %s ) -> sum_ k e. NN %s = sum_ k e. NN ( %s x. ( k ^c -u Z ) ) )' % (CHR, ZP1, CATM, CHV('k'))
S['lchrab'] = '( ( %s /\\ ( Z e. CC /\\ 0 < %s ) ) -> ( abs ` sum_ k e. NN %s ) <_ ( ( N x. ( abs ` Z ) ) x. ( 1 + ( 1 / %s ) ) ) )' % (CHR, RZ, CATM, RZ)
S['lchrab4'] = '( ( %s /\\ ( Z e. CC /\\ ( 1 / 4 ) <_ %s ) ) -> ( abs ` sum_ k e. NN %s ) <_ ( ( 5 x. N ) x. ( 2 + ( abs ` Z ) ) ) )' % (CHR, RZ, CATM)
# ---- holomorphy of the Abel series --------------------------------------------
S['elbx'] = '( ( L e. RR /\\ R e. RR ) -> ( Z e. %s <-> ( Z e. CC /\\ ( L < %s /\\ %s < R ) /\\ ( -u R < ( Im ` Z ) /\\ ( Im ` Z ) < R ) ) ) )' % (BX(), RZ, RZ)
S['bxopn'] = '%s e. %s' % (BX(), TOP)
S['bxabs'] = '( ( ( L e. RR /\\ 0 <_ L /\\ R e. RR ) /\\ Z e. %s ) -> ( abs ` Z ) <_ ( 2 x. R ) )' % BX()
S['holloc'] = '( ( G : D --> CC /\\ A. y e. D E. u e. %s ( y e. u /\\ u C_ D /\\ u C_ dom ( CC _D ( G |` u ) ) ) ) -> %s )' % (TOP, HOLG2('G', 'D'))
S['lgcxpmvt'] = '( ( ( K e. NN /\\ Z e. CC ) /\\ 0 < %s ) -> ( abs ` ( ( ( log ` K ) x. ( K ^c -u Z ) ) - ( ( log ` ( K + 1 ) ) x. ( ( K + 1 ) ^c -u Z ) ) ) ) <_ ( ( 1 + ( ( abs ` Z ) x. ( log ` ( K + 1 ) ) ) ) x. ( K ^c ( -u %s - 1 ) ) ) )' % (RZ, RZ)
S['logp1bnd'] = '( ( K e. NN /\\ E e. RR+ ) -> ( log ` ( K + 1 ) ) <_ ( ( ( 2 ^c E ) / E ) x. ( K ^c E ) ) )'
S['abtdv'] = '( ( ( S : NN --> CC /\\ K e. NN ) /\\ U e. %s ) -> ( CC _D ( z e. U |-> %s ) ) = ( z e. U |-> %s ) )' % (TOP, ATM('S', 'K', 'z'), DAT('S', 'K', 'z'))
S['abthol'] = '( ( ( S : NN --> CC /\\ K e. NN ) /\\ U e. %s ) -> %s )' % (TOP, HOLG2('( z e. U |-> %s )' % ATM('S', 'K', 'z'), 'U'))
BXH = '( ( L e. RR+ /\\ R e. RR ) /\\ Z e. %s )' % BX()
S['abtbnd'] = '( ( ( %s /\\ K e. NN ) /\\ %s ) -> ( abs ` %s ) <_ ( ( B x. ( 2 x. R ) ) x. ( K ^c -u ( L + 1 ) ) ) )' % (ABS, BXH, ATM('S', 'K', 'Z'))
EL = '( L / 2 )'
CD = '( B x. ( 1 + ( ( 2 x. R ) x. ( ( 2 ^c %s ) / %s ) ) ) )' % (EL, EL)
S['abtdvb'] = '( ( ( %s /\\ K e. NN ) /\\ %s ) -> ( abs ` %s ) <_ ( %s x. ( K ^c -u ( 1 + %s ) ) ) )' % (ABS, BXH, DAT('S', 'K', 'Z'), CD, EL)
BXA = '( %s /\\ ( L e. RR+ /\\ R e. RR ) )' % ABS
MAJA = '( n e. NN |-> ( ( B x. ( 2 x. R ) ) x. ( n ^c -u ( L + 1 ) ) ) )'
MAJAD = '( n e. NN |-> ( %s x. ( n ^c -u ( 1 + %s ) ) ) )' % (CD, EL)
S['abbxuh'] = '( %s -> %s )' % (BXA, UH(ABF('S', BX()), MAJA, MAJAD, BX()))
S['abbxhol'] = '( %s -> %s )' % (BXA, HOLG2(ASF('S', BX()), BX()))
S['abhol'] = '( ( %s /\\ ( T e. RR /\\ 0 <_ T ) ) -> %s )' % (ABS, HOLG2(ASF('S', HP()), HP()))
CATMZ = '( %s x. ( ( k ^c -u z ) - ( ( k + 1 ) ^c -u z ) ) )' % CSUM('k')
S['lchrhol0'] = '( ( %s /\\ ( T e. RR /\\ 0 <_ T ) ) -> %s )' % (CHR, HOLG2('( z e. %s |-> sum_ k e. NN %s )' % (HP(), CATMZ), HP()))

ORDER = list(S)


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'c5gc'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'c5gc', 'c5gc.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=c5gc  LOC_AFTER=?\n\n* grammar check of the frozen statements of C5\n\n')
        for i, lab in enumerate(ORDER, 1):
            f.write('%d:: |- %s\n' % (i, S[lab]))
        f.write('qed:: |- ( 1 = 1 -> 1 = 1 )\n$)\n')
    ok, text = _MM.run_mmj2(path)
    bad = [l for l in text.split('\n') if 'grammatical' in l or 'E-PA-0' in l and 'parse' in l.lower()]
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
