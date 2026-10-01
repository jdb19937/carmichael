"""C9: the frozen statements, grammar-checked through mmj2.

    MM_DB=sorties/c9.mm python3 tools/gen/c9_freeze.py         # grammar check
    MM_DB=sorties/c9.mm python3 tools/gen/c9_freeze.py print   # the table
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c9lib import *
import mm as _MM

S = {}
SQT = SQ('C', 'T')
AV, BV = SQA('C', 'V'), SQB('C', 'V')
S['sqfrd'] = ('( ( ( C e. CC /\\ ( T e. RR /\\ R e. RR+ /\\ V e. RR ) ) /\\ ( ( T + R ) <_ V /\\ U e. %s ) ) -> '
              '( %s /\\ A. u e. %s R <_ ( abs ` ( u - U ) ) ) )') % (SQT, INTG(AV, BV, 'U'), FRG(AV, BV))
PH0 = '( S e. Fin /\\ S C_ CC /\\ O : S --> NN0 )'
PRU = '( abs ` %s )' % PRZ('S', 'U')
EXS = '( exp ` ( %s x. ( log ` R ) ) )' % NSUM('S')
S['fprodlbe'] = '( ( %s /\\ ( U e. CC /\\ R e. RR+ /\\ A. j e. S R <_ ( abs ` ( U - j ) ) ) ) -> %s <_ %s )' % (PH0, EXS, PRU)
S['fprodube'] = '( ( %s /\\ ( U e. CC /\\ R e. RR+ /\\ A. j e. S ( abs ` ( U - j ) ) <_ R ) ) -> %s <_ %s )' % (PH0, PRU, EXS)
FACD = 'A. v e. D ( F ` v ) = ( %s x. ( H ` v ) )' % PRZ('Z', 'v', q='k')
S['holzord'] = ('( ( ( %s /\\ ( Z e. Fin /\\ Z C_ D ) ) /\\ ( ( O : Z --> NN /\\ %s ) /\\ ( %s /\\ A. v e. Z ( H ` v ) =/= 0 ) ) /\\ P e. Z ) '
                '-> ( O ` P ) = ( F holord P ) )') % (HOL, HOLG('H', 'D'), FACD)
S['lndhbd'] = '( ( ( %s /\\ %s ) /\\ Y e. %s ) -> ( abs ` ( H ` Y ) ) <_ ( B / %s ) )' % (DATA, FBD, SQ138, EXPL('Z', R18))
LGH = lambda t: '( log ` ( abs ` ( H ` %s ) ) )' % t
S['lndhre'] = ('( ( ( %s /\\ %s ) /\\ ( ( F ` C ) =/= 0 /\\ ( W e. RR /\\ %s <_ W ) ) ) -> '
               'A. y e. %s ( %s - %s ) <_ %s )') % (DATA, FBD, NSUM('Z'), SQ138, LGH('y'), LGH('C'), LOGM)
ZS_ = ZSQ()
S['lndgen'] = ('( ( ( %s /\\ ( C e. CC /\\ %s C_ D ) ) /\\ ( %s /\\ ( ( F ` C ) =/= 0 /\\ ( W e. RR+ /\\ sum_ q e. %s ( F holord q ) <_ W ) ) ) '
               '/\\ ( S e. CC /\\ ( abs ` ( S - C ) ) <_ ( 3 / 2 ) /\\ ( F ` S ) =/= 0 ) ) -> '
               '( abs ` ( ( ( ( CC _D F ) ` S ) / ( F ` S ) ) - sum_ q e. %s ( ( F holord q ) / ( S - q ) ) ) ) <_ ( %s x. %s ) )') % (
    HOL, SQ74, FBD, ZS_, ZS_, K6N, LOGM)

S['sqhp0'] = '( ( ( C e. CC /\\ R e. RR ) /\\ R < ( Re ` C ) ) -> %s C_ %s )' % (SQ('C', 'R'), HP0)
S['lchrsqb'] = '( ( ( %s /\\ T e. RR ) /\\ U e. %s ) -> ( abs ` ( %s ` U ) ) <_ %s )' % (CHI, SQ(C0, R74), LFN, B20)
ZSL = '{ r e. %s | ( %s ` r ) = 0 }' % (SQ(C0, R138), LFN)
S['lndlchr'] = ('( ( ( %s /\\ ( T e. RR /\\ ( W e. RR+ /\\ sum_ q e. %s ( %s holord q ) <_ W ) ) ) /\\ ( S e. CC /\\ ( abs ` ( S - %s ) ) <_ ( 3 / 2 ) /\\ ( %s ` S ) =/= 0 ) ) -> '
                '( abs ` ( ( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) - sum_ q e. %s ( ( %s holord q ) / ( S - q ) ) ) ) <_ ( %s x. ( ( log ` ( %s / ( abs ` ( %s ` %s ) ) ) ) + ( W x. ( log ` ; 2 6 ) ) ) ) )') % (
    CHI, ZSL, LFN, C0, LFN, LFN, LFN, ZSL, LFN, K6N, B20, LFN, C0)

ORDER = list(S)


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'c9gc'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'c9gc', 'c9gc.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=c9gc  LOC_AFTER=?\n\n* grammar check of the frozen statements of C9\n\n')
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
            print(t[-3000:])
