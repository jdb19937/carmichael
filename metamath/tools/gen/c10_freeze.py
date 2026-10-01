"""C10: the frozen statements, grammar-checked through mmj2.

    MM_DB=sorties/c10.mm python3 tools/gen/c10_freeze.py         # grammar check
    MM_DB=sorties/c10.mm python3 tools/gen/c10_freeze.py print   # the table
"""
import sys, os, re
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c10lib import *
import mm as _MM

S = {}
S['blfr'] = ('( ( ( C e. CC /\\ R e. RR+ ) /\\ ( Q e. CC /\\ ( abs ` ( Q - C ) ) <_ R ) /\\ ( U e. CC /\\ R <_ ( abs ` ( U - C ) ) ) ) '
             '-> ( abs ` %s ) <_ ( abs ` ( U - Q ) ) )') % BLF('Q', 'U')
S['blent'] = '( ( ( Z e. Fin /\\ Z C_ CC /\\ O : Z --> NN ) /\\ ( C e. CC /\\ R e. RR+ ) ) -> %s )' % ENT('( s e. CC |-> %s )' % PBL('s'))
JX1 = '( ( %s /\\ ( Z e. Fin /\\ Z C_ D ) ) /\\ ( ( O : Z --> NN /\\ %s ) /\\ %s ) )' % (HOL, HOLG('H', 'D'), FACQ)
JX2 = '( ( C e. CC /\\ R e. RR+ /\\ %s C_ D ) /\\ ( V e. RR+ /\\ V <_ R /\\ A. j e. Z ( abs ` ( C - j ) ) <_ V ) )' % SQ('C', 'R')
JX3 = '( ( B e. RR /\\ A. u e. %s ( abs ` ( F ` u ) ) <_ B ) /\\ ( F ` C ) =/= 0 )' % FRM('C', 'R')
S['jenbl'] = '( ( %s /\\ %s /\\ %s ) -> ( %s x. ( log ` ( R / V ) ) ) <_ ( log ` ( B / ( abs ` ( F ` C ) ) ) ) )' % (
    JX1, JX2, JX3, NSUM('Z'))
AM, BM = '( A - ( M + ( _i x. M ) ) )', '( B + ( M + ( _i x. M ) ) )'
ZR = '{ r e. ( A crect B ) | ( F ` r ) = 0 }'
RX1 = '( %s /\\ ( ( A e. CC /\\ B e. CC ) /\\ %s ) /\\ ( M e. RR+ /\\ ( %s crect %s ) C_ D ) )' % (HOL, GEOG('A', 'B'), AM, BM)
RX2 = ('( ( C e. ( A crect B ) /\\ ( F ` C ) =/= 0 ) /\\ ( R e. RR+ /\\ %s C_ D ) /\\ '
       '( V e. RR+ /\\ V <_ R /\\ A. j e. ( A crect B ) ( abs ` ( C - j ) ) <_ V ) )') % SQ('C', 'R')
RX3 = '( Y e. RR /\\ A. x e. %s ( abs ` ( F ` x ) ) <_ Y )' % SQ('C', 'R')
S['jenrct'] = ('( ( %s /\\ %s /\\ %s ) -> ( %s e. Fin /\\ A. q e. %s ( F holord q ) e. NN /\\ '
               '( sum_ q e. %s ( F holord q ) x. ( log ` ( R / V ) ) ) <_ ( log ` ( Y / ( abs ` ( F ` C ) ) ) ) ) )') % (
    RX1, RX2, RX3, ZR, ZR, ZR)
S['lchrctr'] = '( ( %s /\\ T e. RR ) -> ( 1 / 2 ) <_ ( abs ` ( %s ` %s ) ) )' % (CHI, LFN, C0)
ZQT = ZQ('T')
S['lchrzq'] = ('( ( %s /\\ T e. RR ) -> ( %s e. Fin /\\ A. q e. %s ( %s holord q ) e. NN /\\ '
               '( sum_ q e. %s ( %s holord q ) x. ( log ` %s ) ) <_ ( log ` %s ) ) )') % (CHI, ZQT, ZQT, LFN, ZQT, LFN, R2524, B40)
# fsumunle is in deduction form ($e hypotheses fsumunle.1 .. fsumunle.5, $d ph k)
FSUH = ['( ph -> B e. Fin )', '( ph -> C e. Fin )', '( ph -> A C_ ( B u. C ) )',
        '( ( ph /\\ k e. ( B u. C ) ) -> X e. RR )', '( ( ph /\\ k e. ( B u. C ) ) -> 0 <_ X )']
S['fsumunle'] = '( ph -> sum_ k e. A X <_ ( sum_ k e. B X + sum_ k e. C X ) )'
ZSL = '{ r e. %s | ( %s ` r ) = 0 }' % (SQ(C0, R138), LFN)
W0 = '( ( 4 x. ( log ` %s ) ) / ( log ` %s ) )' % (B80, R2524)
S['lchrzc'] = '( ( %s /\\ T e. RR ) -> ( %s e. Fin /\\ sum_ q e. %s ( %s holord q ) <_ %s ) )' % (CHI, ZSL, ZSL, LFN, W0)
S['lndlchrc'] = ('( ( ( %s /\\ T e. RR ) /\\ ( S e. CC /\\ ( abs ` ( S - %s ) ) <_ ( 3 / 2 ) /\\ ( %s ` S ) =/= 0 ) ) -> '
                 '( abs ` ( ( ( ( CC _D %s ) ` S ) / ( %s ` S ) ) - sum_ q e. %s ( ( %s holord q ) / ( S - q ) ) ) ) <_ ( %s x. ( ( log ` %s ) + ( %s x. ( log ` ; 2 6 ) ) ) ) )') % (
    CHI, C0, LFN, LFN, LFN, ZSL, LFN, K6N, B40, W0)

KNUM = '; ; ; ; ; ; ; 1 7 5 0 0 0 0 0'
S['lndlchrk'] = S['lndlchrc'].rsplit(' <_ ', 1)[0] + ' <_ ( %s x. ( log ` %s ) ) )' % (KNUM, XT)

ORDER = list(S)


def check():
    os.makedirs(os.path.join(ROOT, 'scratch', 'c10gc'), exist_ok=True)
    path = os.path.join(ROOT, 'scratch', 'c10gc', 'c10gc.mmp')
    with open(path, 'w') as f:
        f.write('$( <MM> <PROOF_ASST> THEOREM=c10gc  LOC_AFTER=?\n\n* grammar check of the frozen statements of C10\n\n')
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
