"""Sortie ZL3c helpers: section C (QBND at the symmetric Gamma ratio) and section B
(Euler's integral) of ZL3-blueprint.md.  STATEMENTS / ORDER are this sortie's frozen
statements (headlines zl3qbnd, zl3eul verbatim from tools/zl3lib.py).
`MM_DB=sorties/zl3c.mm python3 tools/zl3clib.py [LABEL...]` grammar-checks them with mmatch."""
import sys, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
import zl3lib as ZL3

STATEMENTS = {}
HYPS = {}
ORDER = []


def st(label, text, hyps=()):
    STATEMENTS[label] = ' '.join(text.split())
    HYPS[label] = list(hyps)
    ORDER.append(label)


# ------------------------------------------------------------------ objects
def EUT(Z):
    return '( m e. NN |-> ( ( ( ( m + 1 ) / m ) ^c %s ) / ( ( %s / m ) + 1 ) ) )' % (Z, Z)


HZV = ('( ( Z e. CC /\\ V e. CC ) /\\ ( ( abs ` ( Im ` Z ) ) = ( abs ` ( Im ` V ) ) /\\ '
       '0 < ( Re ` Z ) /\\ ( Re ` Z ) <_ ( Re ` V ) ) )')
DQ = "( `' Re \" ( -u 1 (,) 1 ) )"                       # the open strip -1 < Re < 1
SQ = "( `' Re \" ( -u ( 1 / 2 ) [,] ( 1 / 2 ) ) )"       # the closed strip of the interpolation
PP = '( P e. RR /\\ 0 <_ P )'
PP1 = '( P e. RR /\\ 0 <_ P /\\ P <_ 1 )'
QQP = ZL3.QQ('P')


def FLB(w):
    """the symmetric ratio with 1/_G ( u ) written u / Gamma ( u + 1 ), u = ( w + P ) / 2"""
    return ('( ( _pi ^c ( %s - ( 1 / 2 ) ) ) x. ( ( _G ` ( ( ( 1 - %s ) + P ) / 2 ) ) x. '
            '( ( ( %s + P ) / 2 ) / ( _G ` ( ( ( %s + P ) / 2 ) + 1 ) ) ) ) )' % (w, w, w, w))


FL = '( w e. %s |-> %s )' % (DQ, FLB('w'))
HOLF = lambda F, D: '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (F, D, D, F)

# ------------------------------------------------------------------ section C
st('zl3rab', '( ( ( A e. CC /\\ B e. CC ) /\\ ( ( abs ` ( Im ` A ) ) = ( abs ` ( Im ` B ) ) /\\ 0 < ( Re ` A ) /\\ '
   '( Re ` A ) <_ ( Re ` B ) ) ) -> ( ( Re ` A ) x. ( abs ` B ) ) <_ ( ( Re ` B ) x. ( abs ` A ) ) )')
st('zl3eutc', '( ( %s /\\ M e. NN ) -> ( ( abs ` ( %s ` M ) ) x. ( %s ` M ) ) <_ ( ( abs ` ( %s ` M ) ) x. ( %s ` M ) ) )'
   % (HZV, EUT('Z'), EUT('( Re ` V )'), EUT('V'), EUT('( Re ` Z )')))
SEQ = lambda Z, N: '( seq 1 ( x. , %s ) ` %s )' % (EUT(Z), N)
st('zl3gseq', '( ( %s /\\ N e. NN ) -> ( ( abs ` %s ) x. %s ) <_ ( ( abs ` %s ) x. %s ) )'
   % (HZV, SEQ('Z', 'N'), SEQ('( Re ` V )', 'N'), SEQ('V', 'N'), SEQ('( Re ` Z )', 'N')))
st('zl3gmono', '( %s -> ( ( abs ` ( _G ` Z ) ) x. ( _G ` ( Re ` V ) ) ) <_ ( ( abs ` ( _G ` V ) ) x. ( _G ` ( Re ` Z ) ) ) )' % HZV)
st('zl3grat', 'E. d e. RR+ A. p e. ( ( 1 / ; ; 1 0 0 ) [,] 3 ) A. q e. ( ( 1 / ; ; 1 0 0 ) [,] 3 ) ( _G ` p ) <_ ( d x. ( _G ` q ) )')
st('zl3igp1', '( ( U e. CC /\\ -u 1 < ( Re ` U ) ) -> ( 1/_G ` U ) = ( U / ( _G ` ( U + 1 ) ) ) )')
st('zl3haff', '( ( ( A e. CC /\\ B e. CC ) /\\ D e. ( TopOpen ` CCfld ) ) -> %s )' % HOLF('( z e. D |-> ( ( A x. z ) + B ) )', 'D'))
st('zl3hco', '( ( %s /\\ %s /\\ A. v e. D ( G ` v ) e. E ) -> %s )'
   % (HOLF('F', 'E'), HOLF('G', 'D'), HOLF('( z e. D |-> ( F ` ( G ` z ) ) )', 'D')))
st('zl3qhol', '( %s -> %s )' % (PP, HOLF(FL, DQ)))
st('zl3qv', '( ( %s /\\ ( Z e. CC /\\ -u 1 < ( Re ` Z ) /\\ ( Re ` Z ) < 1 ) ) -> ( ( %s ` Z ) = ( %s ` Z ) /\\ ( %s ` Z ) e. CC ) )'
   % (PP, QQP, FL, FL))
st('zl3qey', '( ( %s /\\ ( Z e. CC /\\ ( Re ` Z ) = ( 1 / 2 ) ) ) -> ( abs ` ( %s ` Z ) ) <_ 1 )' % (PP, FL))
st('zl3qex', '( ( %s /\\ ( Z e. CC /\\ ( Re ` Z ) = -u ( 1 / 2 ) ) ) -> ( abs ` ( %s ` Z ) ) <_ ( ( abs ` ( Im ` Z ) ) + 2 ) )' % (PP1, FL))
I100 = '( ( 1 / ; ; 1 0 0 ) [,] 3 )'
st('zl3qgb', '( ( ( %s /\\ ( D e. RR+ /\\ A. p e. %s A. q e. %s ( _G ` p ) <_ ( D x. ( _G ` q ) ) ) ) /\\ '
   '( Z e. CC /\\ -u ( 1 / 2 ) <_ ( Re ` Z ) /\\ ( Re ` Z ) <_ ( 1 / 2 ) ) ) -> '
   '( abs ` ( %s ` Z ) ) <_ ( ( 2 x. D ) x. ( exp ` ( 1 x. ( abs ` ( Im ` Z ) ) ) ) ) )' % (PP1, I100, I100, FL))
st('zl3qgr', '( %s -> E. k e. RR+ A. z e. %s ( abs ` ( %s ` z ) ) <_ ( k x. ( exp ` ( 1 x. ( abs ` ( Im ` z ) ) ) ) ) )' % (PP1, SQ, FL))
GRW = lambda F, S: ('( ( K e. RR+ /\\ B e. RR /\\ 0 <_ B ) /\\ A. z e. %s ( abs ` ( %s ` z ) ) <_ '
                    '( K x. ( exp ` ( B x. ( abs ` ( Im ` z ) ) ) ) ) )' % (S, F))
st('zl3gint', '( ( ( ( ( F e. ( D -cn-> CC ) /\\ D C_ dom ( CC _D F ) /\\ %s C_ D ) /\\ %s ) /\\ '
   '( A. z e. CC ( ( Re ` z ) = -u ( 1 / 2 ) -> ( abs ` ( F ` z ) ) <_ ( ( abs ` ( Im ` z ) ) + 2 ) ) /\\ '
   'A. z e. CC ( ( Re ` z ) = ( 1 / 2 ) -> ( abs ` ( F ` z ) ) <_ 1 ) ) ) /\\ '
   '( W e. CC /\\ ( -u ( 1 / 2 ) <_ ( Re ` W ) /\\ ( Re ` W ) <_ ( 1 / 2 ) ) ) ) -> '
   '( abs ` ( F ` W ) ) <_ ( 9 x. ( ( ( abs ` ( Im ` W ) ) + 2 ) ^c ( ( 1 / 2 ) - ( Re ` W ) ) ) ) )' % (SQ, GRW('F', SQ)))
st('zl3qbnd', ZL3.STATEMENTS['zl3qbnd'])

# ------------------------------------------------------------------ section B
st('zl3cx0', '( ( A e. CC /\\ 0 < ( Re ` A ) ) -> ( x e. ( 0 [,) +oo ) |-> ( x ^c A ) ) e. ( ( 0 [,) +oo ) -cn-> CC ) )')
st('zl3dvi', '( ( ( A e. RR /\\ B e. RR ) /\\ F : ( A [,] B ) --> CC ) -> ( RR _D F ) = ( RR _D ( F |` ( A (,) B ) ) ) )')
st('zl3dvc', '( ( ( W e. CC /\\ W =/= 0 ) /\\ N e. RR+ ) -> ( RR _D ( x e. ( 0 [,] N ) |-> ( ( x ^c W ) / W ) ) ) = ( x e. ( 0 (,) N ) |-> ( x ^c ( W - 1 ) ) ) )')
st('zl3ccx', '( ( ( A e. CC /\\ 0 < ( Re ` A ) ) /\\ N e. RR+ ) -> ( x e. ( 0 [,] N ) |-> ( x ^c A ) ) e. ( ( 0 [,] N ) -cn-> CC ) )')
st('zl3ibl', '( ( ( A e. RR /\\ B e. RR ) /\\ F e. ( ( A [,] B ) -cn-> CC ) ) -> ( F |` ( A (,) B ) ) e. L^1 )')
HW1 = '( ( W e. CC /\\ 1 < ( Re ` W ) ) /\\ N e. RR+ )'
st('zl3pint', '( %s -> S. ( 0 (,) N ) ( x ^c ( W - 1 ) ) _d x = ( ( N ^c W ) / W ) )' % HW1)
st('zl3dvp', '( ( N e. RR+ /\\ M e. NN ) -> ( RR _D ( x e. ( 0 [,] N ) |-> ( ( 1 - ( x / N ) ) ^ M ) ) ) = ( x e. ( 0 (,) N ) |-> ( -u ( M / N ) x. ( ( 1 - ( x / N ) ) ^ ( M - 1 ) ) ) ) )')
def JN(N, K, Wv):
    return 'S. ( 0 (,) %s ) ( ( ( 1 - ( x / %s ) ) ^ %s ) x. ( x ^c ( %s - 1 ) ) ) _d x' % (N, N, K, Wv)
HWK = '( ( W e. CC /\\ 1 < ( Re ` W ) ) /\\ ( N e. RR+ /\\ K e. NN0 ) )'
st('zl3jrec', '( %s -> %s = ( ( ( K + 1 ) / ( N x. W ) ) x. %s ) )' % (HWK, JN('N', '( K + 1 )', 'W'), JN('N', 'K', '( W + 1 )')))
st('zl3rfl', '( ( A e. CC /\\ K e. NN0 ) -> ( A RiseFac ( K + 1 ) ) = ( A x. ( ( A + 1 ) RiseFac K ) ) )')
st('zl3jn', '( ( N e. RR+ /\\ K e. NN0 ) -> A. w e. CC ( 1 < ( Re ` w ) -> ( %s x. ( w RiseFac ( K + 1 ) ) ) = ( ( ! ` K ) x. ( N ^c w ) ) ) )' % JN('N', 'K', 'w'))
st('zl3gpk', '( ( ( W e. CC /\\ 0 < ( Re ` W ) ) /\\ K e. NN ) -> ( ( seq 1 ( x. , %s ) ` K ) x. ( ( W + 1 ) RiseFac K ) ) = ( ( ( K + 1 ) ^c W ) x. ( ! ` K ) ) )' % EUT('W'))
SQW = lambda n: '( seq 1 ( x. , %s ) ` %s )' % (EUT('W'), n)
st('zl3qid', '( ( ( W e. CC /\\ 1 < ( Re ` W ) ) /\\ K e. NN ) -> %s = ( ( 1 / W ) x. ( %s x. ( 1 / ( ( W / ( K + 1 ) ) + 1 ) ) ) ) )'
   % (JN('( K + 1 )', '( K + 1 )', 'W'), SQW('K')))
st('zl3crec', '( ( G ~~> A /\\ A e. ( CC \\ { 0 } ) /\\ A. j e. NN ( G ` j ) e. ( CC \\ { 0 } ) ) -> ( n e. NN |-> ( 1 / ( G ` n ) ) ) ~~> ( 1 / A ) )')
st('zl3qlim', '( ( W e. CC /\\ 1 < ( Re ` W ) ) -> ( k e. NN |-> %s ) ~~> ( _G ` W ) )' % JN('( k + 1 )', '( k + 1 )', 'W'))
APN = '( ( 1 - ( U / N ) ) ^ N )'
st('zl3ebd', '( ( N e. NN /\\ ( U e. RR /\\ 0 <_ U /\\ U <_ N ) ) -> ( ( 0 <_ %s /\\ %s <_ ( exp ` -u U ) ) /\\ ( ( exp ` -u U ) - %s ) <_ ( ( ( U ^ 2 ) x. ( exp ` -u U ) ) / N ) ) )' % (APN, APN, APN))
st('zl3pwe', '( ( ( C e. RR /\\ 0 <_ C ) /\\ X e. RR+ ) -> ( X ^c C ) <_ ( ( ( 2 x. ( C + 1 ) ) ^c C ) x. ( exp ` ( X / 2 ) ) ) )')
st('zl3iex', '( ( A e. RR /\\ B e. RR /\\ A <_ B ) -> S. ( A (,) B ) ( exp ` -u ( x / 2 ) ) _d x = ( 2 x. ( ( exp ` -u ( A / 2 ) ) - ( exp ` -u ( B / 2 ) ) ) ) )')
KA = '( ( 2 x. ( ( ( Re ` W ) + 1 ) + 1 ) ) ^c ( ( Re ` W ) + 1 ) )'
KB = '( ( 2 x. ( ( ( Re ` W ) - 1 ) + 1 ) ) ^c ( ( Re ` W ) - 1 ) )'
HW = '( W e. CC /\\ 1 < ( Re ` W ) )'
st('zl3erp', '( ( %s /\\ ( N e. NN /\\ X e. ( 0 (,) N ) ) ) -> ( abs ` ( ( ( exp ` -u X ) - ( ( 1 - ( X / N ) ) ^ N ) ) x. ( X ^c ( W - 1 ) ) ) ) <_ ( ( %s / N ) x. ( exp ` -u ( X / 2 ) ) ) )' % (HW, KA))
st('zl3tlp', '( ( %s /\\ X e. RR+ ) -> ( abs ` ( ( exp ` -u X ) x. ( X ^c ( W - 1 ) ) ) ) <_ ( %s x. ( exp ` -u ( X / 2 ) ) ) )' % (HW, KB))
EIF = lambda a, b: 'S. ( %s (,) %s ) ( ( exp ` -u x ) x. ( x ^c ( W - 1 ) ) ) _d x' % (a, b)
st('zl3err', '( ( %s /\\ N e. NN ) -> ( abs ` ( %s - %s ) ) <_ ( ( 2 x. %s ) / N ) )' % (HW, EIF('0', 'N'), JN('N', 'N', 'W'), KA))
st('zl3tail', '( ( %s /\\ ( A e. RR+ /\\ B e. RR /\\ A <_ B ) ) -> ( abs ` %s ) <_ ( ( 2 x. %s ) x. ( exp ` -u ( A / 2 ) ) ) )' % (HW, EIF('A', 'B'), KB))
KK = '( ( 2 x. %s ) + ( 4 x. %s ) )' % (KA, KB)
FLT = '( |_ ` T )'
st('zl3eub', '( ( %s /\\ ( T e. RR /\\ 2 <_ T ) ) -> ( abs ` ( %s - ( _G ` W ) ) ) <_ ( ( abs ` ( %s - ( _G ` W ) ) ) + ( %s / %s ) ) )' % (HW, EIF('0', 'T'), JN(FLT, FLT, 'W'), KK, FLT))
st('zl3esq', '( %s -> ( n e. ( ZZ>= ` 2 ) |-> ( ( abs ` ( %s - ( _G ` W ) ) ) + ( %s / n ) ) ) ~~> 0 )' % (HW, JN('n', 'n', 'W'), KK))
st('zl3icc', '( ( %s /\\ T e. RR+ ) -> %s e. CC )' % (HW, EIF('0', 'T')))
st('zl3jcc', '( ( %s /\\ N e. NN ) -> %s e. CC )' % (HW, JN('N', 'N', 'W')))
EI1 = '( t e. RR+ |-> %s )' % EIF('0', 't')
st('zl3eu1', '( %s -> %s ~~>r ( _G ` W ) )' % (HW, EI1))
EIL = lambda b: 'S. ( 0 (,) %s ) ( ( exp ` -u ( L x. x ) ) x. ( x ^c ( W - 1 ) ) ) _d x' % b
st('zl3esc', '( ( %s /\\ ( L e. RR+ /\\ T e. RR+ ) ) -> %s = ( ( L ^c -u W ) x. %s ) )' % (HW, EIL('T'), EIF('0', '( L x. T )')))
st('zl3eul', ZL3.STATEMENTS['zl3eul'])


def gramcheck(labels):
    out = {}
    wsdir = 'worksheets'
    for lab in labels:
        p = os.path.join(wsdir, 'zl3cg_%s.mmp' % lab)
        with open(p, 'w') as f:
            f.write('$( <MM> <PROOF_ASST> THEOREM=zl3cg_%s  LOC_AFTER=?\n\n* grammar check\n\n' % lab)
            for n, h in HYPS.get(lab, []):
                f.write('%s::? |- %s\n' % (n, h))
            f.write('qed::ax-1 |- %s\n$)\n' % STATEMENTS[lab])
        env = dict(os.environ, MM_ENGINE='mmatch')
        r = subprocess.run([sys.executable, 'tools/mm.py', 'unify', p], capture_output=True, text=True, env=env)
        txt = r.stdout + r.stderr
        out[lab] = [l for l in txt.split('\n') if 'grammar' in l.lower()]
        os.remove(p)
    return out


if __name__ == '__main__':
    r = gramcheck(sys.argv[1:] or ORDER)
    for lab, bad in r.items():
        print(lab, 'OK' if not bad else 'FAIL')
        for l in bad:
            print('   ', l[:300])
