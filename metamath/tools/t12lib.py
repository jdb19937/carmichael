r"""Sortie T12: Step5.lean (inputF, scalesF, verifyF, outputF, failAll, searchF) at the concrete machine.

The installation predicates of Step5.lean's fragments in T10's form (one wff predicate per fragment,
own equations, callees as predicates, the stacks the numerals ` 0 ... 7 ` of the one call in Step5),
compiled from the Lean program text by a copy of T10's compiler (tools/t10lib.py ` frag ` ) extended
with three own statements: ` clear k ` (T9's ~ tm2fclr form), ` moveNum src dst ` (one label, the form of
T7's ` dup ` ) and ` pushNum k c ` at a class ` c ` (the callee ` TMIpnv ` , a label family, ~ tm2fpnw ).
The predicates that depend on Lean's constants ` C1 ` and ` K ` take them as class arguments.
Built on tools/t10lib.py (read-only); T10's and T11's predicates and statements are reused as they are.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t10lib import *
import t10lib as T10
from t7blib import Frag as _Frag

# ------------------------------------------------------------ loads, tests
CEQ = '( u e. TMSt |-> if ( ( TMcmp ` u ) = 1o , 1o , (/) ) )'          # decide ( cmp = .eq )
L_NGT = LSET(fl='if ( ( TMcmp ` u ) = 2o , (/) , 1o )')                 # flag := !decide ( cmp = .gt )
MOVST = lambda src, dst, L, k: POP(src, 'TMrdA', BRANCH(CIS, PUSH(dst, PBR, GT(L)), GT(k)))
CLRST = lambda x, L, k: POP(x, RDE, BRANCH(CNDA, GT(L), GT(k)))


# ------------------------------------------------------------ the fragment compiler (T10's, extended)
def clear(k): return ('clear', k)
def movenum(src, dst): return ('movenum', src, dst)


class _C12(T10._C):
    def name(self, t):
        if t[0] in ('clear', 'movenum'):
            self.n += 1
            L = 'Z%d' % self.n
            self.ent[id(t)] = L
            self.labels.append(L)
            return
        return T10._C.name(self, t)

    def go(self, t, k):
        op = t[0]
        if op == 'clear':
            L = self.ent[id(t)]
            self.eqs.append((L, MEQ(L, CLRST(t[1], L, k))))
            return L
        if op == 'movenum':
            L = self.ent[id(t)]
            self.eqs.append((L, MEQ(L, MOVST(t[1], t[2], L, k))))
            return L
        return T10._C.go(self, t, k)


def frag12(name, const, ks, prog, lean):
    """register the installation predicate of ` prog ` (T10's ` frag ` with the extended compiler)"""
    c = _C12()
    c.name(prog)
    entry = c.go(prog, 'E')
    labels = list(c.labels)
    start = None
    if entry in labels:
        labels.remove(entry)
        labels = [entry] + labels
    else:
        start = entry
    byl = dict(c.eqs)
    progt = grp([byl[l] for l in labels]) if labels else None
    labt = grp([LAB(l) for l in labels] + [LAB('E')]) if labels else None
    f = comp(name, const, ks, labels, 'E', progt, labt, lean, c.children)
    if start is not None:
        f.start = start
    return f


# ------------------------------------------------------------ pushNum at a class: the callee TMIpnv K N T M P E
# labels ( P ` 0 ) ... ( P ` ( ( # W ) + 1 ) ) = E , W = ( encNatGam ` N ) ; the pushes of ~ tm2fpnw
WN_ = '( encNatGam ` N )'
NWN_ = '( ( # ` %s ) + 1 )' % WN_
PNV_EQ = ('A. k e. ( 0 ..^ %s ) ( M ` ( P ` k ) ) = <. 0 , <. K , <. ( ( 2nd ` T ) X. { ( ( <" 4 "> ++ ( reverse ` %s ) ) ` k ) } ) , '
          '<. 5 , ( ( 2nd ` T ) X. { ( P ` ( k + 1 ) ) } ) >. >. >. >.' % (NWN_, WN_))
PNV_RHS = '( ( P : ( 0 ... %s ) --> ( 2nd ` ( 1st ` T ) ) /\\ ( P ` %s ) = E ) /\\ %s )' % (NWN_, NWN_, PNV_EQ)


class _Pnv(_Frag):
    def rhs_tree(self):
        return PNV_RHS

    def rhs(self):
        return PNV_RHS


FRAGS['pnv'] = _Pnv('pnv', 'TMIpnv', ['K', 'N'], ['A'], 'E', None, None,
                    "` pushNum k c = pushTerm k ( encodeNatGamma' c ) ` at a number ` c = N ` : the pushes of "
                    "` ( <\" 4 \"> ++ ( reverse ` ( encNatGam ` N ) ) ) ` in order along the labels ` ( P ` k ) ` , "
                    "the last going to the exit ` E ` = ` ( P ` ( ( # W ) + 1 ) ) ` (Prims.lean)")


def pnv(k, n): return call('pnv', [k, n])


# ------------------------------------------------------------ Lists: moveEntries x y s (stacks K J I), from ~ tm2lmes
import t7c_h_lst as LST
LST.register('mes', 'TMImes', 'tm2lmes', ['K', 'J', 'I'], ['P1', 'A', "A'", 'A"', "B'", 'B"', "Q'", "E'"], [],
             "` moveEntries src dst s = forEntries src ( moveEntry src dst s ) ; popTop src ` "
             "(moveEntry's two moveNum inline; Lists.lean)")

# ------------------------------------------------------------ Step5: output, failure, input
frag12('fal', 'TMIfal', [],
       seq(clear('0'), clear('1'), clear('2'), clear('3'), clear('4'), clear('5'), clear('6'), clear('7'), push('1', '4')),
       "` failAll = clear 0 ; clear 1 ; clear 2 ; clear 3 ; clear 4 ; clear 5 ; clear 6 ; clear 7 ; "
       "pushSym 1 comma ` ( ` clear k ` : one label, ` pop k readEmpty ` then ` branch ( !da ) ( goto self ) ( goto exit ) ` )")
frag12('out', 'TMIout', [],
       seq(clear('0'), clear('1'), clear('2'), clear('3'), clear('5'), clear('6'), call('lrev', N(4, 0, 2)),
           call('mes', N(0, 1, 2)), call('me', N(7, 1, 2)), clear('7'), clear('4')),
       "` outputF = clear 0 ; clear 1 ; clear 2 ; clear 3 ; clear 5 ; clear 6 ; revList 4 0 2 ; moveEntries 0 1 2 ; "
       "moveEntry 7 1 2 ; clear 7 ; clear 4 `")
frag12('inp', 'TMIinp', [],
       seq(push('2', '4'), movenum('0', '2'), push('7', '4'), movenum('2', '7')),
       "` inputF = pushSym 2 comma ; moveNum 0 2 ; pushSym 7 comma ; moveNum 2 7 ` ( ` moveNum src dst ` : one label, "
       "` pop src readA ` then ` branch isSome ( push dst ( bit ra ) ; goto self ) ( goto exit ) ` )")

# ------------------------------------------------------------ Step5: the scales (C = C1 , K = K)
frag12('sclg', 'TMIsclg', [],
       seq(call('bl', N(7, 1, 2, 3)), call('prd', N(1, 2)), call('bl', N(1, 2, 3, 4)), call('prd', N(2, 3)),
           call('bl', N(2, 3, 4, 5)), call('prd', N(3, 4))),
       "` scLogs = bitlen 7 1 2 3 ; predNum 1 2 ; bitlen 1 2 3 4 ; predNum 2 3 ; bitlen 2 3 4 5 ; predNum 3 4 `")
frag12('scth', 'TMIscth', [],
       seq(call('dup', N(1, 4, 5)), call('inc', N(4, 5)), call('bl', N(4, 5, 6, 0)), call('drop', N(4)), pnv('4', '6'),
           call('mulc', N(4, 5, 6, 0, 2)), call('inc', N(6, 0)), call('inc', N(6, 0)), call('inc', N(6, 0)),
           call('inc', N(6, 0)), pnv('4', '5'), call('divc', N(6, 4, 5, 0, 1, 2)), call('p2', N(5, 0, 4, 6))),
       "` scTheta = dup 1 4 5 ; incr 4 5 ; bitlen 4 5 6 0 ; dropNum 4 ; pushNum 4 6 ; mulC 4 5 6 0 2 ; incr 6 0 ; "
       "incr 6 0 ; incr 6 0 ; incr 6 0 ; pushNum 4 5 ; divC 6 4 5 0 1 2 ; pow2 5 0 4 6 `")
frag12('sctt', 'TMIsctt', [],
       seq(pnv('4', '3'), call('dup', N(2, 5, 6)), call('mulc', N(4, 5, 6, 1, 3)), call('me', N(6, 0, 4))),
       "` scT = pushNum 4 3 ; dup 2 5 6 ; mulC 4 5 6 1 3 ; moveEntry 6 0 4 `")
frag12('sczz', 'TMIsczz', ['C'],
       seq(pnv('4', 'C'), call('dup', N(2, 5, 6)), call('mulc', N(4, 5, 6, 1, 3)), call('dup', N(3, 4, 5)),
           call('mulc', N(6, 4, 5, 1, 2)), call('drop', N(1)), call('drop', N(2)), call('drop', N(3))),
       "` scZ C1 = pushNum 4 C1 ; dup 2 5 6 ; mulC 4 5 6 1 3 ; dup 3 4 5 ; mulC 6 4 5 1 2 ; dropNum 1 ; dropNum 2 ; "
       "dropNum 3 ` at ` C1 = C `")
frag12('scbz', 'TMIscbz', [],
       seq(call('bl', N(5, 4, 6, 1)), call('prd', N(4, 6)), call('inc', N(4, 6))),
       "` scBz = bitlen 5 4 6 1 ; predNum 4 6 ; incr 4 6 `")
frag12('scyy', 'TMIscyy', ['K'],
       seq(call('dup', N(4, 6, 1)), call('inc', N(6, 1)), pnv('1', '( K - 1 )'), call('mulc', N(1, 6, 2, 3, 4)),
           pnv('1', 'K'), call('divc', N(2, 1, 3, 6, 4, 5)), call('p2', N(3, 6, 1, 2)), call('me', N(6, 0, 1))),
       "` scY K = dup 4 6 1 ; incr 6 1 ; pushNum 1 ( K - 1 ) ; mulC 1 6 2 3 4 ; divK 2 1 3 6 4 5 K ; "
       "pow2 3 6 1 2 ; moveEntry 6 0 1 ` , ` divK x y q j s t c = pushNum y c ; divC x y q j s t ` for ` c =/= 0 ` "
       "(here ` K e. NN ` )")
frag12('sc99', 'TMIsc99', [],
       seq(call('inc', N(4, 1)), pnv('1', '; 9 9'), call('mulc', N(1, 4, 2, 3, 6)), pnv('1', '; ; 1 0 0'),
           call('divc', N(2, 1, 3, 4, 6, 5)), call('p2', N(3, 6, 1, 2)), call('me', N(6, 0, 1)), call('me', N(5, 0, 1))),
       "` scZ99 = incr 4 1 ; pushNum 1 99 ; mulC 1 4 2 3 6 ; pushNum 1 100 ; divC 2 1 3 4 6 5 ; pow2 3 6 1 2 ; "
       "moveEntry 6 0 1 ; moveEntry 5 0 1 `")
frag12('scal', 'TMIscal', ['C', 'K'],
       seq(call('sclg', []), call('scth', []), call('sctt', []), call('sczz', ['C']), call('scbz', []),
           call('scyy', ['K']), call('sc99', [])),
       "` scalesF C1 K = scLogs ; scTheta ; scT ; scZ C1 ; scBz ; scY K ; scZ99 ` at ` C1 = C `")

# ------------------------------------------------------------ Step5: verify
frag12('aca', 'TMIaca', [], ite('TMfl', SKIP, seq(call('drop', N(1)), pushnum('1', 0))),
       "` accAnd = ite flag skip ( dropNum 1 ; pushNum 1 0 ) `")
frag12('mlb', 'TMImlb', [],
       seq(call('dup', N(5, 3, 2)), call('dup', N(1, 2, 3)), call('cmp', N(3, 2)),
           ite(CEQ, seq(call('drop', N(3)), pushnum('3', 1)), SKIP), call('me', N(5, 6, 2))),
       "` memBody x y s t z = dup x t s ; dup y s t ; cmpFrag t s ; ite ( cmp = .eq ) ( dropNum t ; pushNum t 1 ) skip ; "
       "moveEntry x z s ` at ` x y s t z = 5 1 2 3 6 `")
frag12('mls', 'TMImls', [],
       seq(push('6', '2'), pushnum('3', 0), forentries('5', call('mlb', [])), call('mes', N(6, 5, 2)),
           call('iz', N(3, 2)), load(L_NOTF), call('drop', N(3))),
       "` memList x y s t z = pushSym z bra ; pushNum t 0 ; forEntries x ( memBody x y s t z ) ; moveEntries z x s ; "
       "isZero t s ; load' ( flag := !flag ) ; dropNum t ` at ` x y s t z = 5 1 2 3 6 `")
ACCLOOP = lambda body: seq(pushnum('1', 1), forentries('5', call(body, [])), poptop('5'), call('iz', N(1, 2)),
                           load(L_NOTF), call('drop', N(1)))
ACCLEAN = ("` accLoopF body = pushNum 1 1 ; forEntries 5 body ; popTop 5 ; isZero 1 2 ; load' ( flag := !flag ) ; "
           "dropNum 1 ` ")
frag12('ndb', 'TMIndb', [],
       seq(call('me', N(5, 1, 2)), call('mls', []), call('drop', N(1)), load(L_NOTF), call('aca', [])),
       "` ndBody = moveEntry 5 1 2 ; memList 5 1 2 3 6 ; dropNum 1 ; load' ( flag := !flag ) ; accAnd `")
frag12('nda', 'TMInda', [], ACCLOOP('ndb'), ACCLEAN + "at ` body = ndBody `")
frag12('nd', 'TMInd', [], seq(call('lcpy', N(4, 5, 2, 3)), call('nda', [])),
       "` nodupTDF = copyList 4 5 2 3 ; accLoopF ndBody `")
frag12('apb', 'TMIapb', [], seq(call('ipt', N(5, 2, 3, 6, 0, 1)), call('aca', []), call('drop', N(5))),
       "` apBody = isPrimeTDF 5 2 3 6 0 1 ; accAnd ; dropNum 5 `")
frag12('apa', 'TMIapa', [], ACCLOOP('apb'), ACCLEAN + "at ` body = apBody `")
frag12('ap', 'TMIap', [], seq(call('lcpy', N(4, 5, 2, 3)), call('apa', [])),
       "` allPrimeTDF = copyList 4 5 2 3 ; accLoopF apBody `")
frag12('kot', 'TMIkot', [],
       seq(call('dup', N(5, 3, 2)), call('prd', N(3, 2)), call('iz', N(3, 2)),
           ite('TMfl',
               seq(call('drop', N(3)), call('dup', N(7, 6, 2)), call('prd', N(6, 2)), call('iz', N(6, 2)), call('drop', N(6))),
               seq(call('dup', N(7, 6, 2)), call('prd', N(6, 2)), call('modc', N(6, 3, 5, 4, 1, 2)), call('iz', N(6, 2)),
                   call('drop', N(6))))),
       "` koTest = dup 5 3 2 ; predNum 3 2 ; isZero 3 2 ; ite flag ( dropNum 3 ; dup 7 6 2 ; predNum 6 2 ; isZero 6 2 ; "
       "dropNum 6 ) ( dup 7 6 2 ; predNum 6 2 ; modC 6 3 5 4 1 2 ; isZero 6 2 ; dropNum 6 ) `")
frag12('kob', 'TMIkob', [], seq(call('kot', []), call('aca', []), call('drop', N(5))),
       "` koBody = koTest ; accAnd ; dropNum 5 `")
frag12('koa', 'TMIkoa', [], ACCLOOP('kob'), ACCLEAN + "at ` body = koBody `")
frag12('ko', 'TMIko', [], seq(call('lcpy', N(4, 5, 2, 3)), call('koa', [])),
       "` korseltTDF = copyList 4 5 2 3 ; accLoopF koBody `")
frag12('ver', 'TMIver', [],
       seq(pushnum('1', 1), call('nd', []), call('aca', []), call('ap', []), call('aca', []), call('prl', N(4, 5, 6, 2, 3)),
           call('dup', N(7, 6, 2)), call('cmp', N(5, 6)), load(L_EQ), call('aca', []), call('ko', []), call('aca', []),
           call('llen', N(4, 5, 2, 3)), pnv('6', '3'), call('cmp', N(6, 5)), load(L_NGT), call('aca', []),
           call('iz', N(1, 2)), load(L_NOTF), call('drop', N(1))),
       "` verifyF = pushNum 1 1 ; nodupTDF ; accAnd ; allPrimeTDF ; accAnd ; prodLF 4 5 6 2 3 ; dup 7 6 2 ; "
       "cmpFrag 5 6 ; load' ( flag := decide ( cmp = .eq ) ) ; accAnd ; korseltTDF ; accAnd ; listLen 4 5 2 3 ; "
       "pushNum 6 3 ; cmpFrag 6 5 ; load' ( flag := !decide ( cmp = .gt ) ) ; accAnd ; isZero 1 2 ; "
       "load' ( flag := !flag ) ; dropNum 1 `")

# ------------------------------------------------------------ Step5: the machine body
frag12('srch', 'TMIsrch', ['C', 'K'],
       seq(call('inp', []), call('scal', ['C', 'K']), call('s2f', []),
           ite('TMfl',
               seq(call('scf', []),
                   ite('TMfl',
                       seq(call('exf', N(6, 3, 0, 5, 1, 2, 7, 4)),
                           ite('TMfl', seq(call('ver', []), ite('TMfl', call('out', []), call('fal', []))),
                               call('fal', []))),
                       call('fal', []))),
               call('fal', []))),
       "` searchF C1 K = inputF ; scalesF C1 K ; step2F ; ite flag ( scanF ; ite flag ( extractF 6 3 0 5 1 2 7 4 ; "
       "ite flag ( verifyF ; ite flag outputF failAll ) failAll ) failAll ) failAll ` at ` C1 = C `")

class _ParamFrag(_Frag):
    """a predicate whose extra arguments are Lean's constants, not stacks: an instance at the numeral stacks keeps them"""
    def at(self, ks, P, E, T='T', M='M'):
        m = {x: x for x in self.stacks}
        m.update({'T': T, 'M': M, 'P': P, 'E': E})
        return m


for _n in ('sczz', 'scyy', 'scal', 'srch'):
    FRAGS[_n].__class__ = _ParamFrag

PREDS12 = ['pnv', 'mes', 'fal', 'out', 'inp', 'sclg', 'scth', 'sctt', 'sczz', 'scbz', 'scyy', 'sc99', 'scal',
           'aca', 'mlb', 'mls', 'ndb', 'nda', 'nd', 'apb', 'apa', 'ap', 'kot', 'kob', 'koa', 'ko', 'ver', 'srch']


# ============================================================ frozen statements (T12-blueprint.md section 2)
STMTS12 = {}
TREES12 = {}
ORDER12 = []


def add12(label, tree, concl):
    STMTS12[label] = '( %s -> %s )' % (cj(tree), concl)
    TREES12[label] = (tree, concl)
    if label not in ORDER12:
        ORDER12.append(label)
    # T10's finish() reads TREES10 / STMTS10
    T10.STMTS10[label] = STMTS12[label]
    T10.TREES10[label] = (tree, concl)


def allstmts12():
    return [(l, STMTS12[l]) for l in ORDER12]


TB = lambda x: '( TMB ` %s )' % x
DOMT = 'dom ( 1st ` ( 1st ` T ) )'
INIT = lambda k, W: '( k e. %s |-> if ( k = %s , %s , (/) ) )' % (DOMT, k, W)   # Lean ` Frag.initStacks k W `
LEN = lambda x: '( # ` %s )' % x
COMMA1 = '<" 4 ">'


def lsum(*ts):
    """left-associated sum"""
    out = ts[0]
    for t in ts[1:]:
        out = '( %s + %s )' % (out, t)
    return out


# ------------------------------------------------------------ failAll_runs
DATA_FAL = STKD('D')
TREE_FAL = TREE0('fal', DATA_FAL)
FALC = lsum(*([LEN(DK(k)) for k in range(8)] + ['9']))
CONCL_FAL = TRI(CS('fal'), CLN('E', S, INIT('1', COMMA1)), FALC)
add12('tmifal', TREE_FAL, CONCL_FAL)

# ------------------------------------------------------------ outputF_runs: m = F , U = W , b = B , bM = N , r4 = X , r7 = Y
OUT_ = '( F encodeOutput W )'
DATA_OUT = ((STKD('D'), ('W e. Word NN0', 'F e. NN0'), ('B e. NN0', 'N e. NN0')),
            ((RALB('W', 'B'), LT2('F', 'N')), (WG('X'), WG('Y'))),
            (DEQ(4, ENCL('W', 'X')), DEQ(7, EWg('F', 'Y'))))
TREE_OUT = TREE0('out', DATA_OUT)
OUTC = lsum(LEN(DK(0)), LEN(DK(1)), LEN(DK(2)), LEN(DK(3)), LEN(DK(5)), LEN(DK(6)), '6',
            '( ( ( # ` W ) + 1 ) x. ( TMB ` B ) )', '( ( ( # ` W ) x. ( ( 2 x. B ) + 6 ) ) + 3 )', '( TMB ` N )',
            '( ( # ` Y ) + 1 )', '( ( # ` X ) + 1 )')
CONCL_OUT = TRI(CS('out'), CLN('E', S, INIT('1', OUT_)), OUTC)
add12('tmiout', TREE_OUT, CONCL_OUT)

# ------------------------------------------------------------ inputF_runs: n = N (from Lean's initStacks 0 ( encodeNatGamma' n ))
DATA_INP = 'N e. NN0'
TREE_INP = ((T_PHM7, FRAGS['inp'].pred()), DATA_INP)
CONCL_INP = TRI(CLN(FRAGS['inp'].entry(), S, INIT('0', '( encNatGam ` N )')),
                CLN('E', S, INIT('7', '( ( encNatGam ` N ) ++ %s )' % COMMA1)),
                '( ( 2 x. ( # ` ( encodeNat ` N ) ) ) + 4 )')
add12('tmiinp', TREE_INP, CONCL_INP)

# ------------------------------------------------------------ Lean's scalesTM: the definition ScTM (hand-written df- in the sortie file)
def SCA_(n): return '( 2 Nlog ( 2 Nlog %s ) )' % n                       # a = log log n
def SCB_(n): return '( 2 Nlog %s )' % SCA_(n)                            # b = log a
def SCZ_(c, n): return '( ( %s x. %s ) x. %s )' % (c, SCA_(n), SCB_(n))  # z = C1 a b
def SCBZ_(c, n): return '( ( 2 Nlog %s ) + 1 )' % SCZ_(c, n)             # bz = log z + 1
def SCZ99_(c, n): return '( 2 ^ ( |_ ` ( ( ( ; 9 9 x. %s ) + ; 9 9 ) / ; ; 1 0 0 ) ) )' % SCBZ_(c, n)
def SCY_(c, k, n): return '( 2 ^ ( |_ ` ( ( ( ( ( %s - 1 ) x. %s ) + %s ) - 1 ) / %s ) ) )' % (k, SCBZ_(c, n), k, k)
def SCT_(n): return '( 3 x. %s )' % SCA_(n)
def SCTH_(n): return '( 2 ^ ( |_ ` ( ( ( 6 x. ( ( 2 Nlog ( ( 2 Nlog %s ) + 1 ) ) + 1 ) ) + 4 ) / 5 ) ) )' % n
def SCTUP_(c, k, n): return '<. <. <. %s , %s >. , <. %s , %s >. >. , %s >.' % (SCZ_(c, n), SCZ99_(c, n), SCY_(c, k, n), SCT_(n), SCTH_(n))
DF_SCTM = 'ScTM = ( c e. NN0 , k e. NN |-> ( n e. NN0 |-> %s ) )' % SCTUP_('c', 'k', 'n')
SC_ = '( ( C ScTM K ) ` N )'
PZ = lambda s: '( 1st ` ( 1st ` ( 1st ` %s ) ) )' % s
PZ99 = lambda s: '( 2nd ` ( 1st ` ( 1st ` %s ) ) )' % s
PY = lambda s: '( 1st ` ( 2nd ` ( 1st ` %s ) ) )' % s
PT = lambda s: '( 2nd ` ( 2nd ` ( 1st ` %s ) ) )' % s
PTH = lambda s: '( 2nd ` %s )' % s

# ------------------------------------------------------------ scalesF_runs: C1 = C , K = K , n = N , b = B , r7 = X
DATA_SCAL = ((STKD('D'), ('C e. NN0', 'K e. NN', 'N e. NN0'), ('B e. NN0', WG('X'))),
             (LT2('N'), LT2('C'), LT2('K')), DEQ(7, EWg('N', 'X')))
TREE_SCAL = TREE0('scal', DATA_SCAL)
SCALD = UP('D', '0', EWg(PZ(SC_), EWg(PZ99(SC_), EWg(PY(SC_), EWg(PT(SC_), EWg(PTH(SC_), DK(0)))))))
CONCL_SCAL = TRI(CS('scal'), CLN('E', S, SCALD), '( ; 5 0 x. ( TMB ` ( ( 3 x. B ) + 8 ) ) )')
add12('tmiscal', TREE_SCAL, CONCL_SCAL)

# ------------------------------------------------------------ verifyF_le_B: m = F , S = W , b = B , bM = N , r4 = X , r7 = Y
VER_ = '( F Verify W )'
VX_ = '( ( ( ( ( 2 x. ( ( # ` W ) + 1 ) ) x. B ) + ( 3 x. B ) ) + N ) + 8 )'
DATA_VER = ((STKD('D'), ('W e. Word NN0', 'F e. NN0'), ('B e. NN0', 'N e. NN0')),
            ((RALB('W', 'B'), LT2('( # ` W )', 'B'), LT2('F', 'N')), ('B <_ N', '1 <_ F', 'A. a e. ran W 1 <_ a'),
             (WG('X'), WG('Y'))),
            (DEQ(4, ENCL('W', 'X')), DEQ(7, EWg('F', 'Y'))))
TREE_VER = TREE0('ver', DATA_VER)
CONCL_VER = TRI(CS('ver'), CLN('E', NFL('( 1st ` %s )' % VER_), 'D'),
                '( ( ( 2nd ` %s ) + 1 ) x. ( TMB ` ( ( 4 x. %s ) + 6 ) ) )' % (VER_, VX_))
add12('tmiverb', TREE_VER, CONCL_VER)

# ------------------------------------------------------------ searchF_le_B: C1 = C , K = K , n = N , bs = B , bn = H
SE_ = '( %s Search N )' % SC_
GETD_ = 'if ( ( 1st ` %s ) = ( inr ` (/) ) , <. 0 , (/) >. , ( 2nd ` ( 1st ` %s ) ) )' % (SE_, SE_)
OUTS_ = '( ( 1st ` %s ) encodeOutput ( 2nd ` %s ) )' % (GETD_, GETD_)


def SB1_(t, bs, bn): return '( ( ( ( 5 x. ( ( %s x. %s ) + 1 ) ) + %s ) + %s ) + 1 )' % (t, bs, bs, bn)
def SX_(t, p, b1): return '( ( ( ( ( ; ; 1 1 1 x. ( %s + 1 ) ) + ( ; 1 3 x. ( %s + 2 ) ) ) x. %s ) + ( 4 x. %s ) ) + ; ; 2 0 0 )' % (t, p, b1, t)
def SPOLY_(t, bs, bn):
    p2t = '( 2 ^ %s )' % t
    return ('( ; ; 3 0 0 x. ( ( ( ( 2 ^ ( ( %s x. %s ) + 1 ) ) ^ 2 ) x. ( %s + 2 ) ) x. ( TMB ` %s ) ) )'
            % (t, bs, p2t, SX_(t, p2t, SB1_(t, bs, bn))))


SRCHPRE = CLN(FRAGS['srch'].entry(), S, INIT('0', '( encNatGam ` N )'))
SRCHPOST = CLN('E', S, INIT('1', OUTS_))
DATA_SRB = ((('C e. NN0', 'K e. NN', 'N e. NN0'), ('B e. NN0', 'H e. NN0', '2 <_ B'), '1 <_ %s' % PZ(SC_)),
            ((LT2(PZ(SC_)), LT2(PZ99(SC_)), LT2(PY(SC_))), (LT2(PT(SC_)), LT2('C'), LT2('K'))),
            (LT2('N', 'H'), LT2(PTH(SC_), 'H')))
TREE_SRB = ((T_PHM7, FRAGS['srch'].pred()), DATA_SRB)
CONCL_SRB = TRI(SRCHPRE, SRCHPOST, '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (SE_, SPOLY_(PT(SC_), 'B', 'H')))
add12('tmisrchb', TREE_SRB, CONCL_SRB)

# ------------------------------------------------------------ searchF_runs: every n with 1 <_ z , the bound searchBound
SBS_ = '( ( 2 Nlog ( ( ( ( ( %s + %s ) + %s ) + %s ) + C ) + K ) ) + 2 )' % (PZ(SC_), PZ99(SC_), PY(SC_), PT(SC_))
SBN_ = '( ( 2 Nlog ( N + %s ) ) + 1 )' % PTH(SC_)
DATA_SRR = (('C e. NN0', 'K e. NN', 'N e. NN0'), '1 <_ %s' % PZ(SC_))
TREE_SRR = ((T_PHM7, FRAGS['srch'].pred()), DATA_SRR)
CONCL_SRR = TRI(SRCHPRE, SRCHPOST, '( ( ( 2nd ` %s ) + 1 ) x. %s )' % (SE_, SPOLY_(PT(SC_), SBS_, SBN_)))
add12('tmisrch', TREE_SRR, CONCL_SRR)

# ------------------------------------------------------------ write-only mode: T12WRITE=1 makes W.run only write the worksheet
# (the worksheets are then added in one mmj2 load by scratch/t12/batch.py)
if os.environ.get('T12WRITE'):
    import tm as _tm
    _tm.W.run = lambda self, unify_only=False: (self.write(), print('WROTE', self.label), True)[2]


# ------------------------------------------------------------ write-only runs before a callee is in the database (T12PRE=1):
# inst reads statements from the database; fall back to the frozen texts (STMTS12, T12EXTRA) for labels not yet added
T12EXTRA = {}
if os.environ.get('T12PRE'):
    import t6blib as _T6
    _orig_stmt = _T6.stmt

    def _stmt12(label):
        if label in _T6._STMT:
            return _T6._STMT[label]
        if label in STMTS12:
            return STMTS12[label]
        if label in T12EXTRA:
            return T12EXTRA[label]
        return _orig_stmt(label)
    _T6.stmt = _stmt12
