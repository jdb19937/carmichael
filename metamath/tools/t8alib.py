r"""Sortie T8a: the concrete Table, part 1 (TM/Table.lean at the machine).

The handlers ` readKet ` / ` readBlank ` , the word ` encSlots ` , and the
installation predicates and runs forms of ` moveSlot ` , ` copySlot ` ,
` dropList ` , ` walkUp ` , ` walkDown ` , ` emptyTbl ` (T7b's encoding: one wff
predicate per fragment, own equations read from the TTAB generic with the
concrete handlers, callees as predicates).  Statement texts (the frozen
statements of T8a-blueprint.md section 4: ` STMTS ` ) and shared helpers on
top of tools/t7clib.py and tools/gen/t7c_h_lst.py (read-only).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen'))
from t7clib import *
import t7c_h_lst as H
from t7_e_cmp import lamty, cis_ty
from cl import Closure
import lin
lin.FASTPATH = True

S = '( 2nd ` T )'
SLOT = '( Word NN0 |_| 1o )'
WSLOT = 'Word %s' % SLOT
HDLS = "( ( 2nd ` T ) ^m ( ( 2nd ` T ) X. ( Gamma' |_| 1o ) ) )"
CNFL = CNOT('fl')
RDK, RDBL = 'TMrdKet', 'TMrdBlank'
KET, BLANK = '3', '0'


def ESL(o):
    return '( encSlot ` %s )' % o


def ES(L):
    return '( encSlots ` %s )' % L


def SB(o):
    """Lean ` SlotBounded N b o ` """
    return '( %s =/= ( inr ` (/) ) -> ( ( # ` ( 2nd ` %s ) ) <_ N /\\ A. a e. ran ( 2nd ` %s ) a < ( 2 ^ B ) ) )' % (o, o, o)


RSB = 'A. o e. ran L %s' % SB('o')
DROP = lambda L, i: '( %s substr <. %s , ( # ` %s ) >. )' % (L, i, L)
PFX = lambda L, i: '( %s prefix %s )' % (L, i)
REV = lambda x: '( reverse ` %s )' % x
NFL = lambda v: '{ h e. TMSt | ( TMfl ` h ) = %s }' % v
IF1 = lambda c: 'if ( %s , 1o , (/) )' % c


# ------------------------------------------------------------ D1: the handlers
def HVAL(v, o, c):
    """the value of a peek handler setting flag := decide ( o = some c )"""
    return MK(*([FLD(f, v) for f in ORDER[:6]] + ['if ( %s = ( inl ` %s ) , 1o , (/) )' % (o, c)]))


HANDLERS = {RDK: KET, RDBL: BLANK}
ST_HF = {h: '%s e. %s' % (h, HDLC) for h in HANDLERS}
ST_HV = {h: '( ( V e. TMSt /\\ O e. %s ) -> ( %s ` <. V , O >. ) = %s )' % (OPT, h, HVAL('V', 'O', c)) for h, c in HANDLERS.items()}
HCLS = lambda z, c: NFL('if ( %s = %s , 1o , (/) )' % (z, c))
ST_HC = {h: "( ( V e. TMSt /\\ Z e. Gamma' ) -> ( %s ` <. V , ( inl ` Z ) >. ) e. %s )" % (h, HCLS('Z', c))
         for h, c in HANDLERS.items()}
HI_KET = "A. r e. %s A. z e. Gamma' ( %s ` <. r , ( inl ` z ) >. ) e. %s" % (S, RDK, HCLS('z', KET))
HI_BLK = "A. r e. %s A. z e. Gamma' ( %s ` <. r , ( inl ` z ) >. ) e. %s" % (S, RDBL, HCLS('z', BLANK))
HI_TY = ('%s e. %s' % (RDK, HDLS), '%s e. %s' % (RDBL, HDLS))
HI_TREE = (HI_TY, HI_KET, HI_BLK)
ST_HI = '( %s -> %s )' % (SEQ, cj(HI_TREE))
HLAB = {RDK: 'ket', RDBL: 'blk'}


# ------------------------------------------------------------ D3: encSlots
ST_ESV = '( L e. %s -> %s = ( ( freeMnd ` Gamma\' ) gsum ( encSlot o. L ) ) )' % (WSLOT, ES('L'))
ST_ESCL = "( L e. %s -> %s e. Word Gamma' )" % (WSLOT, ES('L'))
ST_ES0 = '%s = (/)' % ES('(/)')
ST_ESCC = '( ( L e. %s /\\ U e. %s ) -> %s = ( %s ++ %s ) )' % (WSLOT, WSLOT, ES('( L ++ U )'), ES('L'), ES('U'))
ST_ESS1 = '( O e. %s -> %s = %s )' % (SLOT, ES('<" O ">'), ESL('O'))
ST_ESDR = ('( ( L e. %s /\\ I e. ( 0 ..^ ( # ` L ) ) ) -> %s = ( %s ++ %s ) )'
           % (WSLOT, ES(DROP('L', 'I')), ESL('( L ` I )'), ES(DROP('L', '( I + 1 )'))))
ST_ESRV = ('( ( L e. %s /\\ I e. ( 0 ..^ ( # ` L ) ) ) -> %s = ( %s ++ %s ) )'
           % (WSLOT, ES(REV(PFX('L', '( I + 1 )'))), ESL('( L ` I )'), ES(REV(PFX('L', 'I')))))
ST_SLN0 = '( O e. %s -> %s =/= (/) )' % (SLOT, ESL('O'))
ST_SLBK = "( ( O e. %s /\\ R e. Word Gamma' ) -> ( ( %s ++ R ) ` 0 ) =/= 0 )" % (SLOT, ESL('O'))
ST_ESHD = ("( ( L e. %s /\\ X e. Word Gamma' /\\ I e. ( 0 ... ( # ` L ) ) ) -> ( ( ( %s ++ ( <\" 0 \"> ++ X ) ) ` 0 ) = 0 <-> I = ( # ` L ) ) )"
           % (WSLOT, ES(DROP('L', 'I'))))


# ------------------------------------------------------------ the walkDown counter
FG = '( toNat ` G )'
def LNC(i):
    return 'if ( ( # ` G ) = ( bl ` %s ) , ( bl ` ( %s - %s ) ) , ( # ` G ) )' % (FG, FG, i)
def CW(i):
    return '( ( %s - %s ) bwrd %s )' % (FG, i, LNC(i))
ST_WC0 = '( G e. Word 2o -> %s = G )' % CW('0')
ST_WCP = ('( ( G e. Word 2o /\\ I e. NN0 /\\ I <_ %s ) -> ( %s e. Word 2o /\\ ( toNat ` %s ) = ( %s - I ) /\\ ( # ` %s ) <_ ( # ` G ) ) )'
          % (FG, CW('I'), CW('I'), FG, CW('I')))
ST_WCS = '( ( G e. Word 2o /\\ I e. NN0 /\\ I < %s ) -> ( predBits ` %s ) = %s )' % (FG, CW('I'), CW('( I + 1 )'))

# ------------------------------------------------------------ emptyTbl's table word
ST_ETB0 = '( L e. NN0 -> ( L encTblAsc EmptyTbl ) = ( 3 repeatS L ) )'


# ------------------------------------------------------------ D2: the installation predicates
def own_eqs(generic, hmap, order):
    """the own program equations of a generic TTAB statement in the order of its labels, with the
    handler/stack map applied"""
    ante, _ = split_imp(stmt(generic))
    byl = {}
    def go(t):
        if isinstance(t, str):
            if t.startswith('( M ` '):
                byl[t.split()[3]] = tsub_text(t, hmap)
            return
        for x in t:
            go(x)
    go(parse_conj(ante))
    return [byl[l] for l in order]


def register(name, const, generic, ks, order, exit, hmap, children, lean):
    eqs = own_eqs(generic, hmap, order)
    prog = grp(eqs)
    labt = grp([LAB(l) for l in order] + [LAB(exit)])
    return comp(name, const, ks, order, exit, prog, labt, lean, children)


K4 = ['K', 'J', 'I', "I'"]
K3 = ['K', 'J', 'I']
HM_KET = {'F': RDK, 'C': 'TMfl', "F'": PID, 'Y': KET}
register('mvs', 'TMImvs', 'tm2fmvs', K4, ['P0', "B'", 'B"', 'B1_'], 'E', HM_KET,
         [('lrev', ['K', "I'", 'I'], 'E0', 'W1'), ('lrev', ["I'", 'J', 'I'], 'W1', 'E')],
         "` moveSlot src dst s s' = peekKet src ; ite flag ( popTop src ; pushSym dst ket ) "
         "( revList src s' s ; revList s' dst s ) `")
register('cps', 'TMIcps', 'tm2fcps', K4, ['P0', "B'", 'B"'], 'E', HM_KET,
         [('lcpy', K4, 'E0', 'E')],
         "` copySlot src dst s s' = peekKet src ; ite flag ( pushSym dst ket ) ( copyList src dst s s' ) `")
register('dpl', 'TMIdpl', 'tm2fdpl', ['K'], ['P1', 'A', 'A"', 'E'], "E'", {'F': 'TMrdBra', 'C': CNFL, 'F"': PID},
         [('drop', ['K'], "A'", 'A"')],
         "` dropList x = forEntries x ( dropNum x ) ; popTop x `")
register('wup', 'TMIwup', 'tm2fwup', K4, ['P0', 'A', "B'", 'E'], "E'", {'K': "I'", 'F': RDBL, 'C0': CNFL, 'F"': PID},
         [('mvs', ["I'", 'K', 'I', 'J'], 'B0', "B'")],
         "` walkUp tbl j s scr = forSlots scr ( moveSlot scr tbl s j ) ; popTop scr ` , "
         "` forSlots x body = peekBlank x ; loop ( !flag ) ( body ; peekBlank x ) `")
register('wdn', 'TMIwdn', 'tm2fwdn', K4, ['P0', 'A'], "E'", {'K': "I'", 'Y': BLANK, 'C0': CNFL},
         [('iz', ['J', 'I'], 'P1', 'A'), ('mvs', ['K', "I'", 'I', 'J'], 'B0', 'X1'), ('prd', ['J', 'I'], 'X1', 'X2'),
          ('iz', ['J', 'I'], 'X2', 'A'), ('drop', ['J'], 'E', "E'")],
         "` walkDown tbl j s scr = pushSym scr blank ; isZero j s ; loop ( !flag ) ( moveSlot tbl scr s j ; "
         "predNum j s ; isZero j s ) ; dropNum j `")
register('etb', 'TMIetb', 'tm2fetb', K3, ['P0', 'A', 'B0'], "E'", {'K': 'J', 'Y': BLANK, "Y'": KET, 'C0': CNFL},
         [('iz', ['K', 'I'], 'P1', 'A'), ('prd', ['K', 'I'], "B'", 'X1'), ('iz', ['K', 'I'], 'X1', 'A'), ('drop', ['K'], 'E', "E'")],
         "` emptyTbl c tbl s = pushSym tbl blank ; isZero c s ; loop ( !flag ) ( pushSym tbl ket ; predNum c s ; "
         "isZero c s ) ; dropNum c `")
PREDS = ['mvs', 'cps', 'dpl', 'wup', 'wdn', 'etb']


def HEAD(ks, fname):
    """the antecedent head: the machine, the predicate, the stack indices and their distinctness"""
    f = FRAGS[fname]
    if len(ks) == 1:
        return ((T_PHM7, f.pred()), IDX(ks[0]))
    return ((T_PHM7, f.pred()), (idx_tree(ks), dist_tree(ks)))


def TREE(ks, fname, data):
    h = HEAD(ks, fname)
    return (h[0], h[1], data)


C0 = lambda D: CLN('( P ` 0 )', S, D)
CE = lambda D: CLN('E', S, D)

# moveSlot / copySlot
SLOTC = '( ( N x. ( ( 4 x. B ) + ; 1 2 ) ) + ; 1 0 )'
CPSC = '( ( N x. ( ( 6 x. B ) + ; 1 7 ) ) + ; 1 1 )'
DATA_SL = ((STKD('D'), 'O e. %s' % SLOT, WRD('R', GAM)), '( D ` K ) = ( %s ++ R )' % ESL('O'), (('N e. NN0', 'B e. NN0'), SB('O')))
TREE_MVS = TREE(K4, 'mvs', DATA_SL)
TREE_CPS = TREE(K4, 'cps', DATA_SL)
CONCL_MVS = TRI(C0('D'), CE(UP(UP('D', 'K', 'R'), 'J', CC(ESL('O'), '( D ` J )'))), SLOTC)
CONCL_CPS = TRI(C0('D'), CE(UP('D', 'J', CC(ESL('O'), '( D ` J )'))), CPSC)

# dropList
DATA_DPL = ((STKD('D'), '( D ` K ) = ( ( encList ` L ) ++ R )'), ('L e. Word NN0', WRD('R', GAM)),
            ('B e. NN0', 'A. a e. ran L a < ( 2 ^ B )'))
TREE_DPL = TREE(['K'], 'dpl', DATA_DPL)
CONCL_DPL = TRI(C0('D'), CE(UP('D', 'K', 'R')), '( ( ( # ` L ) x. ( B + 3 ) ) + 3 )')

# walkUp
DATA_WUP = ((STKD('D'), ('L e. %s' % WSLOT, 'U e. %s' % WSLOT), (WRD('X', GAM), WRD('Y', GAM))),
            ("( D ` I' ) = ( %s ++ ( <\" 0 \"> ++ X ) )" % ES('L'), '( D ` K ) = ( %s ++ Y )' % ES('U')),
            (('N e. NN0', 'B e. NN0'), RSB))
TREE_WUP = TREE(K4, 'wup', DATA_WUP)
WUPC = '( ( ( # ` L ) x. ( %s + 2 ) ) + 3 )' % SLOTC
CONCL_WUP = TRI(C0('D'), CE(UP(UP('D', 'K', CC(ES('( %s ++ U )' % REV('L')), 'Y')), "I'", 'X')), WUPC)

# walkDown
DATA_WDN = ((STKD('D'), ('L e. %s' % WSLOT, 'G e. Word 2o'), (WRD('X', GAM), WRD('Y', GAM))),
            ('( D ` K ) = ( %s ++ X )' % ES('L'), '( D ` J ) = ( ( inclBool o. G ) ++ ( <" 4 "> ++ Y ) )'),
            (('N e. NN0', 'B e. NN0', 'H e. NN0'), ('( # ` G ) <_ H', '%s < ( # ` L )' % FG), RSB))
TREE_WDN = TREE(K4, 'wdn', DATA_WDN)
WDNC = '( ( %s x. ( ( %s + ( 4 x. H ) ) + 9 ) ) + ( ( 3 x. H ) + 8 ) )' % (FG, SLOTC)
DFIN_WDN = UP(UP(UP('D', 'K', CC(ES(DROP('L', FG)), 'X')), 'J', 'Y'), "I'",
              CC(ES(REV(PFX('L', FG))), "( <\" 0 \"> ++ ( D ` I' ) )"))
CONCL_WDN = TRI(C0('D'), CE(DFIN_WDN), WDNC)

# emptyTbl
DATA_ETB = ((STKD('D'), 'L e. NN0', WRD('X', GAM)), '( D ` K ) = ( ( encNatGam ` L ) ++ ( <" 4 "> ++ X ) )')
TREE_ETB = TREE(K3, 'etb', DATA_ETB)
ETBC = '( ( L x. ( ( 4 x. ( bl ` L ) ) + ; 1 0 ) ) + ( ( 2 x. ( bl ` L ) ) + 8 ) )'
DFIN_ETB = UP(UP('D', 'K', 'X'), 'J', CC('( L encTblAsc EmptyTbl )', '( <" 0 "> ++ ( D ` J ) )'))
CONCL_ETB = TRI(C0('D'), CE(DFIN_ETB), ETBC)
TREE_ETBB = TREE(K3, 'etb', (DATA_ETB, ('B e. NN0', 'L < ( 2 ^ B )')))
CONCL_ETBB = TRI(C0('D'), CE(DFIN_ETB), '( ( L + 1 ) x. ( TMB ` B ) )')

STMTS = {}
for _h, _c in HANDLERS.items():
    STMTS['tmcrd%sf' % HLAB[_h]] = ST_HF[_h]
    STMTS['tmcrd%sv' % HLAB[_h]] = ST_HV[_h]
    STMTS['tmcrd%sc' % HLAB[_h]] = ST_HC[_h]
STMTS.update({'tmctbhi': ST_HI,
              'ttsesv': ST_ESV, 'ttsescl': ST_ESCL, 'ttses0': ST_ES0, 'ttsesccat': ST_ESCC, 'ttsess1': ST_ESS1,
              'ttsesdrop': ST_ESDR, 'ttsesrev': ST_ESRV, 'ttslotn0': ST_SLN0, 'ttslotblk': ST_SLBK, 'ttseshd': ST_ESHD,
              'ttwc0': ST_WC0, 'ttwcp': ST_WCP, 'ttwcs': ST_WCS, 'ttetb0': ST_ETB0})
for _n in PREDS:
    STMTS['tmi%su' % _n] = unfold_stmt(FRAGS[_n])
for _l, _t, _c in [('tmimvs', TREE_MVS, CONCL_MVS), ('tmicps', TREE_CPS, CONCL_CPS), ('tmidpl', TREE_DPL, CONCL_DPL),
                   ('tmiwup', TREE_WUP, CONCL_WUP), ('tmiwdn', TREE_WDN, CONCL_WDN), ('tmietb', TREE_ETB, CONCL_ETB),
                   ('tmietbb', TREE_ETBB, CONCL_ETBB)]:
    STMTS[_l] = '( %s -> %s )' % (cj(_t), _c)
ORDER_FROZEN = (['tmcrdketf', 'tmcrdketv', 'tmcrdketc', 'tmcrdblkf', 'tmcrdblkv', 'tmcrdblkc', 'tmctbhi',
                 'ttsesv', 'ttsescl', 'ttses0', 'ttsesccat', 'ttsess1', 'ttsesdrop', 'ttsesrev', 'ttslotn0', 'ttslotblk',
                 'ttseshd', 'ttwc0', 'ttwcp', 'ttwcs', 'ttetb0']
                + ['tmi%su' % n for n in PREDS]
                + ['tmimvs', 'tmicps', 'tmidpl', 'tmiwup', 'tmiwdn', 'tmietb', 'tmietbb'])


def allstmts():
    return [(l, STMTS[l]) for l in ORDER_FROZEN]


# ============================================================ proof helpers
from t7lib import parts, rab_in, not1o, _transport


def hsetup(w, ph, T, ks, fname, children=True):
    """Ctx, machine, ne and the extra leaves: the predicate unfolded one level (and its callees one
    level), T7c's list interface (~ tmclhi ), the Table interface (~ tmctbhi ), the flag tests
    (~ tmcflty ), the letters 0 2 3 4"""
    c, mk, ne, base = setup(w, ph, T, ks, pred=FRAGS[fname].pred(), fname=fname)
    f = FRAGS[fname]
    lm = f.lmap()
    if children:
        for j, (fn, cks, en, exn) in enumerate(f.children):
            P_ = PL('P', f.slot(j))
            pr = FRAGS[fn].pred(cks, 'T', 'M', P_, lm[exn])
            base.update(unfold_all(w, ph, base[pr], fn, cks, P_, lm[exn], rec=False))
    ex = dict(base)
    ex.update(H.handler_extra(w, ph, mk, H.IFACE))
    hi = w.s([mk['seq'], w.inst('tmctbhi')], 'syl', '( %s -> %s )' % (ph, cj(HI_TREE)))
    ex.update(parts(w, ph, hi, HI_TREE))
    FLT = (('TMcar e. ( 2o ^m ( 2nd ` T ) )', 'TMda e. ( 2o ^m ( 2nd ` T ) )'),
           ('TMdb e. ( 2o ^m ( 2nd ` T ) )', 'TMfl e. ( 2o ^m ( 2nd ` T ) )'))
    fl = w.s([mk['seq'], w.inst('tmcflty')], 'syl', '( %s -> %s )' % (ph, cj(FLT)))
    ex.update(parts(w, ph, fl, FLT))
    for n in ('0', '2', '3', '4'):
        ex["%s e. Gamma'" % n] = closed(w, ph, 'gamma%s' % n, "%s e. Gamma'" % n)
    ex[SSS(S)] = closed(w, ph, 'ssid', '%s C_ %s' % (S, S))
    return c, mk, ne, ex


def nfl_ss(w, ph, mk, V):
    """( ph -> NFL( V ) C_ ( 2nd ` T ) )"""
    ss = w.s([w.s([], 'ssrab2', '%s C_ TMSt' % NFL(V))], 'a1i', '( %s -> %s C_ TMSt )' % (ph, NFL(V)))
    return w.s([ss, mk['seq']], 'sseqtrrd', '( %s -> %s C_ %s )' % (ph, NFL(V), S))


def nfl_unpack(w, ph, V, x, xin):
    """from xin : ( ph -> x e. NFL( V ) ): ( ph -> x e. TMSt ), ( ph -> ( TMfl ` x ) = V )"""
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (x, x))
    cond = lambda t: '( TMfl ` %s ) = %s' % (t, V)
    cg, new = w.wcongr(cond('h'), {'h': x}, 'h = %s' % x, {'h': idh})
    assert new == cond(x), new
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (x, NFL(V), x, cond(x)))
    both = w.s([xin, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ph, x, cond(x)))
    return (w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (ph, x)), w.s([both], 'simprd', '( %s -> %s )' % (ph, cond(x))))


def nfl_pack(w, ph, V, x, xmem, cstep):
    """( ph -> x e. NFL( V ) )"""
    return rab_in(w, ph, NFL(V), lambda t: '( TMfl ` %s ) = %s' % (t, V), x, xmem, cstep)


def ht_nfl(w, ph, V):
    """( ph -> A. m e. NFL( V ) ( TMfl ` m ) = 1o ) for V = 1o, ( ... -. ( TMfl ` m ) = 1o ) for V = (/)
    (ph free of m)"""
    a = '( %s /\\ m e. %s )' % (ph, NFL(V))
    _, fl = nfl_unpack(w, a, V, 'm', w.s([], 'simpr', '( %s -> m e. %s )' % (a, NFL(V))))
    if V == '1o':
        return w.s([fl], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (ph, NFL(V)))
    n = not1o(w, a, fl, 'TMfl', 'm')
    return w.s([n], 'ralrimiva', '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (ph, NFL(V)))


def peek_iface(w, ph, mk, h, Z, zg, ifeq, V):
    """( ph -> A. r e. ( 2nd ` T ) ( h ` <. r , ( inl ` Z ) >. ) e. NFL( V ) ) from zg : ( ph -> Z e. Gamma' )
    and ifeq : ( ph -> if ( Z = c , 1o , (/) ) = V ) (c the handler's letter; ph free of r)"""
    c = HANDLERS[h]
    a = '( %s /\\ r e. %s )' % (ph, S)
    L = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))
    rr = w.s([w.s([], 'simpr', '( %s -> r e. %s )' % (a, S)), L(mk['seq'])], 'eleqtrd', '( %s -> r e. TMSt )' % a)
    N = '( %s ` <. r , ( inl ` %s ) >. )' % (h, Z)
    m = w.s([rr, L(zg), w.inst('tmcrd%sc' % HLAB[h])], 'syl2anc', '( %s -> %s e. %s )' % (a, N, HCLS(Z, c)))
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (N, N))
    cond = lambda t: '( TMfl ` %s ) = if ( %s = %s , 1o , (/) )' % (t, Z, c)
    cg, new = w.wcongr(cond('h'), {'h': N}, 'h = %s' % N, {'h': idh})
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (N, HCLS(Z, c), N, cond(N)))
    both = w.s([m, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (a, N, cond(N)))
    nm = w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (a, N))
    f1 = w.s([both], 'simprd', '( %s -> %s )' % (a, cond(N)))
    f2 = w.s([f1, L(ifeq)], 'eqtrd', '( %s -> ( TMfl ` %s ) = %s )' % (a, N, V))
    p = nfl_pack(w, a, V, N, nm, f2)
    return w.s([p], 'ralrimiva', '( %s -> A. r e. %s %s e. %s )' % (ph, S, N, NFL(V)))


def pop_iface(w, ph, mk, N, nss, Z, zg, N2=None, n2ss=None):
    """( ph -> A. r e. N ( PID ` <. r , ( inl ` Z ) >. ) e. N2 ) (N2 = ( 2nd ` T ) by default, or a class
    with n2ss : ( ph -> N C_ N2 )) from nss : ( ph -> N C_ ( 2nd ` T ) ), zg : ( ph -> Z e. Gamma' )"""
    N2 = N2 or S
    a = '( %s /\\ r e. %s )' % (ph, N)
    L = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (a, concl(w, ph, st)))
    rn = w.s([], 'simpr', '( %s -> r e. %s )' % (a, N))
    rs = w.s([L(nss), rn], 'sseldd', '( %s -> r e. %s )' % (a, S))
    rr = w.s([rs, L(mk['seq'])], 'eleqtrd', '( %s -> r e. TMSt )' % a)
    oz = w.s([L(zg), w.inst('djulcl')], 'syl', '( %s -> ( inl ` %s ) e. %s )' % (a, Z, OPT))
    OP = '<. r , ( inl ` %s ) >.' % Z
    ox = w.s([rr, oz], 'opelxpd', '( %s -> %s e. ( TMSt X. %s ) )' % (a, OP, OPT))
    fr = w.s([ox, w.inst('fvres')], 'syl', '( %s -> ( %s ` %s ) = ( 1st ` %s ) )' % (a, PID, OP, OP))
    f1 = w.s([rr, oz, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = r )' % (a, OP))
    pv = w.s([fr, f1], 'eqtrd', '( %s -> ( %s ` %s ) = r )' % (a, PID, OP))
    tgt = rs if N2 == S else w.s([L(n2ss), rn], 'sseldd', '( %s -> r e. %s )' % (a, N2))
    pm = w.s([pv, tgt], 'eqeltrd', '( %s -> ( %s ` %s ) e. %s )' % (a, PID, OP, N2))
    return w.s([pm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` %s ) e. %s )' % (ph, N, PID, OP, N2))


def HD0(V):
    return '( %s ` 0 )' % V


def TL1(V):
    return '( %s substr <. 1 , ( # ` %s ) >. )' % (V, V)


def word_split(w, ph, V, vw, vn0):
    """a non-empty word V over Gamma' (vw : ( ph -> V e. Word Gamma' ), vn0 : ( ph -> V =/= (/) )):
    ( ph -> V = ( <" ( V ` 0 ) "> ++ ( V substr <. 1 , ( # ` V ) >. ) ) ), the head's and the rest's typings"""
    eq = w.s([vw, vn0, w.inst('wrdeqs1cat')], 'syl2anc', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ph, V, HD0(V), TL1(V)))
    ln = w.s([vw, vn0, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` %s ) e. NN )' % (ph, V))
    z0 = w.s([ln, w.inst('lbfzo0')], 'sylibr', '( %s -> 0 e. ( 0 ..^ ( # ` %s ) ) )' % (ph, V))
    hg = w.s([vw, z0, w.inst('wrdsymbcl')], 'syl2anc', "( %s -> %s e. Gamma' )" % (ph, HD0(V)))
    tg = w.s([vw, w.inst('swrdcl')], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, TL1(V)))
    return eq, hg, tg


def slot_word(w, ph, oo, rw):
    """V = ( encSlot ` O ) ++ R for oo : ( ph -> O e. SLOT ), rw : ( ph -> R e. Word Gamma' ):
    (V, ew : ESL O e. Word Gamma', vw, vn0)"""
    V = CC(ESL('O'), 'R')
    ew = w.s([oo, w.s([w.s([], 'ttabslotf', "encSlot : %s --> Word Gamma'" % SLOT)], 'ffvelcdmi',
                      "( O e. %s -> %s e. Word Gamma' )" % (SLOT, ESL('O')))], 'syl', "( %s -> %s e. Word Gamma' )" % (ph, ESL('O')))
    vw = w.s([ew, rw, w.inst('ccatcl')], 'syl2anc', "( %s -> %s e. Word Gamma' )" % (ph, V))
    en = w.s([oo, w.inst('ttslotn0')], 'syl', '( %s -> %s =/= (/) )' % (ph, ESL('O')))
    c0 = w.s([ew, rw, w.inst('ccat0')], 'syl2anc', '( %s -> ( %s = (/) <-> ( %s = (/) /\\ R = (/) ) ) )' % (ph, V, ESL('O')))
    n1 = w.s([w.s([en], 'neneqd', '( %s -> -. %s = (/) )' % (ph, ESL('O')))], 'intnanrd', '( %s -> -. ( %s = (/) /\\ R = (/) ) )' % (ph, ESL('O')))
    n2 = w.s([c0, n1], 'mtbird', '( %s -> -. %s = (/) )' % (ph, V))
    vn0 = w.s([n2], 'neqned', '( %s -> %s =/= (/) )' % (ph, V))
    return V, ew, vw, vn0
