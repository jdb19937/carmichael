"""T9: exTest at the machine (Lean ` exTest_runs ` ) on its installation predicate TMIext, and two
helpers for the peeks of ` bra ` .

  tmcrdbrac   the class form of ` readBra ` : the flag records whether the symbol is ` bra `
  tmexhdb     the head of ` encList V ++ X ` is ` bra ` iff ` V ` is empty (Lean ` decide_head?_encList_bra ` )
  tmiexta     the prefix ` moveEntry nm snap s ; dup nm t s ; moveEntry snap nm s ; dup nm snap s ; cmpFrag t snap `
  tmiext      exTest_runs: the prefix (~ tmiexta ), the branch on ` cmp = lt ` by cases

    MM_DB=sorties/t9.mm python3 tools/gen/t9_d_ext.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
import t7c_h_lst as H
from t7_h_iz import lset_val, lset_ty
from t7lib import rab_in

SEL = sys.argv[1:]
ST_BRAC = "( ( V e. TMSt /\\ Z e. Gamma' ) -> ( TMrdBra ` <. V , ( inl ` Z ) >. ) e. %s )" % A8.HCLS('Z', '2')
HDB = lambda v, x: '( ( ( encList ` %s ) ++ %s ) ` 0 )' % (v, x)
ST_HDB = "( ( V e. Word NN0 /\\ X e. Word Gamma' ) -> ( %s = 2 <-> V = (/) ) )" % HDB('V', 'X')
EGY = EWg('G', 'Y')
EFGY = EWg('F', EGY)
WF = '( encNatGam ` F )'
ST_A = '( %s -> %s )' % (cj(TREE_EXT), TRI(CEN9('ext', 'D'), CLN('( P ` 0 )', CMPC('G', 'F'), 'D'), '( 5 x. ( TMB ` N ) )'))


def tmcrdbrac():
    lab = 'tmcrdbrac'
    w = W(lab, 'Lean\'s ` peekBra_runs ` at a state: ` readBra ` on the symbol ` Z ` sets the flag to ` decide ( Z = bra ) ` '
               'and keeps the other fields; the state lands in the class of states whose flag is that value.')
    ph = "( V e. TMSt /\\ Z e. Gamma' )"
    vv = w.s([], 'simpl', '( %s -> V e. TMSt )' % ph)
    zg = w.s([], 'simpr', "( %s -> Z e. Gamma' )" % ph)
    oz = w.s([zg, w.inst('djulcl')], 'syl', '( %s -> ( inl ` Z ) e. %s )' % (ph, OPT))
    nv = H.bra_val(w, ph, 'V', vv, '( inl ` Z )', oz)
    N = '( TMrdBra ` <. V , ( inl ` Z ) >. )'
    zv = w.s([zg], 'elexd', '( %s -> Z e. _V )' % ph)
    cv = closed(w, ph, '2ex', '2 e. _V')
    i11 = w.s([zv, cv, w.inst('tmcinl11')], 'syl2anc', '( %s -> ( ( inl ` Z ) = ( inl ` 2 ) <-> Z = 2 ) )' % ph)
    ib = w.s([i11], 'ifbid', '( %s -> if ( ( inl ` Z ) = ( inl ` 2 ) , 1o , (/) ) = if ( Z = 2 , 1o , (/) ) )' % ph)
    fl = w.s([nv['fields']['fl'], ib], 'eqtrd', '( %s -> ( TMfl ` %s ) = if ( Z = 2 , 1o , (/) ) )' % (ph, N))
    cond = lambda t: '( TMfl ` %s ) = if ( Z = 2 , 1o , (/) )' % t
    rab_in(w, ph, A8.HCLS('Z', '2'), cond, N, nv['mem'], fl)
    w.lines[-1] = 'qed:' + w.lines[-1].split(':', 1)[1]
    return w.run()


def tmexhdb():
    lab = 'tmexhdb'
    w = W(lab, 'The top of a list of numbers on a stack is ` bra ` exactly when the list is empty (Lean '
               '` decide_head?_encList_bra ` ).')
    ph = "( V e. Word NN0 /\\ X e. Word Gamma' )"
    s = w.s
    vw = s([], 'simpl', '( %s -> V e. Word NN0 )' % ph)
    xg = s([], 'simpr', "( %s -> X e. Word Gamma' )" % ph)
    hd = HDB('V', 'X')
    # V = (/) -> hd = 2
    p1 = '( %s /\\ V = (/) )' % ph
    v0 = s([], 'simpr', '( %s -> V = (/) )' % p1)
    e0 = s([s([v0], 'fveq2d', '( %s -> ( encList ` V ) = ( encList ` (/) ) )' % p1),
            closed(w, p1, 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'eqtrd', '( %s -> ( encList ` V ) = <" 2 "> )' % p1)
    e1 = s([s([e0], 'oveq1d', '( %s -> ( ( encList ` V ) ++ X ) = ( <" 2 "> ++ X ) )' % p1)], 'fveq1d',
           '( %s -> %s = ( ( <" 2 "> ++ X ) ` 0 ) )' % (p1, hd))
    g2 = closed(w, p1, 'gamma2', "2 e. Gamma'")
    s2 = s([g2], 's1cld', "( %s -> <\" 2 \"> e. Word Gamma' )" % p1)
    l1 = s([g2, w.inst('s1len') if False else w.inst('s1len')], 'syl', '( %s -> ( # ` <" 2 "> ) = 1 )' % p1) if False else \
        closed(w, p1, 's1len', '( # ` <" 2 "> ) = 1')
    lt = s([l1, closed(w, p1, '0lt1', '0 < 1')], 'breqtrrd', '( %s -> 0 < ( # ` <" 2 "> ) )' % p1)
    cf = s([s2, Lft(w, p1, ph, xg), lt, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( ( <" 2 "> ++ X ) ` 0 ) = ( <" 2 "> ` 0 ) )' % p1)
    sf = s([g2, w.inst('s1fv')], 'syl', '( %s -> ( <" 2 "> ` 0 ) = 2 )' % p1)
    fwd = s([s([e1, cf], 'eqtrd', '( %s -> %s = ( <" 2 "> ` 0 ) )' % (p1, hd)), sf], 'eqtrd', '( %s -> %s = 2 )' % (p1, hd))
    fwd_i = s([fwd], 'ex', '( %s -> ( V = (/) -> %s = 2 ) )' % (ph, hd))
    # V =/= (/) -> hd =/= 2
    p2 = '( %s /\\ V =/= (/) )' % ph
    vn = s([], 'simpr', '( %s -> V =/= (/) )' % p2)
    vw2 = Lft(w, p2, ph, vw)
    G = '( encNatGam o. V )'
    gw = s([vw2, w.inst('tm2lencgam')], 'syl', '( %s -> %s e. Word Word %s )' % (p2, G, BITS))
    gl = s([vw2, closed(w, p2, 'tm2lbitf', 'encNatGam : NN0 --> Word %s' % BITS), w.inst('lenco')], 'syl2anc',
           '( %s -> ( # ` %s ) = ( # ` V ) )' % (p2, G))
    hv = s([vw2, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` V ) = 0 <-> V = (/) ) )' % p2)
    lv = s([s([vn], 'neneqd', '( %s -> -. V = (/) )' % p2), hv], 'mtbird', '( %s -> -. ( # ` V ) = 0 )' % p2)
    hg = s([gw, w.inst('hasheq0')], 'syl', '( %s -> ( ( # ` %s ) = 0 <-> %s = (/) ) )' % (p2, G, G))
    lg = s([s([gl], 'eqeq1d', '( %s -> ( ( # ` %s ) = 0 <-> ( # ` V ) = 0 ) )' % (p2, G)), lv], 'mtbird',
           '( %s -> -. ( # ` %s ) = 0 )' % (p2, G))
    gn = s([s([lg, hg], 'mtbid', '( %s -> -. %s = (/) )' % (p2, G))], 'neqned', '( %s -> %s =/= (/) )' % (p2, G))
    le = s([vw2, w.inst('tm2lenceq')], 'syl', '( %s -> ( encList ` V ) = ( encListB ` %s ) )' % (p2, G))
    e2 = s([s([le], 'oveq1d', '( %s -> ( ( encList ` V ) ++ X ) = ( ( encListB ` %s ) ++ X ) )' % (p2, G))], 'fveq1d',
           '( %s -> %s = ( ( ( encListB ` %s ) ++ X ) ` 0 ) )' % (p2, hd, G))
    BU = '( %s u. { 4 } )' % BITS
    h1 = s([gw, Lft(w, p2, ph, xg), gn, w.inst('tm2lencbhd1')], 'syl3anc',
           '( %s -> ( ( ( encListB ` %s ) ++ X ) ` 0 ) e. %s )' % (p2, G, BU))
    hb = s([e2, h1], 'eqeltrd', '( %s -> %s e. %s )' % (p2, hd, BU))
    nb = s([s([], '2re', '2 e. RR'), w.inst('tmcnbits')], 'ax-mp', '-. 2 e. %s' % BITS)
    ne = s([s([], '2re', '2 e. RR'), s([], '2lt4', '2 < 4')], 'ltneii', '2 =/= 4')
    ns = s([s([ne], 'neii', '-. 2 = 4'), s([s([], '2ex', '2 e. _V')], 'elsn', '( 2 e. { 4 } <-> 2 = 4 )')], 'mtbir',
           '-. 2 e. { 4 }')
    nu = s([s([nb, ns], 'pm3.2i', '( -. 2 e. %s /\\ -. 2 e. { 4 } )' % BITS), s([], 'ioran', '( -. ( 2 e. %s \\/ 2 e. { 4 } ) <-> ( -. 2 e. %s /\\ -. 2 e. { 4 } ) )' % (BITS, BITS))],
           'mpbir', '-. ( 2 e. %s \\/ 2 e. { 4 } )' % BITS)
    nbu = s([nu, s([], 'elun', '( 2 e. %s <-> ( 2 e. %s \\/ 2 e. { 4 } ) )' % (BU, BITS))], 'mtbir', '-. 2 e. %s' % BU)
    bwd = s([hb, s([nbu], 'a1i', '( %s -> -. 2 e. %s )' % (p2, BU)), w.inst('nelne2')], 'syl2anc', '( %s -> %s =/= 2 )' % (p2, hd))
    bwd_i = s([bwd], 'ex', '( %s -> ( V =/= (/) -> %s =/= 2 ) )' % (ph, hd))
    bwd_c = s([bwd_i], 'necon4d', '( %s -> ( %s = 2 -> V = (/) ) )' % (ph, hd))
    w.qed([bwd_c, fwd_i], 'impbid', ST_HDB)
    return w.run()


class Ext(Base):
    def __init__(self, w, ph, T, eqK=True):
        c0 = Ctx(w, ph, T)
        fn, gn = c0['F e. NN0'], c0['G e. NN0']
        vw, xw, yw = c0['S e. Word NN0'], c0[WG('X')], c0[WG('Y')]
        egy = ewg_(w, ph, 'G', gn, 'Y', yw)
        eqs = {'K0': (EFGY, ewg_(w, ph, 'F', fn, EGY, egy))}
        if eqK:
            eqs['K'] = (ENCL('S', 'X'), enclg(w, ph, 'S', vw, 'X', xw))
        Base.__init__(self, w, ph, T, K5T, 'ext', eqs)
        self.fn, self.gn, self.vw, self.xw, self.yw = fn, gn, vw, xw, yw
        self.nn = self.c['N e. NN0']
        self.egy = self.g(EGY, egy)


def tmiexta():
    lab = 'tmiexta'
    ph = cj(TREE_EXT)
    w = W(lab, 'The prefix of Lean\'s ` exTest ` at the machine: ` moveEntry nm snap s ` (~ tmime ) parks ` m\' ` on ` snap ` , '
               '` dup nm t s ` (~ tmidupb ) copies ` n ` onto ` t ` , ` moveEntry snap nm s ` restores ` nm ` , '
               '` dup nm snap s ` copies ` m\' ` onto ` snap ` and ` cmpFrag t snap ` (~ tmicmpb ) compares them.')
    B = Ext(w, ph, TREE_EXT)
    s, c, mk = w.s, B.c, B.mk
    R = B.run()
    wfb = engb(w, ph, 'F', B.fn)
    wfg = encw(w, ph, 'F', B.fn)
    EFI = EWg('F', '( D ` I )')
    B.g(EFI, ewg_(w, ph, 'F', B.fn, '( D ` I )', R.S.vals['I'][2]))
    B.call(R, 'tmime', {'K': 'K0', 'J': 'I', 'I': 'I"', 'P': PL('P', 4), 'E': PL(PL('P', 5), 0), 'W': WF, 'X': EGY},
           {WRD(WF, BITS): wfb, WG(EGY): B.egy}, [('K0', EGY, B.egy), ('I', EFI, B.gam[EFI])])
    S1 = R.S
    EGT = EWg('G', '( D ` I0 )')
    B.g(EGT, ewg_(w, ph, 'G', B.gn, '( D ` I0 )', R.S.vals['I0'][2]))
    B.call(R, 'tmidupb', {'K': 'K0', 'J': 'I0', 'I': 'I"', 'F': 'G', 'N': 'N', 'X': 'Y', 'P': PL('P', 5), 'E': PL(PL('P', 6), 0)},
           {'( %s ` K0 ) = %s' % (S1.D, EGY): S1.vals['K0'][1]}, [('I0', EGT, B.gam[EGT])])
    S2 = R.S
    B.call(R, 'tmime', {'K': 'I', 'J': 'K0', 'I': 'I"', 'P': PL('P', 6), 'E': PL(PL('P', 7), 0), 'W': WF, 'X': '( D ` I )'},
           {WRD(WF, BITS): wfb, '( %s ` I ) = %s' % (S2.D, EFI): S2.vals['I'][1], WG('( D ` I )'): B.gam['( D ` I )']},
           [('I', '( D ` I )', B.gam['( D ` I )']), ('K0', EFGY, B.gam[EFGY])])
    S3 = R.S
    B.call(R, 'tmidupb', {'K': 'K0', 'J': 'I', 'I': 'I"', 'F': 'F', 'N': 'N', 'X': EGY, 'P': PL('P', 7), 'E': PL(PL('P', 8), 0)},
           {'( %s ` K0 ) = %s' % (S3.D, EFGY): S3.vals['K0'][1]}, [('I', EFI, B.gam[EFI])])
    S4 = R.S
    B.call(R, 'tmicmpb', {'K': 'I0', 'J': 'I', 'F': 'G', 'G': 'F', 'N': 'N', 'X': '( D ` I0 )', 'Y': '( D ` I )',
                       'P': PL('P', 8), 'E': PL('P', 0)},
           {'( %s ` I0 ) = %s' % (S4.D, EGT): S4.vals['I0'][1], '( %s ` I ) = %s' % (S4.D, EFI): S4.vals['I'][1],
            WG('( D ` I )'): B.gam['( D ` I )'], WG('( D ` I0 )'): B.gam['( D ` I0 )']},
           [('I0', '( D ` I0 )', B.gam['( D ` I0 )']), ('I', '( D ` I )', B.gam['( D ` I )'])])
    cur, out = R.normalize(K5T)
    assert out == [('K0', EFGY)], out
    t, C, D, n = R.tri, R.C0, R.cur, R.n
    u = upidv(w, ph, 'D', 'K0', EFGY, c['( D ` K0 ) = %s' % EFGY], mk['tv'], B.dd, mk['k']['K0']['kd'])
    t, C, D, n = hrrw(w, ph, t, C, D, n, deq=clneq(w, ph, PL('P', 0), CMPC('G', 'F'), u, UP('D', 'K0', EFGY), 'D'))
    # the bound
    cl = Closure(w, ph, {'F': ('NN0', B.fn), 'G': ('NN0', B.gn), 'N': ('NN0', B.nn)})
    LW = '( # ` %s )' % WF
    cl.leaf(LW, 'NN0', s([wfg, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ph, LW)))
    tb = s([s([B.nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` N ) e. NN0 )' % ph)
    cl.leaf('( TMB ` N )', 'NN0', tb)
    lw = s([s([B.fn, w.inst('encnatgamlen')], 'syl', '( %s -> %s = ( # ` ( encodeNat ` F ) ) )' % (ph, LW)),
            s([B.fn, B.nn, c['F < ( 2 ^ N )'], w.inst('encnatlenpow')], 'syl3anc', '( %s -> ( # ` ( encodeNat ` F ) ) <_ N )' % ph)],
           'eqbrtrd', '( %s -> %s <_ N )' % (ph, LW))
    import num
    l64 = s([num.le_lit(w, '4', '; 6 4')], 'a1i', '( %s -> 4 <_ ; 6 4 )' % ph)
    qd = s([B.nn, closed(w, ph, '4nn0', '4 e. NN0'), l64, w.inst('tmbquad')], 'syl3anc',
           '( %s -> ( 4 x. ( ( N + 2 ) ^ 2 ) ) <_ ( TMB ` N ) )' % ph)
    me = nlinarith(w, ph, [lw, qd, cl.ge0('N'), cl.ge0(LW)], '( ( 2 x. %s ) + 4 ) <_ ( TMB ` N )' % LW, closure=cl,
                   atoms=['N', LW, '( TMB ` N )'])
    le = linarith(w, ph, [me], '%s <_ ( 5 x. ( TMB ` N ) )' % n, closure=cl, atoms=[LW, '( TMB ` N )'])
    hrle(w, ph, mk['phm'], t, C, D, n, '( 5 x. ( TMB ` N ) )', cl.mem('( 5 x. ( TMB ` N ) )', 'NN0'), le, qed=True)
    return w.run()


FINC = NFLi('( G < F \\/ S = (/) )')
DK3 = UP('D', 'K', 'if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) )')


def clt_test(w, pc, B, truth):
    """( pc -> A. m e. CMPC ( CLT ` m ) = 1o ) (truth) or ( ... -. ... ) from the case G < F / -. G < F"""
    s = w.s
    N0 = CMPC('G', 'F')
    XL = lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t
    pm = '( %s /\\ m e. %s )' % (pc, N0)
    mi = s([], 'simpr', '( %s -> m e. %s )' % (pm, N0))
    cond = lambda t: '( TMcmp ` %s ) = ( G Ncmp F )' % t
    idh = s([], 'id', '( h = m -> h = m )')
    cg, new = w.wcongr(cond('h'), {'h': 'm'}, 'h = m', {'h': idh})
    el = s([cg], 'elrab', '( m e. %s <-> ( m e. TMSt /\\ %s ) )' % (N0, cond('m')))
    both = s([mi, el], 'sylib', '( %s -> ( m e. TMSt /\\ %s ) )' % (pm, cond('m')))
    mm = s([both], 'simpld', '( %s -> m e. TMSt )' % pm)
    mc = s([both], 'simprd', '( %s -> %s )' % (pm, cond('m')))
    xex = ifex_closed(w, pm, '( TMcmp ` m ) = (/)', '1o', '(/)', s([], '1oex', '1o e. _V'), s([], '0ex', '(/) e. _V'))
    cv = mval(w, pm, 'u', 'TMSt', XL, 'm', mm, xex)
    Lm = lambda st: s([st], 'adantr', '( %s -> %s )' % (pm, concl(w, pc, st)))
    nl = s([s([B.gn, B.fn], 'jca', '( %s -> ( G e. NN0 /\\ F e. NN0 ) )' % pc), w.inst('ncmplt')], 'syl',
           '( %s -> ( ( G Ncmp F ) = (/) <-> G < F ) )' % pc)
    cnd = s([], 'simpr', '( %s -> %s )' % (pc, 'G < F' if truth else '-. G < F'))
    if truth:
        nc0 = s([cnd, nl], 'mpbird', '( %s -> ( G Ncmp F ) = (/) )' % pc)
        cm0 = s([mc, Lm(nc0)], 'eqtrd', '( %s -> ( TMcmp ` m ) = (/) )' % pm)
        v = s([cv, s([cm0], 'iftrued', '( %s -> %s = 1o )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = 1o )' % (pm, CLT))
        return s([v], 'ralrimiva', '( %s -> A. m e. %s ( %s ` m ) = 1o )' % (pc, N0, CLT))
    nn0 = s([cnd, nl], 'mtbird', '( %s -> -. ( G Ncmp F ) = (/) )' % pc)
    cm1 = s([Lm(nn0), s([mc], 'eqeq1d', '( %s -> ( ( TMcmp ` m ) = (/) <-> ( G Ncmp F ) = (/) ) )' % pm)], 'mtbird',
            '( %s -> -. ( TMcmp ` m ) = (/) )' % pm)
    c0 = s([cv, s([cm1], 'iffalsed', '( %s -> %s = (/) )' % (pm, XL('m')))], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pm, CLT))
    return s([not1o(w, pm, c0, CLT, 'm')], 'ralrimiva', '( %s -> A. m e. %s -. ( %s ` m ) = 1o )' % (pc, N0, CLT))


def label_goto_ty(w, ph, B, X):
    """( ph -> <. 5 , ( S X. { X } ) >. e. ( TM2Stmt ` T ) ) from the label typing of X"""
    return gotocl(w, ph, B.mk['tv'], X, B.ex[LAB(X)])


def tmiext():
    lab = 'tmiext'
    ph = cj(TREE_EXT)
    w = W(lab, 'Lean\'s ` exTest_runs ` at the machine: wherever ` exTest np snap s t nm ` is installed, with ` m\' ` above ` n ` '
               'on ` nm ` , the flag ends up ` n < m\' \\/ P\' = [] ` , the marker ` ket ` is pushed on ` np ` exactly when '
               '` n < m\' ` , every other stack restored, within ` 5 B bM + 3 ` steps (the prefix ~ tmiexta , then '
               '` ite ( cmp = lt ) ( pushSym np ket ; load\' ( flag := true ) ) ( peekBra np ) ` by cases).')
    s = w.s
    N0 = CMPC('G', 'F')
    Q1, Q2, Q3, Q4 = PL('P', 0), PL('P', 1), PL('P', 2), PL('P', 3)
    BND = EXTC
    pre = s([], 'tmiexta', ST_A)
    outs = []
    for truth in (True, False):
        cnd = 'G < F' if truth else '-. G < F'
        pc = '( %s /\\ %s )' % (ph, cnd)
        B = Ext(w, pc, (TREE_EXT, cnd), eqK=not truth)
        c, mk = B.c, B.mk
        ex = {CTY(CLT): lamty(w, pc, mk, CLT, lambda t: 'if ( ( TMcmp ` %s ) = (/) , 1o , (/) )' % t, '2o', s([], '2oex', '2o e. _V'),
                               s([s([], '1oel2o', '1o e. 2o'), s([], '0el2o', '(/) e. 2o')], 'ifcli',
                                 'if ( ( TMcmp ` u ) = (/) , 1o , (/) ) e. 2o')),
              SSS(N0): B.ss(N0), SSS(FINC): B.ss(FINC)}
        R = B.run()
        if truth:
            ex[STMT(GT(Q4))] = label_goto_ty(w, pc, B, Q4)
            ex['A. m e. %s ( %s ` m ) = 1o' % (N0, CLT)] = clt_test(w, pc, B, True)
            B.call(R, 'tm2lbrt', {'A': Q1, 'C': CLT, 'E': Q2, 'Q': GT(Q4), 'N': N0}, ex, [])
            K3W = CC('<" 3 ">', '( D ` K )')
            k3g = wgcat(w, pc, '<" 3 ">', '( D ` K )', s([closed(w, pc, 'gamma3', "3 e. Gamma'")], 's1cld',
                                                          "( %s -> <\" 3 \"> e. Word Gamma' )" % pc), R.S.vals['K'][2])
            ex['3 e. %s' % GX('K')] = s([closed(w, pc, 'gamma3', "3 e. Gamma'"), mk['k']['K']['ge']], 'eleqtrrd',
                                         '( %s -> 3 e. %s )' % (pc, GX('K')))
            B.call(R, 'tm2fpshn', {'A': Q2, 'E': Q3, 'K': 'K', 'Z': '3', 'N': N0}, ex, [('K', K3W, k3g)])
            # load' ( flag := true ) into FINC
            kw = lambda t: dict(fl='1o')
            ex[LTY(LFL1)] = lset_ty(w, pc, mk, LFL1, kw)
            pr = '( %s /\\ r e. %s )' % (pc, N0)
            rn = s([], 'simpr', '( %s -> r e. %s )' % (pr, N0))
            rs = s([s([Lft(w, pr, pc, B.ss(N0)), rn], 'sseldd', '( %s -> r e. %s )' % (pr, S)), Lft(w, pr, pc, mk['seq'])], 'eleqtrd',
                   '( %s -> r e. TMSt )' % pr)
            nv = lset_val(w, pr, kw, 'r', rs)
            NR = '( %s ` r )' % LFL1
            ift = s([s([Lft(w, pr, pc, s([], 'simpr', '( %s -> G < F )' % pc))], 'orcd', '( %s -> ( G < F \\/ S = (/) ) )' % pr)],
                    'iftrued', '( %s -> if ( ( G < F \\/ S = (/) ) , 1o , (/) ) = 1o )' % pr)
            flv = s([nv['fields']['fl'], s([ift], 'eqcomd', '( %s -> 1o = if ( ( G < F \\/ S = (/) ) , 1o , (/) ) )' % pr)], 'eqtrd',
                    '( %s -> ( TMfl ` %s ) = if ( ( G < F \\/ S = (/) ) , 1o , (/) ) )' % (pr, NR))
            inm = A8.nfl_pack(w, pr, 'if ( ( G < F \\/ S = (/) ) , 1o , (/) )', NR, nv['mem'], flv)
            ex['A. r e. %s ( %s ` r ) e. %s' % (N0, LFL1, FINC)] = s([inm], 'ralrimiva', '( %s -> A. r e. %s ( %s ` r ) e. %s )' % (pc, N0, LFL1, FINC))
            B.call(R, 'tm2flg', {'A': Q3, 'E': 'E', 'F': LFL1, 'N': N0, "N'": FINC}, ex, [])
            # stacks: UPD( D , K , <" 3 "> ++ ( D ` K ) ) = DK3
            ife = s([s([], 'simpr', '( %s -> G < F )' % pc)], 'iftrued',
                    '( %s -> if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) ) = %s )' % (pc, K3W))
            deq = upeq(w, pc, 'D', 'K', s([ife], 'eqcomd', '( %s -> %s = if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) ) )' % (pc, K3W)),
                       K3W, 'if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) )')
            nb = '( ( 1 + 1 ) + 1 )'
        else:
            ex[STMT(GT(Q2))] = label_goto_ty(w, pc, B, Q2)
            ex['A. m e. %s -. ( %s ` m ) = 1o' % (N0, CLT)] = clt_test(w, pc, B, False)
            B.call(R, 'tm2fbrg', {'A': Q1, 'C': CLT, 'E': Q4, 'Q': GT(Q2), 'N': N0}, ex, [])
            # peekBra np
            V = ENCL('S', 'X')
            vw = R.S.vals['K'][2]
            vn0 = encl_ne0(w, pc, 'S', B.vw, 'X', B.xw)
            eq, hg, tg = A8.word_split(w, pc, V, vw, vn0)
            HD, TL = A8.HD0(V), A8.TL1(V)
            kv = s([R.S.vals['K'][1], eq], 'eqtrd', '( %s -> ( D ` K ) = ( <" %s "> ++ %s ) )' % (pc, HD, TL))
            hb = s([B.vw, B.xw, w.inst('tmexhdb')], 'syl2anc', '( %s -> ( %s = 2 <-> S = (/) ) )' % (pc, HD))
            ncnd = s([], 'simpr', '( %s -> -. G < F )' % pc)
            orb = s([ncnd, w.inst('biorf')], 'syl', '( %s -> ( S = (/) <-> ( G < F \\/ S = (/) ) ) )' % pc)
            hb2 = s([hb, orb], 'bitrd', '( %s -> ( %s = 2 <-> ( G < F \\/ S = (/) ) ) )' % (pc, HD))
            ifeq = s([hb2], 'ifbid', '( %s -> if ( %s = 2 , 1o , (/) ) = if ( ( G < F \\/ S = (/) ) , 1o , (/) ) )' % (pc, HD))
            pk = A8.peek_iface(w, pc, mk, RDBRA, HD, hg, ifeq, 'if ( ( G < F \\/ S = (/) ) , 1o , (/) )')
            IF_ = 'A. r e. %s ( TMrdBra ` <. r , ( inl ` %s ) >. ) e. %s' % (S, HD, FINC)
            pkN = s([B.ss(N0), pk, w.inst('ssralv')], 'sylc', '( %s -> A. r e. %s ( TMrdBra ` <. r , ( inl ` %s ) >. ) e. %s )' % (pc, N0, HD, FINC))
            ex.update({'( D ` K ) = ( <" %s "> ++ %s )' % (HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg,
                       'A. r e. %s ( TMrdBra ` <. r , ( inl ` %s ) >. ) e. %s' % (N0, HD, FINC): pkN})
            B.call(R, 'tm2lpk', {'A': Q4, 'E': 'E', 'K': 'K', 'F': RDBRA, 'Z': HD, 'X': TL, 'N': N0, "N'": FINC}, ex, [])
            ife = s([ncnd], 'iffalsed', '( %s -> if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) ) = ( D ` K ) )' % pc)
            u = upidv(w, pc, 'D', 'K', 'if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) )',
                      s([ife], 'eqcomd', '( %s -> ( D ` K ) = if ( G < F , ( <" 3 "> ++ ( D ` K ) ) , ( D ` K ) ) )' % pc),
                      mk['tv'], B.dd, mk['k']['K']['kd'])
            deq = s([u], 'eqcomd', '( %s -> D = %s )' % (pc, DK3))
            nb = '( 1 + 1 )'
        t, C, D, n = R.tri, R.C0, R.cur, R.n
        t, C, D, n = hrrw(w, pc, t, C, D, n, deq=clneq(w, pc, 'E', FINC, deq, D.split(' } ) ) ')[0].split('X. { ', 1)[1] if False else
                                                      triple_parts_D(D), DK3))
        tp = Lft(w, pc, ph, pre)
        C0_, D0_, n0_ = triple_parts(concl(w, ph, pre))
        t2 = hrseq(w, pc, mk['phm'], tp, t, C0_, D0_, D, n0_, n)
        NT = '( %s + %s )' % (n0_, n)
        cl = Closure(w, pc, {'N': ('NN0', B.nn)})
        tb = s([s([B.nn, w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` N ) e. NN )' % pc)], 'nnnn0d', '( %s -> ( TMB ` N ) e. NN0 )' % pc)
        cl.leaf('( TMB ` N )', 'NN0', tb)
        le = linarith(w, pc, [], '%s <_ %s' % (NT, BND), closure=cl, atoms=['( TMB ` N )'])
        outs.append(hrle(w, pc, mk['phm'], t2, C0_, D, NT, BND, cl.mem(BND, 'NN0'), le))
    w.qed(outs, 'pm2.61dan', STMTS9['tmiext'])
    return w.run()


def triple_parts_D(Dcls):
    """the stack term of a class text C( A , N , D )"""
    tail = Dcls.rsplit(' X. { ', 1)[1]
    assert tail.endswith(' } ) )')
    return tail[:-len(' } ) )')]


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
