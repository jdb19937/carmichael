"""T7b: the loops of the division at the machine: the blocks of ~ tm2fdmcv 's
antecedent for the shift-up loop ( tmidmuq ) and the shift-down loop
( tmidmd1 , tmidmd2 , tmidmd3 , tmidmdt ), at the families of blueprint
section 3.

    MM_DB=sorties/t7b.mm python3 tools/gen/t7b_h_dmq.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t7blib import *
from cl import Closure
from lin import linarith, lineq, nlinarith
from t7_e_cmp import machine
from t7b_g_dmu import STMT_UB, STMT_DDC, STMT_DSI, NCM, MXLL, MXA_

SEL = sys.argv[1:]

_GA, _GC = split_imp(stmt('tm2fdmcv'))
T_GDM = parse_conj(_GA)
ENF = '( encNatGam ` F )'
K5U = ['K', 'J', "I'", 'I"', 'I0']
DATA_U = ((('F e. NN0', 'G e. NN', 'R e. NN0'), ('R <_ %s' % NF, 'F < ( ( 2 ^ R ) x. G )',
                                                  'A. y e. ( 0 ..^ R ) ( ( 2 ^ y ) x. G ) <_ F')),
          ((WRD('X', GAM), WRD('Y', GAM), STKD('D')), '( D ` K ) = %s' % CC(ENF, YXt('X'))))


def UMAP(P='P', E='E'):
    return {"Y'": YUF, "Q'": QUF, "N'": NUF, "B'": PL(PL(P, 1), 0), 'A': E, "U'": UPB, 'Z0': Z0B, 'C0': CNGT}


def STMT_UQ():
    f = FRAGS['dmu']
    tree = ((T_PHM7, f.pred()), (idx_tree(K5U), dist_tree(K5U)), DATA_U)
    m = UMAP()
    typ = tsub_text(T_GDM[0][1][1][0][0], m)
    per = tsub_text(T_GDM[0][1][1][0][1], m)
    ex = tsub_text(T_GDM[0][1][1][1], m)
    assert ex.startswith('A. m e. ( %s ` R )' % NUF), ex
    return tree, '( %s /\\ ( %s /\\ %s ) )' % (typ, per, ex)


def fv(w, ph, F_, body, t, tn, xex, v='k'):
    """( ph -> ( F_ ` t ) = body( t ) ) for F_ = ( v e. NN0 |-> body( v ) )"""
    assert F_ == '( %s e. NN0 |-> %s )' % (v, body(v)), (F_, body(v))
    return mval(w, ph, v, 'NN0', body, t, tn, xex)


def rabv(w, ph, rab):
    return rabV(w, ph, rab)


def cngt_val(w, ph, m, mem, cmp_eq, val, gt_false):
    """( ph -> ( CNGT ` m ) = 1o ) from mem : m e. TMSt, cmp_eq : ( TMcmp ` m ) = val and
    gt_false : -. val = 2o"""
    X_of = lambda t: 'if ( ( TMcmp ` %s ) = 2o , (/) , 1o )' % t
    z0 = w.s([], '0ex', '(/) e. _V'); o1 = w.s([], '1oex', '1o e. _V')
    xex = ifex_closed(w, ph, '( TMcmp ` %s ) = 2o' % m, '(/)', '1o', z0, o1)
    v = mval(w, ph, 'u', 'TMSt', X_of, m, mem, xex)
    e = w.s([cmp_eq], 'eqeq1d', '( %s -> ( ( TMcmp ` %s ) = 2o <-> %s = 2o ) )' % (ph, m, val))
    n = w.s([e, gt_false], 'mtbird', '( %s -> -. ( TMcmp ` %s ) = 2o )' % (ph, m))
    it = w.s([n], 'iffalsed', '( %s -> %s = 1o )' % (ph, X_of(m)))
    return w.s([v, it], 'eqtrd', '( %s -> ( %s ` %s ) = 1o )' % (ph, CNGT, m))


def rab_elim(w, ph, rab, cond_fn, x, xin):
    """from xin : ( ph -> x e. rab ), rab = { h e. TMSt | cond( h ) } : (x e. TMSt, cond( x ))"""
    idh = w.s([], 'id', '( h = %s -> h = %s )' % (x, x))
    cg, new = w.wcongr(cond_fn('h'), {'h': x}, 'h = %s' % x, {'h': idh})
    assert new == cond_fn(x), (new, cond_fn(x))
    el = w.s([cg], 'elrab', '( %s e. %s <-> ( %s e. TMSt /\\ %s ) )' % (x, rab, x, cond_fn(x)))
    both = w.s([xin, el], 'sylib', '( %s -> ( %s e. TMSt /\\ %s ) )' % (ph, x, cond_fn(x)))
    return w.s([both], 'simpld', '( %s -> %s e. TMSt )' % (ph, x)), w.s([both], 'simprd', '( %s -> %s )' % (ph, cond_fn(x)))


def ifmax_le(w, ph, A, B, C, ar, br, cr, ale, ble):
    """( ph -> if ( A <_ B , B , A ) <_ C ) by maxle"""
    MX = 'if ( %s <_ %s , %s , %s )' % (A, B, B, A)
    mb = w.s([ar, br, cr, w.inst('maxle')], 'syl3anc', '( %s -> ( %s <_ %s <-> ( %s <_ %s /\\ %s <_ %s ) ) )' % (ph, MX, C, A, C, B, C))
    return w.s([mb, w.s([ale, ble], 'jca', '( %s -> ( %s <_ %s /\\ %s <_ %s ) )' % (ph, A, C, B, C))], 'mpbird', '( %s -> %s <_ %s )' % (ph, MX, C))


def tmidmuq():
    lab = 'tmidmuq'
    T, C = STMT_UQ()
    ph = cj(T)
    w = W(lab, 'The shift-up loop of Lean\'s ` divmodCore ` at the machine (Lean ` DmUpInv ` , ` dmUpBody_runs ` ): '
               'the families ` Y\' ` (the divisor shifted by ` i ` on ` y ` ), ` Q\' ` ( ` i ` on ` j ` ) and ` N\' ` '
               '( ` cmp = compare ( 2 ^ i d ) a ` ) are typed, the loop test holds below the number of doublings '
               '` R ` and fails at ` R ` , and each iteration runs within ` U\' = 7 n + 3 g + 15 ` .')
    c = Ctx(w, ph, T)
    mk = machine(w, ph, c, K5U)
    phm, tv, seq = mk['phm'], mk['tv'], mk['seq']
    ne = ne_fn(w, ph, c, set(flat(dist_tree(K5U))))
    fn, gn, rn = c['F e. NN0'], c['G e. NN'], c['R e. NN0']
    rle, rlt, rmin = c['R <_ %s' % NF], c['F < ( ( 2 ^ R ) x. G )'], c['A. y e. ( 0 ..^ R ) ( ( 2 ^ y ) x. G ) <_ F']
    xg, yg, dd = c[WRD('X', GAM)], c[WRD('Y', GAM)], c[STKD('D')]
    dk = c['( D ` K ) = %s' % CC(ENF, YXt('X'))]
    gn0 = w.s([gn, w.inst('nnnn0')], 'syl', '( %s -> G e. NN0 )' % ph)
    eg = w.s([gn0, w.inst('encnatcl')], 'syl', '( %s -> %s e. Word 2o )' % (ph, EG))
    ef = w.s([fn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` F ) e. Word 2o )' % ph)
    b0 = closed(w, ph, '0el2o', '(/) e. 2o')
    dip = w.s([stkfv(w, ph, 'D', "I'", tv, dd, mk['k']["I'"]['kd']), mk['k']["I'"]['wge']], 'eleqtrd', "( %s -> ( D ` I' ) e. Word Gamma' )" % ph)
    ssS = lambda rab: w.s([w.s([w.s([], 'ssrab2', '%s C_ TMSt' % rab)], 'a1i', '( %s -> %s C_ TMSt )' % (ph, rab)), seq], 'sseqtrrd',
                          '( %s -> %s C_ ( 2nd ` T ) )' % (ph, rab))

    def words_at(ps, t, tn):
        """steps under ps: SHG( t ) e. Word 2o, YUB( t ) e. Word Gamma', QUB( t ) e. Word Gamma', family values"""
        L = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (ps, concl(w, ph, st)))
        rw = w.s([L(b0), tn, w.inst('repsw')], 'syl2anc', '( %s -> ( (/) repeatS %s ) e. Word 2o )' % (ps, t))
        sh = w.s([rw, L(eg), w.inst('ccatcl')], 'syl2anc', '( %s -> %s e. Word 2o )' % (ps, SHG(t)))
        yw = wgcat(w, ps, '( inclBool o. %s )' % SHG(t), YXt('Y'), wib(w, ps, SHG(t), sh), wg4(w, ps, 'Y', L(yg)))
        eqg = w.s([tn, w.inst('encnatgamcl')], 'syl', "( %s -> ( encNatGam ` %s ) e. Word Gamma' )" % (ps, t))
        qw = wgcat(w, ps, '( encNatGam ` %s )' % t, YXt("( D ` I' )"), eqg, wg4(w, ps, "( D ` I' )", L(dip)))
        yv = fv(w, ps, YUF, YUB, t, tn, w.s([yw], 'elexd', '( %s -> %s e. _V )' % (ps, YUB(t))))
        qv = fv(w, ps, QUF, QUB, t, tn, w.s([qw], 'elexd', '( %s -> %s e. _V )' % (ps, QUB(t))))
        nv = fv(w, ps, NUF, NUB, t, tn, rabV(w, ps, NUB(t)))
        return dict(sh=sh, yw=yw, qw=qw, yv=yv, qv=qv, nv=nv, rw=rw)

    # ---------------- typing over ( 0 ... R )
    pt = '( %s /\\ i e. ( 0 ... R ) )' % ph
    iz = w.s([], 'simpr', '( %s -> i e. ( 0 ... R ) )' % pt)
    itn = w.s([iz, w.inst('elfznn0')], 'syl', '( %s -> i e. NN0 )' % pt)
    wa = words_at(pt, 'i', itn)
    Lt = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pt, concl(w, ph, st)))
    togk_ = lambda ps, X, s, g, lift: w.s([g, lift(mk['k'][s]['wge'])], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(s)))
    y1 = w.s([wa['yv'], togk_(pt, YUB('i'), 'J', wa['yw'], Lt)], 'eqeltrd', '( %s -> ( %s ` i ) e. Word %s )' % (pt, YUF, GX('J')))
    q1 = w.s([wa['qv'], togk_(pt, QUB('i'), "I'", wa['qw'], Lt)], 'eqeltrd', "( %s -> ( %s ` i ) e. Word %s )" % (pt, QUF, GX("I'")))
    n1 = w.s([wa['nv'], w.s([ssS(NUB('i'))], 'adantr', '( %s -> %s C_ ( 2nd ` T ) )' % (pt, NUB('i')))], 'eqsstrd',
             '( %s -> ( %s ` i ) C_ ( 2nd ` T ) )' % (pt, NUF))
    TY = '( ( ( %s ` i ) e. Word %s /\\ ( %s ` i ) e. Word %s ) /\\ ( %s ` i ) C_ ( 2nd ` T ) )' % (YUF, GX('J'), QUF, GX("I'"), NUF)
    ty = w.s([w.s([y1, q1], 'jca', '( %s -> ( ( %s ` i ) e. Word %s /\\ ( %s ` i ) e. Word %s ) )' % (pt, YUF, GX('J'), QUF, GX("I'"))), n1],
             'jca', '( %s -> %s )' % (pt, TY))
    typ = w.s([ty], 'ralrimiva', '( %s -> A. i e. ( 0 ... R ) %s )' % (ph, TY))
    # ---------------- per iteration
    ps = '( %s /\\ i e. ( 0 ..^ R ) )' % ph
    L = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (ps, concl(w, ph, st)))
    ii = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ R ) )' % ps)
    inn = w.s([ii, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % ps)
    ilt = w.s([ii, w.inst('elfzolt2')], 'syl', '( %s -> i < R )' % ps)
    i1 = '( i + 1 )'
    i1n = w.s([inn, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (ps, i1))
    w0 = words_at(ps, 'i', inn)
    w1 = words_at(ps, i1, i1n)
    # Y' step
    v1 = w.s([L(eg), inn, w.inst('tmidvw1')], 'syl2anc', '( %s -> ( inclBool o. %s ) = ( <" %s "> ++ ( inclBool o. %s ) ) )'
             % (ps, SHG(i1), Z0B, SHG('i')))
    v2 = w.s([v1], 'oveq1d', '( %s -> %s = ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) )' % (ps, YUB(i1), Z0B, SHG('i'), YXt('Y')))
    z0g = w.s([w.s([closed(w, ps, '0el2o', '(/) e. 2o'), closed(w, ps, 'inclboolf', "inclBool : 2o --> Gamma'")], 'ffvelcdmd' if False else 'jca', '') if False else None], '', '') if False else None
    z0g = closed(w, ps, 'tm2lbit0' if False else 'gammabit0', "%s e. Gamma'" % Z0B) if False else None
    s1z = w.s([w.s([w.s([], '0el2o', '(/) e. 2o'), w.inst('inclboolfv')], 'ax-mp', '( inclBool ` (/) ) = %s' % Z0B)], 'id', '') if False else None
    # <" Z0 "> e. Word Gamma' : Z0 e. Gamma' via inclBool : 2o --> Gamma'
    zf = closed(w, ps, 'inclboolf', "inclBool : 2o --> Gamma'")
    zv = w.s([zf, closed(w, ps, '0el2o', '(/) e. 2o')], 'ffvelcdmd', "( %s -> ( inclBool ` (/) ) e. Gamma' )" % ps)
    zeq = w.s([closed(w, ps, '0el2o', '(/) e. 2o'), w.inst('inclboolfv')], 'syl', '( %s -> ( inclBool ` (/) ) = %s )' % (ps, Z0B))
    zg = w.s([zv, zeq], 'eqeltrrd' if False else 'eqeltrd', '') if False else w.s([zeq, zv], 'eqeltrrd', "( %s -> %s e. Gamma' )" % (ps, Z0B))
    s1g = w.s([zg], 's1cld', "( %s -> <\" %s \"> e. Word Gamma' )" % (ps, Z0B))
    ca = w.s([s1g, wib(w, ps, SHG('i'), w0['sh']), wg4(w, ps, 'Y', L(yg)), w.inst('ccatass')], 'syl3anc',
             '( %s -> ( ( <" %s "> ++ ( inclBool o. %s ) ) ++ %s ) = ( <" %s "> ++ %s ) )' % (ps, Z0B, SHG('i'), YXt('Y'), Z0B, YUB('i')))
    ys = w.s([v2, ca], 'eqtrd', '( %s -> %s = ( <" %s "> ++ %s ) )' % (ps, YUB(i1), Z0B, YUB('i')))
    ysf0 = w.s([w0['yv']], 's1eqd' if False else 'oveq2d', '( %s -> ( <" %s "> ++ ( %s ` i ) ) = ( <" %s "> ++ %s ) )' % (ps, Z0B, YUF, Z0B, YUB('i')))
    YSTEP = '( %s ` %s ) = ( <" %s "> ++ ( %s ` i ) )' % (YUF, i1, Z0B, YUF)
    yst = w.s([w.s([w1['yv'], ys], 'eqtrd', '( %s -> ( %s ` %s ) = ( <" %s "> ++ %s ) )' % (ps, YUF, i1, Z0B, YUB('i'))), ysf0], 'eqtr4d',
              '( %s -> %s )' % (ps, YSTEP))
    # the loop test on ( N' ` i )
    pm = '( %s /\\ m e. ( %s ` i ) )' % (ps, NUF)
    mi = w.s([w.s([], 'simpr', '( %s -> m e. ( %s ` i ) )' % (pm, NUF)), w.s([w0['nv']], 'adantr', '( %s -> ( %s ` i ) = %s )' % (pm, NUF, NUB('i')))],
             'eleqtrd', '( %s -> m e. %s )' % (pm, NUB('i')))
    VAL = '( ( ( 2 ^ i ) x. G ) Ncmp F )'
    mm, mc = rab_elim(w, pm, NUB('i'), lambda h: '( TMcmp ` %s ) = %s' % (h, VAL), 'm', mi)
    # -. VAL = 2o : ncmpgt, minimality
    rmi = w.s([w.s([], 'eqid' if False else 'id', '') ], '', '') if False else None
    idi = w.s([], 'id', '( i = i -> i = i )') if False else None
    mn = w.s([L(rmin), ii, w.inst('rspcv' if False else 'rsp')], 'sylc' if False else '', '') if False else None
    rsp_ = w.s([L(rmin)], 'r19.21bi' if False else 'id', '') if False else None
    idy = w.s([], 'id', '( y = i -> y = i )')
    cgy, newy = w.wcongr('( ( 2 ^ y ) x. G ) <_ F', {'y': 'i'}, 'y = i', {'y': idy})
    mnn = w.s([cgy, L(rmin), ii], 'rspcdva', '( %s -> ( ( 2 ^ i ) x. G ) <_ F )' % ps)
    cps = Closure(w, ps, {'i': ('NN0', inn), 'G': ('NN', L(gn)), 'F': ('NN0', L(fn)), 'R': ('NN0', L(rn))})
    X2 = '( ( 2 ^ i ) x. G )'
    x2n = cps.mem(X2, 'NN0'); fn0 = cps.mem('F', 'NN0')
    gt = w.s([x2n, fn0, w.inst('ncmpgt')], 'syl2anc', '( %s -> ( %s = 2o <-> F < %s ) )' % (ps, VAL, X2))
    nl = w.s([cps.mem(X2, 'RR'), cps.mem('F', 'RR')], 'lenltd', '( %s -> ( %s <_ F <-> -. F < %s ) )' % (ps, X2, X2))
    nlt = w.s([mnn, nl], 'mpbid', '( %s -> -. F < %s )' % (ps, X2))
    ng = w.s([gt, nlt], 'mtbird', '( %s -> -. %s = 2o )' % (ps, VAL))
    cv = cngt_val(w, pm, 'm', mm, mc, VAL, w.s([ng], 'adantr', '( %s -> -. %s = 2o )' % (pm, VAL)))
    ht = w.s([cv], 'ralrimiva', '( %s -> A. m e. ( %s ` i ) ( %s ` m ) = 1o )' % (ps, NUF, CNGT))
    # the iteration's triple by tmidmub
    kk = mk['k']
    Lk = lambda s, key: L(kk[s][key])
    togk = lambda X, s, g: w.s([g, Lk(s, 'wge')], 'eleqtrrd', '( %s -> %s e. Word %s )' % (ps, X, GX(s)))
    YI, YI1, QI, QI1 = FAPP(YUF, 'i'), FAPP(YUF, i1), FAPP(QUF, 'i'), FAPP(QUF, i1)
    yig = w.s([w0['yv'], w0['yw']], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ps, YI))
    yi1g = w.s([w1['yv'], w1['yw']], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ps, YI1))
    qig = w.s([w0['qv'], w0['qw']], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ps, QI))
    qi1g = w.s([w1['qv'], w1['qw']], 'eqeltrd', "( %s -> %s e. Word Gamma' )" % (ps, QI1))
    ne_ps = lambda a, b: w.s([ne(a, b)], 'adantr', '( %s -> %s =/= %s )' % (ps, a, b))
    vals = {'K': (CC(ENF, YXt('X')), L(dk), None)}
    S0 = Stacks(w, ps, {'tv': L(tv), 'k': {s: {'kd': Lk(s, 'kd'), 'wge': Lk(s, 'wge')} for s in K5U}}, 'D', L(dd), ne_ps,
                {'K': (CC(ENF, YXt('X')), L(dk), None)})
    Sa = S0.upd('J', YI, yig)
    Sb = Sa.upd("I'", QI, qig)
    Sc = Sb.upd('J', YI1, yi1g)
    DP = Sc.D
    # data for tmidmub
    egf = w.s([L(fn), w.inst('encnatgamval')], 'syl', '( %s -> %s = ( inclBool o. ( encodeNat ` F ) ) )' % (ps, ENF))
    WXF = CC('( inclBool o. ( encodeNat ` F ) )', YXt('X'))
    dkp = w.s([Sc.val('K')[1], w.s([egf], 'oveq1d', '( %s -> ( %s ++ %s ) = %s )' % (ps, ENF, YXt('X'), WXF))], 'eqtrd',
              '( %s -> ( %s ` K ) = %s )' % (ps, DP, WXF))
    WYS = CC('( inclBool o. %s )' % SHG(i1), YXt('Y'))
    djp = w.s([Sc.val('J')[1], w1['yv']], 'eqtrd', '( %s -> ( %s ` J ) = %s )' % (ps, DP, WYS))
    WQI = CC('( encNatGam ` i )', YXt("( D ` I' )"))
    dqp = w.s([Sc.val("I'")[1], w0['qv']], 'eqtrd', "( %s -> ( %s ` I' ) = %s )" % (ps, DP, WQI))
    cps2 = Closure(w, ps, {})
    extra = {'C e. NN0': inn, WRD('L', '2o'): None}
    m = {'C': 'i', 'L': '( encodeNat ` F )', "L'": SHG(i1), 'X': 'X', 'Y': 'Y', 'Q': "( D ` I' )", 'D': DP}
    T_UB, C_UB = STMT_UB()
    cub = Ctx(w, ps, T, root=w.s([], 'simpl', '( %s -> %s )' % (ps, ph)))
    ex = {'i e. NN0': inn, WRD('( encodeNat ` F )', '2o'): L(ef), WRD(SHG(i1), '2o'): w1['sh'], WRD("( D ` I' )", GAM): L(dip),
          STKD(DP): Sc.memb, '( %s ` K ) = %s' % (DP, WXF): dkp, '( %s ` J ) = %s' % (DP, WYS): djp, "( %s ` I' ) = %s" % (DP, WQI): dqp}
    for leaf_ in flat(T):
        if leaf_ not in ex:
            ex[leaf_] = cub[leaf_]
    t1, c1 = inst(w, ps, 'tmidmub', m, Bld(w, ps, cub, ex))
    Ca, Da, n1 = triple_parts(c1)
    # pre class ( N' ` i ) C_ S
    nss = w.s([w0['nv'], w.s([ssS(NUB('i'))], 'adantr', '( %s -> %s C_ ( 2nd ` T ) )' % (ps, NUB('i')))], 'eqsstrd',
              '( %s -> ( %s ` i ) C_ ( 2nd ` T ) )' % (ps, NUF))
    B1 = PL(PL('P', 1), 0)
    Cn = CLN(B1, FAPP(NUF, 'i'), DP)
    t2 = hrssc(w, ps, L(phm), t1, Ca, Da, n1, Cn, clnss(w, ps, B1, FAPP(NUF, 'i'), SS, DP, nss))
    # post: class and stacks
    NCMI = tsub_text(NCM, m)
    tsh = w.s([L(eg), i1n, w.inst('tonatrep0a')], 'syl2anc', '( %s -> ( toNat ` %s ) = ( ( 2 ^ %s ) x. ( toNat ` %s ) ) )' % (ps, SHG(i1), i1, EG))
    tg = w.s([L(gn0), w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` %s ) = G )' % (ps, EG))
    tsh2 = w.s([tsh, w.s([tg], 'oveq2d', '( %s -> ( ( 2 ^ %s ) x. ( toNat ` %s ) ) = ( ( 2 ^ %s ) x. G ) )' % (ps, i1, EG, i1))], 'eqtrd',
               '( %s -> ( toNat ` %s ) = ( ( 2 ^ %s ) x. G ) )' % (ps, SHG(i1), i1))
    tf = w.s([L(fn), w.inst('tonatencnat')], 'syl', '( %s -> ( toNat ` ( encodeNat ` F ) ) = F )' % ps)
    vv = w.s([tsh2, tf], 'oveq12d', '( %s -> ( ( toNat ` %s ) Ncmp ( toNat ` ( encodeNat ` F ) ) ) = ( ( ( 2 ^ %s ) x. G ) Ncmp F ) )' % (ps, SHG(i1), i1))
    ce = w.s([vv], 'eqeq2d', '( %s -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` ( encodeNat ` F ) ) ) <-> ( TMcmp ` h ) = ( ( ( 2 ^ %s ) x. G ) Ncmp F ) ) )'
             % (ps, SHG(i1), i1))
    rb = w.s([w.s([ce], 'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMcmp ` h ) = ( ( toNat ` %s ) Ncmp ( toNat ` ( encodeNat ` F ) ) ) <-> ( TMcmp ` h ) = ( ( ( 2 ^ %s ) x. G ) Ncmp F ) ) )' % (ps, SHG(i1), i1))],
             'rabbidva', '( %s -> %s = %s )' % (ps, NCMI, NUB(i1)))
    ncls = w.s([rb, w.s([w1['nv']], 'eqcomd', '( %s -> %s = ( %s ` %s ) )' % (ps, NUB(i1), NUF, i1))], 'eqtrd', '( %s -> %s = ( %s ` %s ) )' % (ps, NCMI, NUF, i1))
    POST0 = UP(DP, "I'", CC('( encNatGam ` %s )' % i1, YXt("( D ` I' )")))
    POST1 = UP(DP, "I'", QI1)
    ue = upeq(w, ps, DP, "I'", w.s([w1['qv']], 'eqcomd', '( %s -> %s = %s )' % (ps, QUB(i1), QI1)), QUB(i1), QI1)
    assert Da == CLN('E', NCMI, POST0), (Da, POST0)
    de1 = clnneq(w, ps, 'E', ncls, NCMI, FAPP(NUF, i1), POST0)
    de2 = clneq(w, ps, 'E', FAPP(NUF, i1), ue, POST0, POST1)
    deq = w.s([de1, de2], 'eqtrd', '( %s -> %s = %s )' % (ps, Da, CLN('E', FAPP(NUF, i1), POST1)))
    t3, C3, D3, n3 = hrrw(w, ps, t2, Cn, Da, n1, deq=deq)
    # the bound
    nfn = w.s([L(ef), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NF))
    ngn = w.s([L(eg), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, NG))
    ENI = '( # ` ( encodeNat ` i ) )'
    eni = w.s([w.s([inn, w.inst('encnatcl')], 'syl', '( %s -> ( encodeNat ` i ) e. Word 2o )' % ps), w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, ENI))
    LSH = '( # ` %s )' % SHG(i1)
    lsh = w.s([w1['sh'], w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (ps, LSH))
    shl = w.s([w1['rw'], L(eg), w.inst('ccatlen')], 'syl2anc', '( %s -> %s = ( ( # ` ( (/) repeatS %s ) ) + %s ) )' % (ps, LSH, i1, NG))
    rpl = w.s([L(b0), i1n, w.inst('repswlen')], 'syl2anc', '( %s -> ( # ` ( (/) repeatS %s ) ) = %s )' % (ps, i1, i1))
    rpn = w.s([w1['rw'], w.inst('lencl')], 'syl', '( %s -> ( # ` ( (/) repeatS %s ) ) e. NN0 )' % (ps, i1))
    cb = Closure(w, ps, {'i': ('NN0', inn), 'R': ('NN0', L(rn))})
    for a, st in [(NF, nfn), (NG, ngn), (ENI, eni), (LSH, lsh), ('( # ` ( (/) repeatS %s ) )' % i1, rpn)]:
        cb.leaf(a, 'NN0', st)
    # |enc i| <_ n : bl i <_ n since i < 2 ^ n
    enbl = w.s([inn, w.inst('encnatlenbl')], 'syl', '( %s -> %s = ( bl ` i ) )' % (ps, ENI))
    two = w.s([w.s([], '2z', '2 e. ZZ'), w.inst('uzid')], 'ax-mp', '2 e. ( ZZ>= ` 2 )')
    np = w.s([w.s([two], 'a1i', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % ps), nfn, w.inst('bernneq3')], 'syl2anc', '( %s -> %s < ( 2 ^ %s ) )' % (ps, NF, NF))
    cb.atom('( 2 ^ %s )' % NF)
    ilt2 = linarith(w, ps, [ilt, L(rle), np], 'i < ( 2 ^ %s )' % NF, closure=cb)
    bll = w.s([inn, nfn, ilt2, w.inst('blle')], 'syl3anc', '( %s -> ( bl ` i ) <_ %s )' % (ps, NF))
    eni_le = w.s([enbl, bll], 'eqbrtrd', '( %s -> %s <_ %s )' % (ps, ENI, NF))
    cb.have('( bl ` i )', 'NN0', w.s([inn, w.inst('blcl')], 'syl', '( %s -> ( bl ` i ) e. NN0 )' % ps))
    zl = w.s([cb.mem('i', 'ZZ'), cb.mem('R', 'ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s -> ( i < R <-> ( i + 1 ) <_ R ) )' % ps)
    i1le = w.s([ilt, zl], 'mpbid', '( %s -> ( i + 1 ) <_ R )' % ps)
    lsh_le = linarith(w, ps, [shl, rpl, i1le, L(rle)], '%s <_ ( %s + %s )' % (LSH, NF, NG), closure=cb)
    nf_le = linarith(w, ps, [cb.ge0(NG)], '%s <_ ( %s + %s )' % (NF, NF, NG), closure=cb)
    MX = tsub_text(MXLL, m)
    mxl = ifmax_le(w, ps, LSH, NF, '( %s + %s )' % (NF, NG), cb.mem(LSH, 'RR'), cb.mem(NF, 'RR'), cb.mem('( %s + %s )' % (NF, NG), 'RR'), lsh_le, nf_le)
    cb.leaf(MX, 'NN0', w.s([nfn, lsh], 'ifcld', '( %s -> %s e. NN0 )' % (ps, MX)))
    le = linarith(w, ps, [eni_le, lsh_le, mxl], '%s <_ %s' % (n3, UPB), closure=cb)
    t4 = hrle(w, ps, L(phm), t3, C3, D3, n3, UPB, cb.mem(UPB, 'NN0'), le)
    PER = '( %s /\\ A. m e. ( %s ` i ) ( %s ` m ) = 1o /\\ %s )' % (YSTEP, NUF, CNGT, TRI(C3, D3, UPB))
    body = w.s([yst, ht, t4], '3jca', '( %s -> %s )' % (ps, PER))
    per = w.s([body], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ R ) %s )' % (ph, PER))
    # ---------------- the exit test at R
    pr = '( %s /\\ m e. ( %s ` R ) )' % (ph, NUF)
    Lr = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (pr, concl(w, ph, st)))
    rv = fv(w, ph, NUF, NUB, 'R', rn, rabV(w, ph, NUB('R')))
    mr = w.s([w.s([], 'simpr', '( %s -> m e. ( %s ` R ) )' % (pr, NUF)), Lr(rv)], 'eleqtrd', '( %s -> m e. %s )' % (pr, NUB('R')))
    VR = '( ( ( 2 ^ R ) x. G ) Ncmp F )'
    mmr, mcr = rab_elim(w, pr, NUB('R'), lambda h: '( TMcmp ` %s ) = %s' % (h, VR), 'm', mr)
    cr = Closure(w, pr, {'G': ('NN', Lr(gn)), 'F': ('NN0', Lr(fn)), 'R': ('NN0', Lr(rn))})
    XR = '( ( 2 ^ R ) x. G )'
    gtr = w.s([cr.mem(XR, 'NN0'), cr.mem('F', 'NN0'), w.inst('ncmpgt')], 'syl2anc', '( %s -> ( %s = 2o <-> F < %s ) )' % (pr, VR, XR))
    is2 = w.s([Lr(rlt), gtr], 'mpbird', '( %s -> %s = 2o )' % (pr, VR))
    X_of = lambda t: 'if ( ( TMcmp ` %s ) = 2o , (/) , 1o )' % t
    xex = ifex_closed(w, pr, '( TMcmp ` m ) = 2o', '(/)', '1o', w.s([], '0ex', '(/) e. _V'), w.s([], '1oex', '1o e. _V'))
    cvr = mval(w, pr, 'u', 'TMSt', X_of, 'm', mmr, xex)
    c2o = w.s([mcr, is2], 'eqtrd', '( %s -> ( TMcmp ` m ) = 2o )' % pr)
    it = w.s([c2o], 'iftrued', '( %s -> %s = (/) )' % (pr, X_of('m')))
    cz = w.s([cvr, it], 'eqtrd', '( %s -> ( %s ` m ) = (/) )' % (pr, CNGT))
    n1o = not1o(w, pr, cz, CNGT, 'm')
    ext = w.s([n1o], 'ralrimiva', '( %s -> A. m e. ( %s ` R ) -. ( %s ` m ) = 1o )' % (ph, NUF, CNGT))
    w.qed([typ, w.s([per, ext], 'jca', '( %s -> %s )' % (ph, C.split(' /\\ ', 1)[1][:-2] if False else cj((concl(w, ph, per), concl(w, ph, ext)))))], 'jca', '( %s -> %s )' % (ph, C))
    return w.run()


if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
