"""Sortie EF2: exists_good_height (ef2ghc: two squares cover; ef2gh)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef2lib import *
from c8_o import numst
import lin
import ef2_b
lin.FASTPATH = True

IT = '( T [,] ( T + 1 ) )'
ZU = ZS('F', 'U')
WW = '( %s u. %s )' % (ZS('F', 'T'), ZS('F', '( T + 1 )'))
S['ef2ghc'] = '( ( ( T e. RR /\\ U e. %s ) /\\ Q e. %s ) -> Q e. %s )' % (IT, ZU, WW)


def u_facts(w, A):
    """in context A (whose first conjunct chain gives T e. RR /\\ U e. IT): T, U reals and T <_ U <_ T + 1"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A, f))
    return s


def gen_ghc():
    w = W('ef2ghc', 'Two squares cover (Lean ` exists_grid_cover ` on squares): a zero of the ` 13 / 8 ` square about ` 2 + i U ` , ` T <_ U <_ T + 1 ` , lies in the square about ` 2 + i T ` or in the one about ` 2 + i ( T + 1 ) ` .')
    A0, _ = ante_of(S['ef2ghc'])
    Ps = '( Im ` Q ) <_ ( T + %s )' % R138
    outs = []
    for case in (0, 1):
        Ac = '( %s /\\ %s )' % (A0, Ps if case == 0 else '-. ' + Ps)
        s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ac, f))
        tr = s([], 'simplll', 'T e. RR')
        ui = s([], 'simpllr', 'U e. %s' % IT)
        qin = s([], 'simplr', 'Q e. %s' % ZU)
        t1 = s([tr, numst(w, Ac, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
        e2 = s([tr, t1, w.inst('elicc2')], 'syl2anc', '( U e. %s <-> ( U e. RR /\\ T <_ U /\\ U <_ ( T + 1 ) ) )' % IT)
        u3 = s([ui, e2], 'mpbid', '( U e. RR /\\ T <_ U /\\ U <_ ( T + 1 ) )')
        ur = s([u3, w.inst('simp1')], 'syl', 'U e. RR')
        hy = [s([u3, w.inst('simp2')], 'syl', 'T <_ U'), s([u3, w.inst('simp3')], 'syl', 'U <_ ( T + 1 )')]
        d = zs_unpack(w, Ac, 'F', 'U', ur, 'Q', qin)
        lv = dict(d['lv']); lv['T'] = tr; lv['U'] = ur
        iq = lv['( Im ` Q )']
        if case == 0:
            hy.append(s([], 'simpr', Ps))
            m = zs_mem(w, Ac, 'F', 'T', tr, 'Q', d['cc'], hy + d['hy'], lv, d['fz'])
            outs.append(w.s([s([m, w.inst('elun1')], 'syl', 'Q e. %s' % WW)], 'ex', '( %s -> ( %s -> Q e. %s ) )' % (A0, Ps, WW)))
        else:
            b = s([tr, numst(w, Ac, R138, 'RR')], 'readdcld', '( T + %s ) e. RR' % R138)
            lt = s([s([], 'simpr', '-. ' + Ps), s([b, iq], 'ltnled', '( ( T + %s ) < ( Im ` Q ) <-> -. %s )' % (R138, Ps))], 'mpbird', '( T + %s ) < ( Im ` Q )' % R138)
            hy.append(lt)
            m = zs_mem(w, Ac, 'F', '( T + 1 )', t1, 'Q', d['cc'], hy + d['hy'], lv, d['fz'])
            outs.append(w.s([s([m, w.inst('elun2')], 'syl', 'Q e. %s' % WW)], 'ex', '( %s -> ( -. %s -> Q e. %s ) )' % (A0, Ps, WW)))
    w.qed(outs, 'pm2.61d', S['ef2ghc'])
    return run8(w)


SU = '( V + ( _i x. U ) )'
XU = XA('U')
S['ef2ghs'] = ('( ( ( %s /\\ U e. RR ) /\\ ( V e. RR /\\ E e. RR+ /\\ A. p e. %s E <_ ( abs ` ( U - ( Im ` p ) ) ) ) ) -> '
               '( abs ` sum_ q e. %s ( ( F holord q ) / ( %s - q ) ) ) <_ ( ( ; ; 8 0 0 x. ( log ` %s ) ) / E ) )') % (DD(), ZU, ZU, SU, XU)


def gen_ghs():
    w = W('ef2ghs', 'The partial-fraction sum at ` V + i U ` over the square zeros about ` 2 + i U ` is at most ` 800 log ( A ( abs U + 2 ) ) / E ` when every zero ordinate is at distance ` >_ E ` from ` U ` (inside Lean ` exists_good_height ` ).')
    A0, _ = ante_of(S['ef2ghs'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    X1, X2 = top_and(A0)
    x1 = s([], 'simpl', X1); x2 = s([], 'simpr', X2)
    dd = s([x1, w.inst('simpl')], 'syl', DD()); ur = s([x1, w.inst('simpr')], 'syl', 'U e. RR')
    Y1, Y2, Y3 = top_and(X2)
    vr = s([x2, w.inst('simp1')], 'syl', Y1); erp = s([x2, w.inst('simp2')], 'syl', Y2); gap = s([x2, w.inst('simp3')], 'syl', Y3)
    zc = tsub(ante_of(S['ef2zs'])[1], {'T': 'U'})
    zs = s([x1, w.inst('ef2zs')], 'syl', zc)
    c1, c2, c3 = top_and(zc)
    fin = s([zs, w.inst('simp1')], 'syl', c1); alln = s([zs, w.inst('simp2')], 'syl', c2); mass = s([zs, w.inst('simp3')], 'syl', c3)
    su = s([s([vr], 'recnd', 'V e. CC'), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([ur], 'recnd', 'U e. CC')], 'mulcld', '( _i x. U ) e. CC')], 'addcld', '%s e. CC' % SU)
    Aq = '( %s /\\ q e. %s )' % (A0, ZU)
    sq = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    qin = sq([], 'simpr', 'q e. %s' % ZU)
    ad = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Aq, f))
    urq = ad(ur, 'U e. RR'); vrq = ad(vr, 'V e. RR'); erq = ad(erp, 'E e. RR+'); suq = ad(su, '%s e. CC' % SU)
    d = zs_unpack(w, Aq, 'F', 'U', urq, 'q', qin)
    qc = d['cc']
    nn = w.s([alln], 'r19.21bi', '( %s -> ( F holord q ) e. NN )' % Aq)
    M = '( F holord q )'
    mr = sq([nn], 'nnred', '%s e. RR' % M); m0 = sq([sq([nn], 'nnnn0d', '%s e. NN0' % M)], 'nn0ge0d', '0 <_ %s' % M)
    D = '( %s - q )' % SU
    dc = sq([suq, qc], 'subcld', '%s e. CC' % D)
    # E <_ abs ( U - Im q ) = abs ( Im D ) <_ abs D
    sub = w.s([w.s([w.s([w.s([], 'fveq2', '( p = q -> ( Im ` p ) = ( Im ` q ) )')], 'oveq2d', '( p = q -> ( U - ( Im ` p ) ) = ( U - ( Im ` q ) ) )')], 'fveq2d',
                     '( p = q -> ( abs ` ( U - ( Im ` p ) ) ) = ( abs ` ( U - ( Im ` q ) ) ) )')], 'breq2d',
              '( p = q -> ( E <_ ( abs ` ( U - ( Im ` p ) ) ) <-> E <_ ( abs ` ( U - ( Im ` q ) ) ) ) )')
    g1 = sq([sub, ad(gap, Y3), qin], 'rspcdva', 'E <_ ( abs ` ( U - ( Im ` q ) ) )')
    two = numst(w, Aq, '2', 'RR')
    imd = sq([suq, qc], 'imsubd', '( Im ` %s ) = ( ( Im ` %s ) - ( Im ` q ) )' % (D, SU))
    ims = sq([vrq, urq], 'crimd', '( Im ` %s ) = U' % SU)
    imd2 = sq([imd, sq([ims], 'oveq1d', '( ( Im ` %s ) - ( Im ` q ) ) = ( U - ( Im ` q ) )' % SU)], 'eqtrd', '( Im ` %s ) = ( U - ( Im ` q ) )' % D)
    abi = sq([imd2], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` ( U - ( Im ` q ) ) )' % D)
    g2 = sq([g1, abi], 'breqtrrd', 'E <_ ( abs ` ( Im ` %s ) )' % D)
    g3 = sq([dc, w.inst('absimle')], 'syl', '( abs ` ( Im ` %s ) ) <_ ( abs ` %s )' % (D, D))
    er = sq([erq], 'rpred', 'E e. RR')
    ad_ = sq([dc], 'abscld', '( abs ` %s ) e. RR' % D)
    aim = sq([sq([dc], 'imcld', '( Im ` %s ) e. RR' % D)], 'recnd', '( Im ` %s ) e. CC' % D)
    aimr = sq([aim], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % D)
    g4 = sq([er, aimr, ad_, g2, g3], 'letrd', 'E <_ ( abs ` %s )' % D)
    e0 = sq([numst(w, Aq, '0', 'RR'), er, ad_, sq([erq], 'rpgt0d', '0 < E'), g4], 'ltletrd', '0 < ( abs ` %s )' % D)
    adp = sq([ad_, e0], 'elrpd', '( abs ` %s ) e. RR+' % D)
    dn0 = sq([e0, sq([dc, w.inst('absgt0')], 'syl', '( %s =/= 0 <-> 0 < ( abs ` %s ) )' % (D, D))], 'mpbird', '%s =/= 0' % D)
    # abs ( M / D ) = M / abs D <_ M / E
    mc = sq([mr], 'recnd', '%s e. CC' % M)
    t1 = sq([mc, dc, dn0], 'absdivd', '( abs ` ( %s / %s ) ) = ( ( abs ` %s ) / ( abs ` %s ) )' % (M, D, M, D))
    t2 = sq([sq([mr, m0], 'absidd', '( abs ` %s ) = %s' % (M, M))], 'oveq1d', '( ( abs ` %s ) / ( abs ` %s ) ) = ( %s / ( abs ` %s ) )' % (M, D, M, D))
    t3 = sq([erq, adp, mr, m0, g4], 'lediv2ad', '( %s / ( abs ` %s ) ) <_ ( %s / E )' % (M, D, M))
    tl = sq([sq([t1, t2], 'eqtrd', '( abs ` ( %s / %s ) ) = ( %s / ( abs ` %s ) )' % (M, D, M, D)), t3], 'eqbrtrd', '( abs ` ( %s / %s ) ) <_ ( %s / E )' % (M, D, M))
    tc = sq([mc, dc, dn0], 'divcld', '( %s / %s ) e. CC' % (M, D))
    SUMA = 'sum_ q e. %s ( abs ` ( %s / %s ) )' % (ZU, M, D)
    SUMB = 'sum_ q e. %s ( %s / E )' % (ZU, M)
    SUMM = MASS(ZU, 'F')
    f1 = s([fin, tc], 'fsumabs', '( abs ` sum_ q e. %s ( %s / %s ) ) <_ %s' % (ZU, M, D, SUMA))
    f2 = s([fin, sq([tc], 'abscld', '( abs ` ( %s / %s ) ) e. RR' % (M, D)), sq([mr, er, sq([erq], 'rpne0d', 'E =/= 0')], 'redivcld', '( %s / E ) e. RR' % M), tl], 'fsumle', '%s <_ %s' % (SUMA, SUMB))
    f3 = s([fin, s([erp], 'rpcnd', 'E e. CC'), mc, s([erp], 'rpne0d', 'E =/= 0')], 'fsumdivc', '( %s / E ) = %s' % (SUMM, SUMB))
    X8 = '( ; ; 8 0 0 x. ( log ` %s ) )' % XU
    mre = s([fin, mr], 'fsumrecl', '%s e. RR' % SUMM)
    lx = zslogx(w, A0, dd, ur)
    f4 = s([mre, lx, erp, mass], 'lediv1dd', '( %s / E ) <_ ( %s / E )' % (SUMM, X8))
    f5 = s([f3, f4], 'eqbrtrrd', '%s <_ ( %s / E )' % (SUMB, X8))
    fa = le_tr(w, A0, f1, '( abs ` sum_ q e. %s ( %s / %s ) )' % (ZU, M, D), SUMA, f2, SUMB)
    le_tr(w, A0, fa, '( abs ` sum_ q e. %s ( %s / %s ) )' % (ZU, M, D), SUMB, f5, '( %s / E )' % X8, name='qed')
    return run8(w)


def zslogx(w, A0, dd, ur):
    """( A0 -> ( ; ; 8 0 0 x. ( log ` XA(U) ) ) e. RR ) from DD and U e. RR"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    xp = s([s([dd, ur], 'jca', '( %s /\\ U e. RR )' % DD()), w.inst('ef2x2')], 'syl', '2 <_ %s' % XU)
    hol, ar, a1, allt, nz = dd_parts(w, A0, dd)
    xr = s([ar, s([s([s([ur], 'recnd', 'U e. CC')], 'abscld', '( abs ` U ) e. RR'), numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` U ) + 2 ) e. RR')], 'remulcld', '%s e. RR' % XU)
    xrp = s([xr, lin8(w, A0, [xp], '0 < %s' % XU, {XU: xr})], 'elrpd', '%s e. RR+' % XU)
    return s([numst(w, A0, '; ; 8 0 0', 'RR'), s([xrp], 'relogcld', '( log ` %s ) e. RR' % XU)], 'remulcld', '( ; ; 8 0 0 x. ( log ` %s ) ) e. RR' % XU)


L_ = LT4
WI = '( Im " %s )' % WW
GAM = '( %s u. G )' % WI
DEN = '( 2 x. ( ( # ` %s ) + 1 ) )' % GAM
DL = '( 1 / %s )' % DEN
IV = '( ( 1 / 2 ) [,] 3 )'
A4 = '( A x. ( T + 4 ) )'


def gh_facts(w, C, a0):
    """facts of the A0 part of ef2gh in context C, a0 : ( C -> A0 )"""
    A0 = ante_of(S['ef2gh'])[0]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (C, f))
    X1, X2 = top_and(A0)
    x1 = s([a0, w.inst('simpl')], 'syl', X1); x2 = s([a0, w.inst('simpr')], 'syl', X2)
    dd = s([x1, w.inst('simpl')], 'syl', DD()); tt = s([x1, w.inst('simpr')], 'syl', '( T e. RR /\\ 2 <_ T )')
    tr = s([tt, w.inst('simpl')], 'syl', 'T e. RR'); t2 = s([tt, w.inst('simpr')], 'syl', '2 <_ T')
    G1, G2, G3 = top_and(X2)
    gfin = s([x2, w.inst('simp1')], 'syl', G1); gss = s([x2, w.inst('simp2')], 'syl', G2); gcard = s([x2, w.inst('simp3')], 'syl', G3)
    hol, ar, a1, allt, nz = dd_parts(w, C, dd)
    t1 = s([tr, numst(w, C, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    f = {'dd': dd, 'tr': tr, 't2': t2, 'gss': gss, 'ar': ar, 'a1': a1, 'hol': hol, 't1': t1}
    fins, cards, logs, sqs = [], [], [], []
    for t, st in (('T', tr), ('( T + 1 )', t1)):
        dt = s([dd, st], 'jca', '( %s /\\ %s e. RR )' % (DD(), t))
        zc = tsub(ante_of(S['ef2zs'])[1], {'T': t})
        fins.append(s([s([dt, w.inst('ef2zs')], 'syl', zc), w.inst('simp1')], 'syl', top_and(zc)[0]))
        cards.append(s([dt, w.inst('ef2card')], 'syl', tsub(ante_of(S['ef2card'])[1], {'T': t})))
        d = sq_data(w, C, t, st)
        sqs.append(s([s([w.s([], 'ssrab2', '%s C_ %s' % (ZS('F', t), SQ(CT(t), R138)))], 'a1i', '%s C_ %s' % (ZS('F', t), SQ(CT(t), R138))),
                      s([d['a'], d['b'], w.inst('crectss')], 'syl2anc', '%s C_ CC' % SQ(CT(t), R138))], 'sstrd', '%s C_ CC' % ZS('F', t)))
    Z0, Z1 = ZS('F', 'T'), ZS('F', '( T + 1 )')
    wfin = s([fins[0], fins[1], w.inst('unfi')], 'syl2anc', '%s e. Fin' % WW)
    wcc = s([sqs[0], sqs[1]], 'unssd', '%s C_ CC' % WW)
    imf = w.s([], 'imf', 'Im : CC --> RR')
    fun = s([w.s([imf, w.inst('ffun')], 'ax-mp', 'Fun Im')], 'a1i', 'Fun Im')
    fnc = s([w.s([imf, w.inst('ffn')], 'ax-mp', 'Im Fn CC')], 'a1i', 'Im Fn CC')
    dm = s([w.s([imf, w.inst('fdm')], 'ax-mp', 'dom Im = CC')], 'a1i', 'dom Im = CC')
    iwfin = s([fun, wfin, w.inst('imafi')], 'syl2anc', '%s e. Fin' % WI)
    iwrr = s([s([w.s([], 'imassrn', '%s C_ ran Im' % WI)], 'a1i', '%s C_ ran Im' % WI), s([w.s([imf, w.inst('frn')], 'ax-mp', 'ran Im C_ RR')], 'a1i', 'ran Im C_ RR')], 'sstrd', '%s C_ RR' % WI)
    gfin2 = s([iwfin, gfin, w.inst('unfi')], 'syl2anc', '%s e. Fin' % GAM)
    grr = s([iwrr, gss], 'unssd', '%s C_ RR' % GAM)
    onto = s([fun, s([wcc, dm], 'sseqtrrd', '%s C_ dom Im' % WW), w.inst('fores')], 'syl2anc', '( Im |` %s ) : %s -onto-> %s' % (WW, WW, WI))
    hdom = s([s([wfin, onto, w.inst('fodomfi')], 'syl2anc', '%s ~<_ %s' % (WI, WW)), w.inst('hashdomi')], 'syl', '( # ` %s ) <_ ( # ` %s )' % (WI, WW))
    hun = s([fins[0], fins[1], w.inst('hashun2')], 'syl2anc', '( # ` %s ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (WW, Z0, Z1))
    hg = s([iwfin, gfin, w.inst('hashun2')], 'syl2anc', '( # ` %s ) <_ ( ( # ` %s ) + ( # ` G ) )' % (GAM, WI))
    hr = lambda X, fs: s([s([fs, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % X)], 'nn0red', '( # ` %s ) e. RR' % X)
    lv = {'( # ` %s )' % GAM: hr(GAM, gfin2), '( # ` %s )' % WI: hr(WI, iwfin), '( # ` %s )' % WW: hr(WW, wfin),
          '( # ` %s )' % Z0: hr(Z0, fins[0]), '( # ` %s )' % Z1: hr(Z1, fins[1]), '( # ` G )': hr('G', gfin), 'T': tr, 'A': ar}
    # A ( T + 4 ) facts, L >_ 1
    t4 = s([tr, numst(w, C, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')
    pass
    a4r = s([ar, t4], 'remulcld', '%s e. RR' % A4)
    a4g = s([numst(w, C, '1', 'RR'), ar, t4, lin8(w, C, [t2], '0 <_ ( T + 4 )', {'T': tr}), a1], 'lemul1ad', '( 1 x. ( T + 4 ) ) <_ %s' % A4)
    lv[A4] = a4r
    six = lin8(w, C, [a4g, t2], '6 <_ %s' % A4, dict(lv))
    a4p = s([a4r, lin8(w, C, [six], '0 < %s' % A4, {A4: a4r})], 'elrpd', '%s e. RR+' % A4)
    ere = s([w.s([], 'epr', '_e e. RR+')], 'a1i', '_e e. RR+')
    e3 = s([w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3')], 'a1i', '_e < 3')
    er_ = s([ere], 'rpred', '_e e. RR')
    ele = lin8(w, C, [e3, six], '_e <_ %s' % A4, {'_e': er_, A4: a4r})
    lg1 = s([s([w.s([], 'loge', '( log ` _e ) = 1')], 'a1i', '( log ` _e ) = 1'), s([ele, s([ere, a4p], 'logled', '( _e <_ %s <-> ( log ` _e ) <_ %s )' % (A4, L_))], 'mpbid', '( log ` _e ) <_ %s' % L_)],
            'eqbrtrrd', '1 <_ %s' % L_)
    lr = s([a4p], 'relogcld', '%s e. RR' % L_)
    lv[L_] = lr
    # log X(t) <_ L for t = T, T + 1
    at = s([tr, lin8(w, C, [t2], '0 <_ T', {'T': tr})], 'absidd', '( abs ` T ) = T')
    at1 = s([t1, lin8(w, C, [t2], '0 <_ ( T + 1 )', {'T': tr})], 'absidd', '( abs ` ( T + 1 ) ) = ( T + 1 )')
    hy = [hdom, hun, hg, gcard, lg1]
    for t, st, ab, bump in (('T', tr, at, '2'), ('( T + 1 )', t1, at1, '3')):
        X = XA(t)
        inner = '( ( abs ` %s ) + 2 )' % t
        ir = s([s([s([st], 'recnd', '%s e. CC' % t)], 'abscld', '( abs ` %s ) e. RR' % t), numst(w, C, '2', 'RR')], 'readdcld', '%s e. RR' % inner)
        a0le = s([numst(w, C, '0', 'RR'), numst(w, C, '1', 'RR'), ar, lin8(w, C, [], '0 <_ 1', {}), a1], 'letrd', '0 <_ A')
        le_i = lin8(w, C, [ab], '%s <_ ( T + 4 )' % inner, {'T': tr, '( abs ` %s )' % t: s([s([st], 'recnd', '%s e. CC' % t)], 'abscld', '( abs ` %s ) e. RR' % t)})
        xle = s([ir, t4, ar, a0le, le_i], 'lemul2ad', '%s <_ %s' % (X, A4))
        xr = s([ar, ir], 'remulcld', '%s e. RR' % X)
        x2 = s([s([dd, st], 'jca', '( %s /\\ %s e. RR )' % (DD(), t)), w.inst('ef2x2')], 'syl', '2 <_ %s' % X)
        xp = s([xr, lin8(w, C, [x2], '0 < %s' % X, {X: xr})], 'elrpd', '%s e. RR+' % X)
        lx = s([xle, s([xp, a4p], 'logled', '( %s <_ %s <-> ( log ` %s ) <_ %s )' % (X, A4, X, L_))], 'mpbid', '( log ` %s ) <_ %s' % (X, L_))
        lv['( log ` %s )' % X] = s([xp], 'relogcld', '( log ` %s ) e. RR' % X)
        hy.append(lx)
    hy += cards
    ncard = lin8(w, C, hy, '( # ` %s ) <_ ( ; ; ; 1 6 1 6 x. %s )' % (GAM, L_), lv)
    denr = s([numst(w, C, '2', 'RR'), s([lv['( # ` %s )' % GAM], numst(w, C, '1', 'RR')], 'readdcld', '( ( # ` %s ) + 1 ) e. RR' % GAM)], 'remulcld', '%s e. RR' % DEN)
    hge = s([s([gfin2, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % GAM)], 'nn0ge0d', '0 <_ ( # ` %s )' % GAM)
    denp = s([denr, lin8(w, C, [hge], '0 < %s' % DEN, {'( # ` %s )' % GAM: lv['( # ` %s )' % GAM]})], 'elrpd', '%s e. RR+' % DEN)
    lv2 = {'( # ` %s )' % GAM: lv['( # ` %s )' % GAM], L_: lr}
    den1 = lin8(w, C, [ncard, lg1], '%s <_ ( ; ; ; 3 2 3 4 x. %s )' % (DEN, L_), lv2)
    den2 = lin8(w, C, [ncard, lg1], '%s <_ ( %s x. %s )' % (DEN, GAP, L_), lv2)
    f.update({'gfin2': gfin2, 'grr': grr, 'wcc': wcc, 'fnc': fnc, 'lg1': lg1, 'lr': lr, 'a4p': a4p, 'a4r': a4r, 'denp': denp, 'den1': den1,
              'den2': den2, 't4': t4})
    return f


def gen_gh():
    w = W('ef2gh', 'Lean ` exists_good_height ` on squares: for ` T >_ 2 ` and a finite set ` G ` of at most ` 16 log ( A ( T + 4 ) ) ` reals there is ` u e. [ T , T + 1 ] ` at distance ` >_ 1 / ( 4000 log ( A ( T + 4 ) ) ) ` from ` G ` with ` F ( v + i u ) =/= 0 ` and ` abs ( F-prime / F ) ( v + i u ) <_ 21000000 log ^ 2 ( A ( T + 4 ) ) ` for ` v e. [ 1 / 2 , 3 ] ` (Lean: ` 2000 ` , ` 10 ^ 6 ` ).')
    A0, GC = ante_of(S['ef2gh'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    f0 = gh_facts(w, A0, s([], 'id', A0))
    GP = tsub(stmt('gappt'), {'G': GAM, 't': 'u', 'g': 'y'})
    ga, gc = ante_of(GP)
    ex = s([s([s([f0['gfin2'], f0['grr']], 'jca', top_and(ga)[0]), f0['tr']], 'jca', ga), w.inst('gappt')], 'syl', gc)
    PHI = GC[len('E. u e. %s ' % IT):]
    GAPY = gc[len('E. u e. %s ' % IT):]
    Au = '( ( %s /\\ u e. %s ) /\\ %s )' % (A0, IT, GAPY)
    su = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Au, f))
    f = gh_facts(w, Au, su([], 'simpll', A0))
    ui = su([], 'simplr', 'u e. %s' % IT)
    gapall = su([], 'simpr', GAPY)
    e2 = su([f['tr'], f['t1'], w.inst('elicc2')], 'syl2anc', '( u e. %s <-> ( u e. RR /\\ T <_ u /\\ u <_ ( T + 1 ) ) )' % IT)
    u3 = su([ui, e2], 'mpbid', '( u e. RR /\\ T <_ u /\\ u <_ ( T + 1 ) )')
    ur = su([u3, w.inst('simp1')], 'syl', 'u e. RR')
    tu = su([u3, w.inst('simp2')], 'syl', 'T <_ u'); ut = su([u3, w.inst('simp3')], 'syl', 'u <_ ( T + 1 )')
    dlp = su([f['denp']], 'rpreccld', '%s e. RR+' % DL)
    dlr = su([dlp], 'rpred', '%s e. RR' % DL)
    def gapat(Ctx, y_expr, mem, gst=None):
        sub = w.s([w.s([w.s([], 'oveq2', '( y = %s -> ( u - y ) = ( u - %s ) )' % (y_expr, y_expr))], 'fveq2d', '( y = %s -> ( abs ` ( u - y ) ) = ( abs ` ( u - %s ) ) )' % (y_expr, y_expr))],
                  'breq2d', '( y = %s -> ( %s <_ ( abs ` ( u - y ) ) <-> %s <_ ( abs ` ( u - %s ) ) ) )' % (y_expr, DL, DL, y_expr))
        return w.s([sub, w.s([gst or gapall], 'adantr', '( %s -> %s )' % (Ctx, GAPY)), mem], 'rspcdva', '( %s -> %s <_ ( abs ` ( u - %s ) ) )' % (Ctx, DL, y_expr))
    # conjunct 1
    Ag = '( %s /\\ g e. G )' % Au
    sg = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ag, f))
    gg = sg([sg([], 'simpr', 'g e. G'), w.inst('elun2')], 'syl', 'g e. %s' % GAM)
    g1 = gapat(Ag, 'g', gg)
    L4p = su([numst(w, Au, GAP, 'RR+'), su([f['lr'], su([numst(w, Au, '0', 'RR'), numst(w, Au, '1', 'RR'), f['lr'], lin8(w, Au, [], '0 < 1', {}), f['lg1']], 'ltletrd', '0 < %s' % L_)], 'elrpd', '%s e. RR+' % L_)],
              'rpmulcld', '( %s x. %s ) e. RR+' % (GAP, L_))
    q1 = su([f['denp'], L4p, numst(w, Au, '1', 'RR'), lin8(w, Au, [], '0 <_ 1', {}), f['den2']], 'lediv2ad', '( 1 / ( %s x. %s ) ) <_ %s' % (GAP, L_, DL))
    grr = sg([w.s([f['gss']], 'adantr', '( %s -> G C_ RR )' % Ag), sg([], 'simpr', 'g e. G')], 'sseldd', 'g e. RR')
    ugr = sg([sg([w.s([ur], 'adantr', '( %s -> u e. RR )' % Ag), grr], 'resubcld', '( u - g ) e. RR')], 'recnd', '( u - g ) e. CC')
    c1 = sg([sg([w.s([L4p], 'adantr', '( %s -> ( %s x. %s ) e. RR+ )' % (Ag, GAP, L_))], 'rpreccld', '( 1 / ( %s x. %s ) ) e. RR+' % (GAP, L_))], 'rpred', '( 1 / ( %s x. %s ) ) e. RR' % (GAP, L_))
    c1 = sg([c1, w.s([dlr], 'adantr', '( %s -> %s e. RR )' % (Ag, DL)), sg([ugr], 'abscld', '( abs ` ( u - g ) ) e. RR'), w.s([q1], 'adantr', '( %s -> ( 1 / ( %s x. %s ) ) <_ %s )' % (Ag, GAP, L_, DL)), g1],
            'letrd', '( 1 / ( %s x. %s ) ) <_ ( abs ` ( u - g ) )' % (GAP, L_))
    conj1 = w.s([c1], 'ralrimiva', '( %s -> A. g e. G ( 1 / ( %s x. %s ) ) <_ ( abs ` ( u - g ) ) )' % (Au, GAP, L_))
    # conjunct 2
    Av = '( %s /\\ v e. %s )' % (Au, IV)
    sv = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Av, f_))
    av = lambda st, f_: w.s([st], 'adantr', '( %s -> %s )' % (Av, f_))
    vi = sv([], 'simpr', 'v e. %s' % IV)
    h2 = numst(w, Av, '( 1 / 2 )', 'RR'); th = numst(w, Av, '3', 'RR')
    v3 = sv([vi, sv([h2, th, w.inst('elicc2')], 'syl2anc', '( v e. %s <-> ( v e. RR /\\ ( 1 / 2 ) <_ v /\\ v <_ 3 ) )' % IV)], 'mpbid', '( v e. RR /\\ ( 1 / 2 ) <_ v /\\ v <_ 3 )')
    vr = sv([v3, w.inst('simp1')], 'syl', 'v e. RR'); v1 = sv([v3, w.inst('simp2')], 'syl', '( 1 / 2 ) <_ v'); v2 = sv([v3, w.inst('simp3')], 'syl', 'v <_ 3')
    urv = av(ur, 'u e. RR'); tuv = av(tu, 'T <_ u'); trv = av(f['tr'], 'T e. RR'); t2v = av(f['t2'], '2 <_ T')
    iu = sv([sv([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), sv([urv], 'recnd', 'u e. CC')], 'mulcld', '( _i x. u ) e. CC')
    scc = sv([sv([vr], 'recnd', 'v e. CC'), iu], 'addcld', '%s e. CC' % SV)
    res = sv([vr, urv], 'crred', '( Re ` %s ) = v' % SV); ims = sv([vr, urv], 'crimd', '( Im ` %s ) = u' % SV)
    dd = av(f['dd'], DD()); hol = av(f['hol'], HOLF('F', HP0))
    ZUu = ZS('F', 'u')
    # every zero of the square about 2 + i u has its ordinate in GAM
    Ap = '( %s /\\ p e. %s )' % (Av, ZUu)
    sp = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Ap, f_))
    ap = lambda st, f_: w.s([st], 'adantr', '( %s -> %s )' % (Ap, f_))
    GH = tsub(S['ef2ghc'], {'U': 'u', 'Q': 'p'})
    gha, ghc_ = ante_of(GH)
    pw = sp([sp([sp([ap(trv, 'T e. RR'), ap(av(ui, 'u e. %s' % IT), 'u e. %s' % IT)], 'jca', '( T e. RR /\\ u e. %s )' % IT), sp([], 'simpr', 'p e. %s' % ZUu)], 'jca', gha),
             w.inst('ef2ghc')], 'syl', ghc_)
    pim = sp([ap(av(f['fnc'], 'Im Fn CC'), 'Im Fn CC'), ap(av(f['wcc'], '%s C_ CC' % WW), '%s C_ CC' % WW), pw, w.inst('fnfvima')], 'syl3anc', '( Im ` p ) e. %s' % WI)
    pg = sp([pim, w.inst('elun1')], 'syl', '( Im ` p ) e. %s' % GAM)
    gp = gapat(Ap, '( Im ` p )', pg, av(gapall, GAPY))
    GZ = 'A. p e. %s %s <_ ( abs ` ( u - ( Im ` p ) ) )' % (ZUu, DL)
    gapz = w.s([gp], 'ralrimiva', '( %s -> %s )' % (Av, GZ))
    dlv = av(dlp, '%s e. RR+' % DL)
    # F ( v + i u ) =/= 0
    Az = '( %s /\\ ( F ` %s ) = 0 )' % (Av, SV)
    sz = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Az, f_))
    az = lambda st, f_: w.s([st], 'adantr', '( %s -> %s )' % (Az, f_))
    lvz = {'v': az(vr, 'v e. RR'), 'u': az(urv, 'u e. RR')}
    sin = zs_mem(w, Az, 'F', 'u', lvz['u'], SV, az(scc, '%s e. CC' % SV), [az(res, '( Re ` %s ) = v' % SV), az(ims, '( Im ` %s ) = u' % SV), az(v1, '( 1 / 2 ) <_ v'), az(v2, 'v <_ 3')],
                 lvz, sz([], 'simpr', '( F ` %s ) = 0' % SV))
    subp = w.s([w.s([w.s([w.s([], 'fveq2', '( p = %s -> ( Im ` p ) = ( Im ` %s ) )' % (SV, SV))], 'oveq2d', '( p = %s -> ( u - ( Im ` p ) ) = ( u - ( Im ` %s ) ) )' % (SV, SV))],
                      'fveq2d', '( p = %s -> ( abs ` ( u - ( Im ` p ) ) ) = ( abs ` ( u - ( Im ` %s ) ) ) )' % (SV, SV))], 'breq2d',
               '( p = %s -> ( %s <_ ( abs ` ( u - ( Im ` p ) ) ) <-> %s <_ ( abs ` ( u - ( Im ` %s ) ) ) ) )' % (SV, DL, DL, SV))
    gz = sz([subp, az(gapz, GZ), sin], 'rspcdva', '%s <_ ( abs ` ( u - ( Im ` %s ) ) )' % (DL, SV))
    e0 = sz([sz([sz([az(ims, '( Im ` %s ) = u' % SV)], 'oveq2d', '( u - ( Im ` %s ) ) = ( u - u )' % SV), sz([sz([lvz['u']], 'recnd', 'u e. CC')], 'subidd', '( u - u ) = 0')], 'eqtrd',
                 '( u - ( Im ` %s ) ) = 0' % SV)], 'fveq2d', '( abs ` ( u - ( Im ` %s ) ) ) = ( abs ` 0 )' % SV)
    e1 = sz([e0, sz([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( abs ` 0 ) = 0')], 'eqtrd', '( abs ` ( u - ( Im ` %s ) ) ) = 0' % SV)
    dz = sz([gz, e1], 'breqtrd', '%s <_ 0' % DL)
    dlz = az(av(dlr, '%s e. RR' % DL), '%s e. RR' % DL)
    ndz = sz([sz([az(dlv, '%s e. RR+' % DL)], 'rpgt0d', '0 < %s' % DL), sz([numst(w, Az, '0', 'RR'), dlz], 'ltnled', '( 0 < %s <-> -. %s <_ 0 )' % (DL, DL))], 'mpbid', '-. %s <_ 0' % DL)
    fne = sv([sv([dz, ndz], 'pm2.65da', '-. ( F ` %s ) = 0' % SV)], 'neqned', '( F ` %s ) =/= 0' % SV)
    # the Landau expansion at 2 + i u
    pn = sv([sv([vr], 'recnd', 'v e. CC'), numst(w, Av, '2', 'CC'), iu, w.inst('pnpcan2')], 'syl3anc', '( %s - %s ) = ( v - 2 )' % (SV, CT('u')))
    tw = numst(w, Av, '2', 'RR'); th2 = numst(w, Av, '( 3 / 2 )', 'RR')
    ad2 = sv([sv([vr, tw, th2], 'absdifled', '( ( abs ` ( v - 2 ) ) <_ ( 3 / 2 ) <-> ( ( 2 - ( 3 / 2 ) ) <_ v /\\ v <_ ( 2 + ( 3 / 2 ) ) ) )'),
              sv([lin8(w, Av, [v1], '( 2 - ( 3 / 2 ) ) <_ v', {'v': vr}), lin8(w, Av, [v2], 'v <_ ( 2 + ( 3 / 2 ) )', {'v': vr})], 'jca', '( ( 2 - ( 3 / 2 ) ) <_ v /\\ v <_ ( 2 + ( 3 / 2 ) ) )')],
             'mpbird', '( abs ` ( v - 2 ) ) <_ ( 3 / 2 )')
    ad3 = sv([sv([pn], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( v - 2 ) )' % (SV, CT('u'))), ad2], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( 3 / 2 )' % (SV, CT('u')))
    ddu = sv([dd, urv], 'jca', '( %s /\\ u e. RR )' % DD())
    LN = tsub(S['ef2lnd'], {'T': 'u', 'S': SV})
    lna, lnc = ante_of(LN)
    lnd = sv([sv([ddu, sv([scc, ad3, fne], '3jca', top_and(lna)[1])], 'jca', lna), w.inst('ef2lnd')], 'syl', lnc)
    GS = tsub(S['ef2ghs'], {'U': 'u', 'V': 'v', 'E': DL})
    gsa, gsc = ante_of(GS)
    ghs = sv([sv([ddu, sv([vr, dlv, gapz], '3jca', top_and(gsa)[1])], 'jca', gsa), w.inst('ef2ghs')], 'syl', gsc)
    # the complex numbers
    hpv = sv([sv([numst(w, Av, '0', 'RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (SV, HP0, SV, SV)),
              sv([scc, sv([lin8(w, Av, [v1], '0 < v', {'v': vr}), res], 'breqtrrd', '0 < ( Re ` %s )' % SV)], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (SV, SV))], 'mpbird', '%s e. %s' % (SV, HP0))
    fsc = fcc(w, Av, hol, 'F', HP0, SV, hpv)
    dfc = sv([sv([hol, w.inst('holf')], 'syl', '( CC _D F ) : %s --> CC' % HP0), hpv], 'ffvelcdmd', '( ( CC _D F ) ` %s ) e. CC' % SV)
    Q = '( ( ( CC _D F ) ` %s ) / ( F ` %s ) )' % (SV, SV)
    qc = sv([dfc, fsc, fne], 'divcld', '%s e. CC' % Q)
    zc = tsub(ante_of(S['ef2zs'])[1], {'T': 'u'})
    zs = sv([ddu, w.inst('ef2zs')], 'syl', zc)
    zfin = sv([zs, w.inst('simp1')], 'syl', top_and(zc)[0]); zall = sv([zs, w.inst('simp2')], 'syl', top_and(zc)[1])
    Aq = '( %s /\\ q e. %s )' % (Av, ZUu)
    sq_ = lambda h, r, f_: w.s(h, r, '( %s -> %s )' % (Aq, f_))
    aq = lambda st, f_: w.s([st], 'adantr', '( %s -> %s )' % (Aq, f_))
    d = zs_unpack(w, Aq, 'F', 'u', aq(urv, 'u e. RR'), 'q', sq_([], 'simpr', 'q e. %s' % ZUu))
    ne1 = sq_([aq(fne, '( F ` %s ) =/= 0' % SV), d['fz']], 'neeqtrrd', '( F ` %s ) =/= ( F ` q )' % SV)
    ne2 = sq_([sq_([w.s([], 'fveq2', '( %s = q -> ( F ` %s ) = ( F ` q ) )' % (SV, SV))], 'a1i', '( %s = q -> ( F ` %s ) = ( F ` q ) )' % (SV, SV))], 'necon3d',
              '( ( F ` %s ) =/= ( F ` q ) -> %s =/= q )' % (SV, SV))
    sqn = sq_([ne1, ne2], 'mpd', '%s =/= q' % SV)
    dn = sq_([aq(scc, '%s e. CC' % SV), d['cc'], sqn], 'subne0d', '( %s - q ) =/= 0' % SV)
    mc = sq_([w.s([zall], 'r19.21bi', '( %s -> ( F holord q ) e. NN )' % Aq)], 'nncnd', '( F holord q ) e. CC')
    tc = sq_([mc, sq_([aq(scc, '%s e. CC' % SV), d['cc']], 'subcld', '( %s - q ) e. CC' % SV), dn], 'divcld', '( ( F holord q ) / ( %s - q ) ) e. CC' % SV)
    P = 'sum_ q e. %s ( ( F holord q ) / ( %s - q ) )' % (ZUu, SV)
    pc = sv([zfin, tc], 'fsumcl', '%s e. CC' % P)
    tri = sv([qc, pc], 'abs2difd', '( ( abs ` %s ) - ( abs ` %s ) ) <_ ( abs ` ( %s - %s ) )' % (Q, P, Q, P))
    # numbers
    XU_ = XA('u')
    Lu = '( log ` %s )' % XU_
    au = sv([urv, lin8(w, Av, [tuv, t2v], '0 <_ u', {'u': urv, 'T': trv})], 'absidd', '( abs ` u ) = u')
    ar = av(f['ar'], 'A e. RR'); a1 = av(f['a1'], '1 <_ A'); t4 = av(f['t4'], '( T + 4 ) e. RR')
    inner = '( ( abs ` u ) + 2 )'
    aur = sv([sv([urv], 'recnd', 'u e. CC')], 'abscld', '( abs ` u ) e. RR')
    ir = sv([aur, numst(w, Av, '2', 'RR')], 'readdcld', '%s e. RR' % inner)
    a0le = sv([numst(w, Av, '0', 'RR'), numst(w, Av, '1', 'RR'), ar, lin8(w, Av, [], '0 <_ 1', {}), a1], 'letrd', '0 <_ A')
    xle = sv([ir, t4, ar, a0le, lin8(w, Av, [au, av(ut, 'u <_ ( T + 1 )')], '%s <_ ( T + 4 )' % inner, {'u': urv, 'T': trv, '( abs ` u )': aur})], 'lemul2ad', '%s <_ %s' % (XU_, A4))
    xr = sv([ar, ir], 'remulcld', '%s e. RR' % XU_)
    x2 = sv([ddu, w.inst('ef2x2')], 'syl', '2 <_ %s' % XU_)
    xp = sv([xr, lin8(w, Av, [x2], '0 < %s' % XU_, {XU_: xr})], 'elrpd', '%s e. RR+' % XU_)
    lul = sv([xle, sv([xp, av(f['a4p'], '%s e. RR+' % A4)], 'logled', '( %s <_ %s <-> %s <_ %s )' % (XU_, A4, Lu, L_))], 'mpbid', '%s <_ %s' % (Lu, L_))
    lur = sv([xp], 'relogcld', '%s e. RR' % Lu)
    lu0 = sv([xr, lin8(w, Av, [x2], '1 <_ %s' % XU_, {XU_: xr})], 'logge0d', '0 <_ %s' % Lu)
    lr = av(f['lr'], '%s e. RR' % L_); lg1 = av(f['lg1'], '1 <_ %s' % L_)
    denp = av(f['denp'], '%s e. RR+' % DEN); den1 = av(f['den1'], '%s <_ ( ; ; ; 3 2 3 4 x. %s )' % (DEN, L_))
    X8 = '( ; ; 8 0 0 x. %s )' % Lu
    x8r = sv([numst(w, Av, '; ; 8 0 0', 'RR'), lur], 'remulcld', '%s e. RR' % X8)
    q1 = sv([sv([x8r], 'recnd', '%s e. CC' % X8), sv([dlv], 'rpcnd', '%s e. CC' % DL), sv([dlv], 'rpne0d', '%s =/= 0' % DL)], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (X8, DL, X8, DL))
    q2 = sv([sv([sv([denp], 'rpcnd', '%s e. CC' % DEN), sv([denp], 'rpne0d', '%s =/= 0' % DEN)], 'recrecd', '( 1 / %s ) = %s' % (DL, DEN))], 'oveq2d', '( %s x. ( 1 / %s ) ) = ( %s x. %s )' % (X8, DL, X8, DEN))
    q3 = sv([q1, q2], 'eqtrd', '( %s / %s ) = ( %s x. %s )' % (X8, DL, X8, DEN))
    L8 = '( ; ; 8 0 0 x. %s )' % L_
    L32 = '( ; ; ; 3 2 3 4 x. %s )' % L_
    pr = sv([x8r, sv([numst(w, Av, '; ; 8 0 0', 'RR'), lr], 'remulcld', '%s e. RR' % L8), sv([denp], 'rpred', '%s e. RR' % DEN), sv([numst(w, Av, '; ; ; 3 2 3 4', 'RR'), lr], 'remulcld', '%s e. RR' % L32),
             lin8(w, Av, [lu0], '0 <_ %s' % X8, {Lu: lur}), sv([denp], 'rpge0d', '0 <_ %s' % DEN), lin8(w, Av, [lul], '%s <_ %s' % (X8, L8), {Lu: lur, L_: lr}), den1],
            'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (X8, DEN, L8, L32))
    l0 = sv([numst(w, Av, '0', 'RR'), numst(w, Av, '1', 'RR'), lr, lin8(w, Av, [], '0 <_ 1', {}), lg1], 'letrd', '0 <_ %s' % L_)
    lsq = sv([numst(w, Av, '1', 'RR'), lr, lr, l0, lg1], 'lemul1ad', '( 1 x. %s ) <_ ( %s x. %s )' % (L_, L_, L_))
    sqv = sv([sv([lr], 'recnd', '%s e. CC' % L_)], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (L_, L_, L_))
    AQ, AP, AQP = '( abs ` %s )' % Q, '( abs ` %s )' % P, '( abs ` ( %s - %s ) )' % (Q, P)
    lvf = {AQ: sv([qc], 'abscld', '%s e. RR' % AQ), AP: sv([pc], 'abscld', '%s e. RR' % AP), AQP: sv([sv([qc, pc], 'subcld', '( %s - %s ) e. CC' % (Q, P))], 'abscld', '%s e. RR' % AQP),
           Lu: lur, L_: lr, '( %s / %s )' % (X8, DL): sv([x8r, dlv], 'rerpdivcld', '( %s / %s ) e. RR' % (X8, DL)),
           '( %s x. %s )' % (X8, DEN): sv([x8r, sv([denp], 'rpred', '%s e. RR' % DEN)], 'remulcld', '( %s x. %s ) e. RR' % (X8, DEN))}
    fin_ = lin8(w, Av, [tri, lnd, ghs, q3, pr, lul, lg1, lsq, sqv], '%s <_ ( %s x. ( %s ^ 2 ) )' % (AQ, KGH, L_), lvf, products=True)
    body = sv([fne, fin_], 'jca', '( ( F ` %s ) =/= 0 /\\ %s <_ ( %s x. ( %s ^ 2 ) ) )' % (SV, AQ, KGH, L_))
    conj2 = w.s([body], 'ralrimiva', '( %s -> A. v e. %s ( ( F ` %s ) =/= 0 /\\ %s <_ ( %s x. ( %s ^ 2 ) ) ) )' % (Au, IV, SV, AQ, KGH, L_))
    phi = su([conj1, conj2], 'jca', PHI)
    im = w.s([phi], 'ex', '( ( %s /\\ u e. %s ) -> ( %s -> %s ) )' % (A0, IT, GAPY, PHI))
    w.qed([ex, w.s([im], 'reximdva', '( %s -> ( %s -> %s ) )' % (A0, gc, GC))], 'mpd', S['ef2gh'])
    return run8(w)


if __name__ == '__main__':
    for g in sys.argv[1:] or ['ef2ghc', 'ef2ghs', 'ef2gh']:
        {'ef2ghc': gen_ghc, 'ef2ghs': gen_ghs, 'ef2gh': gen_gh}[g]()
