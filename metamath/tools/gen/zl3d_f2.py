"""ZL3d section F, part 2: zl3thy and zl3thfe.  `MM_DB=sorties/zl3d.mm python3 tools/gen/zl3d_f2.py [LABEL...]`"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))
from zl3d_f import *
from zl3d_f import _ztsub

only = sys.argv[1:]


def go(w):
    if only and w.label not in only:
        return True
    if os.environ.get('ZL3D_WRITE'):
        w.write(); print('WROTE', w.label, len(w.lines)); return True
    return runh(w) if L.HYPS.get(w.label) else w.run()


def want(label):
    return __name__ == '__main__' and (not only or label in only)


PAR = L.ZL3.PAR; YB = L.ZL3.YB; EPS = L.ZL3.EPS
TAU = '( M DChrGS Y )'


def zt_r(w, A, Z, X, P, v='r'):
    """closed equality ZT(Z,X,P) = ( v e. ZZ |-> ZTg(Z,v,X,P) ) and the renamed class"""
    ZR = '( %s e. ZZ |-> %s )' % (v, ZTg(Z, v, X, P))
    return w.s([ztsub_g(w, Z, X, P, 'n', v)], 'cbvmptv', '%s = %s' % (L.ZT(Z, X, P), ZR)), ZR


if want('zl3thy'):
    w = W('zl3thy', 'The theta transformation of a primitive character, on the full sums over ` ZZ ` : ` Theta_Y ( 1 / y ) = EPS y ^ ( a + 1/2 ) Theta_YB ( y ) ` .')
    A, Cc = ante_of('zl3thy')
    pr = D(w, A, 'simpl', [], L.PR); yrp = D(w, A, 'simpr', [], 'y e. RR+')
    ch = D(w, A, 'simpld', [pr], L.CH()); mn = D(w, A, 'simpld', [ch], 'M e. NN'); yd = D(w, A, 'simprd', [ch], 'Y e. %s' % DB)
    par = D(w, A, 'syl', [ch, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pp = D(w, A, 'simplld', [par], '%s e. { 0 , 1 }' % PAR); ybd = D(w, A, 'simplrd', [par], '%s e. %s' % (YB, DB))
    ym1 = D(w, A, 'simprld', [par], '( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (LMr, PAR)); ybm1 = D(w, A, 'simprrd', [par], '( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (YB, LMr, PAR))
    pn = par_nn0(w, A, pp, PAR)
    mc = D(w, A, 'nncnd', [mn], 'M e. CC'); mne = D(w, A, 'nnne0d', [mn], 'M =/= 0'); yc = D(w, A, 'rpcnd', [yrp], 'y e. CC'); yne = D(w, A, 'rpne0d', [yrp], 'y =/= 0')
    X1 = '( 1 / y )'
    ZTY1 = L.ZT('Y', X1, PAR)
    C0 = '( exp ` ( 1 / ( _pi x. ( %s / M ) ) ) )' % X1
    zt1 = D(w, A, 'syl3anc', [ch, D(w, A, 'jca', [pp, ym1], '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, LMr, PAR)), D(w, A, 'rpreccld', [yrp], '%s e. RR+' % X1), w.inst('zl3zt')],
            L.split_imp(S['zl3zt'])[1].replace(L.ZT('Z', 'X', 'P'), ZTY1).replace('( exp ` ( 1 / ( _pi x. ( X / M ) ) ) )', C0).replace(L.THP(L.CZ('Z'), 'X', 'P'), L.THP(L.CZ('Y'), X1, PAR)))
    eq1, ZR1 = zt_r(w, A, 'Y', X1, PAR)
    eq1A = w.s([eq1], 'a1i', '( %s -> %s = %s )' % (A, ZTY1, ZR1))
    hc1, _ = w.wcongr(L.HBF(ZTY1, C0), {}, A, {}, rules={ZTY1: (ZR1, eq1A)})
    hb1 = D(w, A, 'mpbid', [D(w, A, 'simpld', [zt1], L.HBF(ZTY1, C0)), hc1], L.HBF(ZR1, C0))
    GBr = L.GB(ZR1)
    rg = D(w, A, 'syl2anc', [mn, hb1, w.inst('zl3rg')], '%s = sum_ b e. ( 0 ..^ M ) %s' % (L.PZF(ZR1), L.PZF(GBr)))
    pz1, _ = w.rewrite(L.PZF(ZTY1), {ZTY1: (ZR1, eq1A)}, A)
    Ab = '( %s /\\ b e. ( 0 ..^ M ) )' % A
    eq1b = w.s([eq1], 'a1i', '( %s -> %s = %s )' % (Ab, ZTY1, ZR1))
    gbr, _ = w.rewrite(L.PZF(L.GB(ZTY1)), {ZTY1: (ZR1, eq1b)}, Ab)
    gb = D(w, Ab, 'zl3gb', [], '') if False else w.s([D(w, Ab, 'jca', [D(w, Ab, 'jca', [D(w, Ab, 'simpll', [], L.CH()) if False else D(w, Ab, 'syl', [D(w, Ab, 'simpl', [], A), w.s([ch], 'idi', '( %s -> %s )' % (A, L.CH()))], L.CH()),
                                                                                  D(w, Ab, 'simplr', [], 'y e. RR+')], '( %s /\\ y e. RR+ )' % L.CH()), D(w, Ab, 'simpr', [], 'b e. ( 0 ..^ M ) ')],
                                                    '( ( %s /\\ y e. RR+ ) /\\ b e. ( 0 ..^ M ) )' % L.CH()) if False else None], '', '') if False else None
    abch = D(w, Ab, 'jca', [D(w, Ab, 'jca', [D(w, Ab, 'syl', [w.s([], 'simpl', '( %s -> %s )' % (Ab, A)), w.s([ch], 'idi', '( %s -> %s )' % (A, L.CH()))], L.CH()), D(w, Ab, 'simplr', [], 'y e. RR+')],
                                             '( %s /\\ y e. RR+ )' % L.CH()), w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % Ab)], '( ( %s /\\ y e. RR+ ) /\\ b e. ( 0 ..^ M ) )' % L.CH())
    YBb = '( Y ` ( %s ` b ) )' % LMr
    cb_ = '( %s x. ( M ^ %s ) )' % (YBb, PAR)
    gbv = D(w, Ab, 'syl', [abch, w.inst('zl3gb')], '%s = ( %s x. %s )' % (L.PZF(L.GB(ZTY1)), cb_, L.THGR))
    MA = '( M ^ %s )' % PAR; NI = '( -u _i ^ %s )' % PAR; MY = '( M / y )'
    TC = '( %s ^c -u ( ( 1 / 2 ) + %s ) )' % (MY, PAR)
    ZG = L.PZF(L.GRB)
    K1 = '( %s x. ( %s x. %s ) )' % (MA, NI, TC)
    # constants in CC
    ybc = chval(w, Ab, 'Y', ad(w, Ab, yd, 'Y e. %s' % DB), 'b', w.s([w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % Ab), w.inst('elfzoelz')], 'syl', '( %s -> b e. ZZ )' % Ab))
    mac = D(w, Ab, 'expcld', [ad(w, Ab, mc, 'M e. CC'), ad(w, Ab, pn, '%s e. NN0' % PAR)], '%s e. CC' % MA)
    nic = D(w, Ab, 'expcld', [D(w, Ab, 'negcld', [cst(w, Ab, 'ax-icn', '_i e. CC')], '-u _i e. CC'), ad(w, Ab, pn, '%s e. NN0' % PAR)], '%s e. CC' % NI)
    tcc = D(w, Ab, 'cxpcld', [D(w, Ab, 'divcld', [ad(w, Ab, mc, 'M e. CC'), ad(w, Ab, yc, 'y e. CC'), ad(w, Ab, yne, 'y =/= 0')], '%s e. CC' % MY),
                               D(w, Ab, 'negcld', [D(w, Ab, 'addcld', [cst(w, Ab, 'halfcn', '( 1 / 2 ) e. CC'), D(w, Ab, 'nn0cnd', [ad(w, Ab, pn, '%s e. NN0' % PAR)], '%s e. CC' % PAR)], '( ( 1 / 2 ) + %s ) e. CC' % PAR)],
                                 '-u ( ( 1 / 2 ) + %s ) e. CC' % PAR)], '%s e. CC' % TC)
    bz = w.s([w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % Ab), w.inst('elfzoelz')], 'syl', '( %s -> b e. ZZ )' % Ab)
    myp = D(w, Ab, 'rpdivcld', [D(w, Ab, 'nnrpd', [ad(w, Ab, mn, 'M e. NN')], 'M e. RR+'), ad(w, Ab, yrp, 'y e. RR+')], '%s e. RR+' % MY)
    bmr = D(w, Ab, 'redivcld', [D(w, Ab, 'zred', [bz], 'b e. RR'), D(w, Ab, 'nnred', [ad(w, Ab, mn, 'M e. NN')], 'M e. RR'), ad(w, Ab, mne, 'M =/= 0')], '( b / M ) e. RR')
    grc = D(w, Ab, 'syl3anc', [myp, bmr, ad(w, Ab, pp, '%s e. { 0 , 1 }' % PAR), w.inst('zl3grc')], 'seq 1 ( + , %s ) e. dom ~~>' % pairmap(L.GRB, 'm'))
    grcn = seqcv_rename(w, Ab, L.GRB, grc, 'm', 'n')
    Abk = '( %s /\\ k e. ZZ )' % Ab
    kz_ = w.s([], 'simpr', '( %s -> k e. ZZ )' % Abk)
    cl = Closure(w, Abk, {'M': [ad(w, Abk, ad(w, Ab, mc, 'M e. CC'), 'M e. CC'), ad(w, Abk, ad(w, Ab, mne, 'M =/= 0'), 'M =/= 0')], 'b': D(w, Abk, 'zcnd', [ad(w, Abk, bz, 'b e. ZZ')], 'b e. CC'),
                          'k': D(w, Abk, 'zcnd', [kz_], 'k e. CC'), PAR: ad(w, Abk, ad(w, Ab, pn, '%s e. NN0' % PAR), '%s e. NN0' % PAR), '_pi': cst(w, Abk, 'picn', '_pi e. CC'), '_i': cst(w, Abk, 'ax-icn', '_i e. CC'),
                          MY: [D(w, Abk, 'rpcnd', [ad(w, Abk, myp, '%s e. RR+' % MY)], '%s e. CC' % MY), D(w, Abk, 'rpne0d', [ad(w, Abk, myp, '%s e. RR+' % MY)], '%s =/= 0' % MY)]})
    cl.atom(PAR); cl.atom(MY)
    GRbody = lambda cv, v: '( ( %s ^ %s ) x. ( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / %s ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. ( %s / M ) ) ) ) ) )' % (v, PAR, v, MY, v, cv)
    grf = D(w, Ab, 'fmptd', [cl.mem(GRbody('b', 'k'), 'CC'), eq_(w, L.GRB)], '%s : ZZ --> CC' % L.GRB)
    zgc = pz_cl(w, Ab, L.GRB, grf, grcn)
    rea = chain(w, Ab, ['( %s x. %s )' % (cb_, L.THGR), '( %s x. ( ( %s x. %s ) x. %s ) )' % (cb_, NI, TC, ZG), '( ( %s x. %s ) x. ( ( %s x. %s ) x. %s ) )' % (MA, YBb, NI, TC, ZG),
                     '( %s x. ( %s x. %s ) )' % (K1, YBb, ZG)],
                [D(w, Ab, 'oveq2d', [D(w, Ab, 'eqcomd', [D(w, Ab, 'mulassd', [nic, tcc, zgc], '( ( %s x. %s ) x. %s ) = %s' % (NI, TC, ZG, L.THGR))], '%s = ( ( %s x. %s ) x. %s )' % (L.THGR, NI, TC, ZG))],
                   '( %s x. %s ) = ( %s x. ( ( %s x. %s ) x. %s ) )' % (cb_, L.THGR, cb_, NI, TC, ZG)),
                 D(w, Ab, 'oveq1d', [D(w, Ab, 'mulcomd', [ybc, mac], '%s = ( %s x. %s )' % (cb_, MA, YBb))], '( %s x. ( ( %s x. %s ) x. %s ) ) = ( ( %s x. %s ) x. ( ( %s x. %s ) x. %s ) )' % (cb_, NI, TC, ZG, MA, YBb, NI, TC, ZG)),
                 D(w, Ab, 'mul4d', [mac, ybc, D(w, Ab, 'mulcld', [nic, tcc], '( %s x. %s ) e. CC' % (NI, TC)), zgc], '( ( %s x. %s ) x. ( ( %s x. %s ) x. %s ) ) = ( %s x. ( %s x. %s ) )' % (MA, YBb, NI, TC, ZG, K1, YBb, ZG))])
    per_b = chain(w, Ab, [L.PZF(GBr), L.PZF(L.GB(ZTY1)), '( %s x. %s )' % (cb_, L.THGR), '( %s x. ( %s x. %s ) )' % (K1, YBb, ZG)], [('r', gbr), gbv, rea])
    # the families HQ_b and Hc
    HQ = lambda cv: '( q e. ZZ |-> ( ( Y ` ( %s ` %s ) ) x. %s ) )' % (LMr, cv, GRbody(cv, 'q'))
    HC = '( c e. ( 0 ..^ M ) |-> %s )' % HQ('c')
    cs1 = w.s([w.s([], 'fveq2', '( c = b -> ( %s ` c ) = ( %s ` b ) )' % (LMr, LMr))], 'fveq2d', '( c = b -> ( Y ` ( %s ` c ) ) = %s )' % (LMr, YBb))
    cs2 = w.s([w.s([], 'oveq1', '( c = b -> ( c / M ) = ( b / M ) )')], 'oveq2d', '( c = b -> ( q x. ( c / M ) ) = ( q x. ( b / M ) ) )')
    cs3 = w.s([cs2], 'oveq2d', '( c = b -> ( ( 2 x. ( _i x. _pi ) ) x. ( q x. ( c / M ) ) ) = ( ( 2 x. ( _i x. _pi ) ) x. ( q x. ( b / M ) ) ) )')
    cs4 = w.s([cs3], 'fveq2d', '( c = b -> ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( q x. ( c / M ) ) ) ) = ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( q x. ( b / M ) ) ) ) )')
    EQ1 = '( exp ` -u ( _pi x. ( ( q ^ 2 ) / %s ) ) )' % MY
    cs5 = w.s([cs4], 'oveq2d', '( c = b -> ( %s x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( q x. ( c / M ) ) ) ) ) = ( %s x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( q x. ( b / M ) ) ) ) ) )' % (EQ1, EQ1))
    cs6 = w.s([cs5], 'oveq2d', '( c = b -> %s = %s )' % (GRbody('c', 'q'), GRbody('b', 'q')))
    cs7 = w.s([cs1, cs6], 'oveq12d', '( c = b -> ( ( Y ` ( %s ` c ) ) x. %s ) = ( %s x. %s ) )' % (LMr, GRbody('c', 'q'), YBb, GRbody('b', 'q')))
    csub = w.s([cs7], 'mpteq2dv', '( c = b -> %s = %s )' % (HQ('c'), HQ('b')))
    hcb = D(w, Ab, 'syl', [w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % Ab), w.s([csub, eq_(w, HC), w.s([w.s([], 'zex', 'ZZ e. _V')], 'mptex', '%s e. _V' % HQ('b'))], 'fvmpt',
                                                                                  '( b e. ( 0 ..^ M ) -> ( %s ` b ) = %s )' % (HC, HQ('b')))], '( %s ` b ) = %s' % (HC, HQ('b')))
    HCb = '( %s ` b )' % HC
    def hqv(A2, v, vz):
        """( A2 -> ( HQ_b ` v ) = ( Yb x. ( GRB ` v ) ) )"""
        def qs(a, b_):
            E = '( %s = %s ->' % (a, b_)
            p1 = w.s([], 'oveq1', '%s ( %s ^ %s ) = ( %s ^ %s ) )' % (E, a, PAR, b_, PAR))
            q1 = w.s([], 'oveq1', '%s ( %s ^ 2 ) = ( %s ^ 2 ) )' % (E, a, b_))
            q2 = w.s([q1], 'oveq1d', '%s ( ( %s ^ 2 ) / %s ) = ( ( %s ^ 2 ) / %s ) )' % (E, a, MY, b_, MY))
            q3 = w.s([q2], 'oveq2d', '%s ( _pi x. ( ( %s ^ 2 ) / %s ) ) = ( _pi x. ( ( %s ^ 2 ) / %s ) ) )' % (E, a, MY, b_, MY))
            q4 = w.s([q3], 'negeqd', '%s -u ( _pi x. ( ( %s ^ 2 ) / %s ) ) = -u ( _pi x. ( ( %s ^ 2 ) / %s ) ) )' % (E, a, MY, b_, MY))
            q5 = w.s([q4], 'fveq2d', '%s ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / %s ) ) ) = ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / %s ) ) ) )' % (E, a, MY, b_, MY))
            r1 = w.s([], 'oveq1', '%s ( %s x. ( b / M ) ) = ( %s x. ( b / M ) ) )' % (E, a, b_))
            r2 = w.s([r1], 'oveq2d', '%s ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. ( b / M ) ) ) = ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. ( b / M ) ) ) )' % (E, a, b_))
            r3 = w.s([r2], 'fveq2d', '%s ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. ( b / M ) ) ) ) = ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. ( b / M ) ) ) ) )' % (E, a, b_))
            s1 = w.s([q5, r3], 'oveq12d', '%s ( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / %s ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. ( b / M ) ) ) ) ) = ( ( exp ` -u ( _pi x. ( ( %s ^ 2 ) / %s ) ) ) x. ( exp ` ( ( 2 x. ( _i x. _pi ) ) x. ( %s x. ( b / M ) ) ) ) ) )' % (E, a, MY, a, b_, MY, b_))
            return w.s([p1, s1], 'oveq12d', '%s %s = %s )' % (E, GRbody('b', a), GRbody('b', b_)))
        a1 = D(w, A2, 'syl', [vz, w.s([w.s([qs('q', v)], 'oveq2d', '( q = %s -> ( %s x. %s ) = ( %s x. %s ) )' % (v, YBb, GRbody('b', 'q'), YBb, GRbody('b', v))), eq_(w, HQ('b')),
                                        w.s([], 'ovex', '( %s x. %s ) e. _V' % (YBb, GRbody('b', v)))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = ( %s x. %s ) )' % (v, HQ('b'), v, YBb, GRbody('b', v)))],
                '( %s ` %s ) = ( %s x. %s )' % (HQ('b'), v, YBb, GRbody('b', v)))
        GRp = '( p e. ZZ |-> %s )' % GRbody('b', 'p')
        cbp = w.s([qs('k', 'p')], 'cbvmptv', '%s = %s' % (L.GRB, GRp))
        a2a = w.s([w.s([cbp], 'fveq1i', '( %s ` %s ) = ( %s ` %s )' % (L.GRB, v, GRp, v))], 'a1i', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A2, L.GRB, v, GRp, v))
        a2b = D(w, A2, 'syl', [vz, w.s([qs('p', v), eq_(w, GRp), w.s([], 'ovex', '%s e. _V' % GRbody('b', v))], 'fvmpt', '( %s e. ZZ -> ( %s ` %s ) = %s )' % (v, GRp, v, GRbody('b', v)))],
                '( %s ` %s ) = %s' % (GRp, v, GRbody('b', v)))
        a2 = D(w, A2, 'eqtrd', [a2a, a2b], '( %s ` %s ) = %s' % (L.GRB, v, GRbody('b', v)))
        return D(w, A2, 'eqtr4d', [a1, D(w, A2, 'oveq2d', [a2], '( %s x. ( %s ` %s ) ) = ( %s x. %s )' % (YBb, L.GRB, v, YBb, GRbody('b', v)))], '( %s ` %s ) = ( %s x. ( %s ` %s ) )' % (HQ('b'), v, YBb, L.GRB, v))
    Abq = '( %s /\\ q e. ZZ )' % Ab
    qz = w.s([], 'simpr', '( %s -> q e. ZZ )' % Abq)
    clq = Closure(w, Abq, {'M': [ad(w, Abq, ad(w, Ab, mc, 'M e. CC'), 'M e. CC'), ad(w, Abq, ad(w, Ab, mne, 'M =/= 0'), 'M =/= 0')], 'b': D(w, Abq, 'zcnd', [ad(w, Abq, bz, 'b e. ZZ')], 'b e. CC'),
                           'q': D(w, Abq, 'zcnd', [qz], 'q e. CC'), PAR: ad(w, Abq, ad(w, Ab, pn, '%s e. NN0' % PAR), '%s e. NN0' % PAR), '_pi': cst(w, Abq, 'picn', '_pi e. CC'), '_i': cst(w, Abq, 'ax-icn', '_i e. CC'),
                           MY: [D(w, Abq, 'rpcnd', [ad(w, Abq, myp, '%s e. RR+' % MY)], '%s e. CC' % MY), D(w, Abq, 'rpne0d', [ad(w, Abq, myp, '%s e. RR+' % MY)], '%s =/= 0' % MY)], YBb: ad(w, Abq, ybc, '%s e. CC' % YBb)})
    clq.atom(PAR); clq.atom(MY); clq.atom(YBb)
    hqf = D(w, Ab, 'fmptd', [clq.mem('( %s x. %s )' % (YBb, GRbody('b', 'q')), 'CC'), eq_(w, HQ('b'))], '%s : ZZ --> CC' % HQ('b'))
    hcf = D(w, Ab, 'mpbird', [hqf, D(w, Ab, 'feq1d', [hcb], '( %s : ZZ --> CC <-> %s : ZZ --> CC )' % (HCb, HQ('b')))], '%s : ZZ --> CC' % HCb)
    def hcv(A2, v, vz, hq_):
        return D(w, A2, 'eqtrd', [D(w, A2, 'fveq1d', [ad(w, A2, hcb, '%s = %s' % (HCb, HQ('b')))], '( %s ` %s ) = ( %s ` %s )' % (HCb, v, HQ('b'), v)), hq_], '( %s ` %s ) = ( %s x. ( %s ` %s ) )' % (HCb, v, YBb, L.GRB, v))
    # convergence of the pairs of HCb
    Abk2 = '( %s /\\ j e. NN )' % Ab
    kn2 = w.s([], 'simpr', '( %s -> j e. NN )' % Abk2)
    kz2 = D(w, Abk2, 'nnzd', [kn2], 'j e. ZZ'); mkz2 = D(w, Abk2, 'znegcld', [kz2], '-u j e. ZZ')
    gfk = D(w, Abk2, 'ffvelcdmd', [ad(w, Abk2, grf, '%s : ZZ --> CC' % L.GRB), kz2], '( %s ` j ) e. CC' % L.GRB); gfm = D(w, Abk2, 'ffvelcdmd', [ad(w, Abk2, grf, '%s : ZZ --> CC' % L.GRB), mkz2], '( %s ` -u j ) e. CC' % L.GRB)
    PGk = '( ( %s ` j ) + ( %s ` -u j ) )' % (L.GRB, L.GRB)
    fk = D(w, Abk2, 'syl', [kn2, w.s([pairsub_(w, L.GRB, 'n', 'j'), eq_(w, pairmap(L.GRB, 'n')), w.s([], 'ovex', '%s e. _V' % PGk)], 'fvmpt', '( j e. NN -> ( %s ` j ) = %s )' % (pairmap(L.GRB, 'n'), PGk))],
           '( %s ` j ) = %s' % (pairmap(L.GRB, 'n'), PGk))
    PHk = '( ( %s ` j ) + ( %s ` -u j ) )' % (HCb, HCb)
    gk = D(w, Abk2, 'syl', [kn2, w.s([pairsub_(w, HCb, 'n', 'j'), eq_(w, pairmap(HCb, 'n')), w.s([], 'ovex', '%s e. _V' % PHk)], 'fvmpt', '( j e. NN -> ( %s ` j ) = %s )' % (pairmap(HCb, 'n'), PHk))],
           '( %s ` j ) = %s' % (pairmap(HCb, 'n'), PHk))
    ybk2 = ad(w, Abk2, ybc, '%s e. CC' % YBb)
    ph_ = D(w, Abk2, 'eqtr4d', [D(w, Abk2, 'oveq12d', [hcv(Abk2, 'j', kz2, hqv(Abk2, 'j', kz2)), hcv(Abk2, '-u j', mkz2, hqv(Abk2, '-u j', mkz2))], '%s = ( ( %s x. ( %s ` j ) ) + ( %s x. ( %s ` -u j ) ) )' % (PHk, YBb, L.GRB, YBb, L.GRB)),
                                D(w, Abk2, 'adddid', [ybk2, gfk, gfm], '( %s x. %s ) = ( ( %s x. ( %s ` j ) ) + ( %s x. ( %s ` -u j ) ) )' % (YBb, PGk, YBb, L.GRB, YBb, L.GRB))], '%s = ( %s x. %s )' % (PHk, YBb, PGk))
    gkf = D(w, Abk2, 'eqtrd', [gk, D(w, Abk2, 'eqtr4d', [ph_, D(w, Abk2, 'oveq2d', [fk], '( %s x. ( %s ` j ) ) = ( %s x. %s )' % (YBb, pairmap(L.GRB, 'n'), YBb, PGk))], '%s = ( %s x. ( %s ` j ) )' % (PHk, YBb, pairmap(L.GRB, 'n')))],
              '( %s ` j ) = ( %s x. ( %s ` j ) )' % (pairmap(HCb, 'n'), YBb, pairmap(L.GRB, 'n')))
    SQG = 'seq 1 ( + , %s )' % pairmap(L.GRB, 'n')
    gl = D(w, Ab, 'mpbid', [grcn, cst(w, Ab, 'climdm', '( %s e. dom ~~> <-> %s ~~> ( ~~> ` %s ) )' % (SQG, SQG, SQG))], '%s ~~> ( ~~> ` %s )' % (SQG, SQG))
    im = D(w, Ab, 'isermulc2', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, Ab, '1z', '1 e. ZZ'), ybc, gl, D(w, Abk2, 'eqeltrd', [fk, D(w, Abk2, 'addcld', [gfk, gfm], '%s e. CC' % PGk)], '( %s ` j ) e. CC' % pairmap(L.GRB, 'n')), gkf],
           'seq 1 ( + , %s ) ~~> ( %s x. ( ~~> ` %s ) )' % (pairmap(HCb, 'n'), YBb, SQG))
    hcc = D(w, Ab, 'syl', [im, w.s([w.s([], 'climrel', 'Rel ~~>')], 'releldmi', '( seq 1 ( + , %s ) ~~> ( %s x. ( ~~> ` %s ) ) -> seq 1 ( + , %s ) e. dom ~~> )' % (pairmap(HCb, 'n'), YBb, SQG, pairmap(HCb, 'n')))],
            'seq 1 ( + , %s ) e. dom ~~>' % pairmap(HCb, 'n'))
    # PZ ( HQ_b ) = Yb x. PZ ( GRB )
    Abm = '( %s /\\ m e. ZZ )' % Ab
    mzz = w.s([], 'simpr', '( %s -> m e. ZZ )' % Abm)
    ALLM = 'A. m e. ZZ ( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) )' % (L.GRB, HQ('b'), YBb, L.GRB)
    alm = D(w, Ab, 'ralrimiva', [D(w, Abm, 'jca', [D(w, Abm, 'ffvelcdmd', [ad(w, Abm, grf, '%s : ZZ --> CC' % L.GRB), mzz], '( %s ` m ) e. CC' % L.GRB), hqv(Abm, 'm', mzz)],
                                     '( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) )' % (L.GRB, HQ('b'), YBb, L.GRB))], ALLM)
    zx = lambda X: w.s([w.s([w.s([], 'zex', 'ZZ e. _V')], 'mptex', '%s e. _V' % X)], 'a1i', '( %s -> %s e. _V )' % (Ab, X))
    pzm1 = D(w, Ab, 'syl2anc', [D(w, Ab, '3jca', [ybc, zx(HQ('b')), zx(L.GRB)], '( %s e. CC /\\ %s e. _V /\\ %s e. _V )' % (YBb, HQ('b'), L.GRB)),
                                D(w, Ab, 'jca', [alm, grc], '( %s /\\ seq 1 ( + , %s ) e. dom ~~> )' % (ALLM, pairmap(L.GRB, 'm'))), w.inst('zl3pzm')], '%s = ( %s x. %s )' % (L.PZF(HQ('b')), YBb, ZG))
    pzhc, _ = w.rewrite(L.PZF(HCb), {HCb: (HQ('b'), hcb)}, Ab)
    pzhc2 = D(w, Ab, 'eqtrd', [pzhc, pzm1], '%s = ( %s x. %s )' % (L.PZF(HCb), YBb, ZG))
    # sums over b
    ofi = cst(w, A, 'fzofi', '( 0 ..^ M ) e. Fin')
    s1 = D(w, A, 'sumeq2dv', [D(w, Ab, 'eqtr4d', [per_b, D(w, Ab, 'oveq2d', [pzhc2], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (K1, L.PZF(HCb), K1, YBb, ZG))], '%s = ( %s x. %s )' % (L.PZF(GBr), K1, L.PZF(HCb)))],
           'sum_ b e. ( 0 ..^ M ) %s = sum_ b e. ( 0 ..^ M ) ( %s x. %s )' % (L.PZF(GBr), K1, L.PZF(HCb)))
    k1c = D(w, A, 'mulcld', [D(w, A, 'expcld', [mc, pn], '%s e. CC' % MA), D(w, A, 'mulcld', [D(w, A, 'expcld', [D(w, A, 'negcld', [cst(w, A, 'ax-icn', '_i e. CC')], '-u _i e. CC'), pn], '%s e. CC' % NI),
                                                                                          D(w, A, 'cxpcld', [D(w, A, 'divcld', [mc, yc, yne], '%s e. CC' % MY), D(w, A, 'negcld', [D(w, A, 'addcld', [cst(w, A, 'halfcn', '( 1 / 2 ) e. CC'), D(w, A, 'nn0cnd', [pn], '%s e. CC' % PAR)], '( ( 1 / 2 ) + %s ) e. CC' % PAR)], '-u ( ( 1 / 2 ) + %s ) e. CC' % PAR)], '%s e. CC' % TC)],
                                                                       '( %s x. %s ) e. CC' % (NI, TC))], '%s e. CC' % K1)
    s2 = D(w, A, 'fsummulc2', [ofi, k1c, D(w, Ab, 'eqeltrd', [pzhc2, D(w, Ab, 'mulcld', [ybc, zgc], '( %s x. %s ) e. CC' % (YBb, ZG))], '%s e. CC' % L.PZF(HCb))],
           '( %s x. sum_ b e. ( 0 ..^ M ) %s ) = sum_ b e. ( 0 ..^ M ) ( %s x. %s )' % (K1, L.PZF(HCb), K1, L.PZF(HCb)))
    ALLB = 'A. b e. ( 0 ..^ M ) ( ( %s ` b ) : ZZ --> CC /\\ seq 1 ( + , %s ) e. dom ~~> )' % (HC, pairmap('( %s ` b )' % HC, 'n'))
    alb = D(w, A, 'ralrimiva', [D(w, Ab, 'jca', [hcf, hcc], '( ( %s ` b ) : ZZ --> CC /\\ seq 1 ( + , %s ) e. dom ~~> )' % (HC, pairmap('( %s ` b )' % HC, 'n')))], ALLB)
    KSUM = '( k e. ZZ |-> sum_ b e. ( 0 ..^ M ) ( ( %s ` b ) ` k ) )' % HC
    pzf = D(w, A, 'syl2anc', [ofi, alb, w.inst('zl3pzf')], '%s = sum_ b e. ( 0 ..^ M ) %s' % (L.PZF(KSUM), L.PZF(HCb)))
    # the k-mapping is TAU times the theta term of YB
    Ak = '( %s /\\ k e. ZZ )' % A
    kz = w.s([], 'simpr', '( %s -> k e. ZZ )' % Ak)
    Akb = '( %s /\\ b e. ( 0 ..^ M ) )' % Ak
    akb_ab = D(w, Akb, 'jca', [D(w, Akb, 'simpll', [], A), w.s([], 'simpr', '( %s -> b e. ( 0 ..^ M ) )' % Akb)], Ab)
    kzb = D(w, Akb, 'simplr', [], 'k e. ZZ')
    liftb = lambda st, f: D(w, Akb, 'syl', [akb_ab, st], f)
    hck = D(w, Akb, 'eqtrd', [D(w, Akb, 'fveq1d', [liftb(hcb, '%s = %s' % (HCb, HQ('b')))], '( %s ` k ) = ( %s ` k )' % (HCb, HQ('b'))),
                              D(w, Akb, 'syl2anc', [akb_ab, kzb, w.s([w.s([w.s([hqv(Abk_ := '( %s /\\ k e. ZZ )' % Ab, 'k', w.s([], 'simpr', '( %s -> k e. ZZ )' % ('( %s /\\ k e. ZZ )' % Ab)))], 'ex', '( %s -> ( k e. ZZ -> ( %s ` k ) = ( %s x. ( %s ` k ) ) ) )' % (Ab, HQ('b'), YBb, L.GRB))], 'imp', '( ( %s /\\ k e. ZZ ) -> ( %s ` k ) = ( %s x. ( %s ` k ) ) )' % (Ab, HQ('b'), YBb, L.GRB))], 'idi', '( ( %s /\\ k e. ZZ ) -> ( %s ` k ) = ( %s x. ( %s ` k ) ) )' % (Ab, HQ('b'), YBb, L.GRB))],
                                '( %s ` k ) = ( %s x. ( %s ` k ) )' % (HQ('b'), YBb, L.GRB))],
              '( %s ` k ) = ( %s x. ( %s ` k ) )' % (HCb, YBb, L.GRB))
    ZTgB = ZTg(YB, 'k', 'y', PAR)
    gs = D(w, Ak, 'syl3anc', [ad(w, Ak, pr, L.PR), ad(w, Ak, yrp, 'y e. RR+'), kz, w.inst('zl3gs')],
           'sum_ b e. ( 0 ..^ M ) ( %s x. ( %s ` k ) ) = ( %s x. %s )' % (YBb, L.GRB, TAU, ZTgB))
    ksum = D(w, Ak, 'eqtrd', [D(w, Ak, 'sumeq2dv', [hck], 'sum_ b e. ( 0 ..^ M ) ( ( %s ` b ) ` k ) = sum_ b e. ( 0 ..^ M ) ( %s x. ( %s ` k ) )' % (HC, YBb, L.GRB)), gs],
             'sum_ b e. ( 0 ..^ M ) ( ( %s ` b ) ` k ) = ( %s x. %s )' % (HC, TAU, ZTgB))
    GK = '( k e. ZZ |-> ( %s x. %s ) )' % (TAU, ZTgB)
    kme = D(w, A, 'mpteq2dva', [ksum], '%s = %s' % (KSUM, GK))
    pzk, _ = w.rewrite(L.PZF(KSUM), {KSUM: (GK, kme)}, A)
    ZTYB = L.ZT(YB, 'y', PAR)
    CY = '( exp ` ( 1 / ( _pi x. ( y / M ) ) ) )'
    ztb = D(w, A, 'syl3anc', [D(w, A, 'jca', [mn, ybd], L.CH(YB)), D(w, A, 'jca', [pp, ybm1], '( %s e. { 0 , 1 } /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, YB, LMr, PAR)), yrp, w.inst('zl3zt')],
            L.split_imp(S['zl3zt'])[1].replace(L.ZT('Z', 'X', 'P'), ZTYB).replace('( exp ` ( 1 / ( _pi x. ( X / M ) ) ) )', CY).replace(L.THP(L.CZ('Z'), 'X', 'P'), L.THP(L.CZ(YB), 'y', PAR)))
    eqb, ZRB = zt_r(w, A, YB, 'y', PAR)
    eqbA = w.s([eqb], 'a1i', '( %s -> %s = %s )' % (A, ZTYB, ZRB))
    hcb2, _ = w.wcongr(L.HBF(ZTYB, CY), {}, A, {}, rules={ZTYB: (ZRB, eqbA)})
    hbb = D(w, A, 'mpbid', [D(w, A, 'simpld', [ztb], L.HBF(ZTYB, CY)), hcb2], L.HBF(ZRB, CY))
    pztb = D(w, A, 'syl', [hbb, w.inst('zl3pzt')], L.split_imp(S['zl3pzt'])[1].replace('( F `', '( %s `' % ZRB).replace('( 2 x. C )', '( 2 x. %s )' % CY))
    cvb = seqcv_rename(w, A, ZRB, D(w, A, 'simpld', [pztb], 'seq 1 ( + , %s ) e. dom ~~>' % pairmap(ZRB, 'n')), 'n', 'm')
    Am = '( %s /\\ m e. ZZ )' % A
    mz_ = w.s([], 'simpr', '( %s -> m e. ZZ )' % Am)
    zrbm = D(w, Am, 'syl', [mz_, w.s([ztsub_g(w, YB, 'y', PAR, 'r', 'm'), eq_(w, ZRB), w.s([], 'ovex', '%s e. _V' % ZTg(YB, 'm', 'y', PAR))], 'fvmpt', '( m e. ZZ -> ( %s ` m ) = %s )' % (ZRB, ZTg(YB, 'm', 'y', PAR)))],
             '( %s ` m ) = %s' % (ZRB, ZTg(YB, 'm', 'y', PAR)))
    gkm = D(w, Am, 'syl', [mz_, w.s([w.s([ztsub_g(w, YB, 'y', PAR, 'k', 'm')], 'oveq2d', '( k = m -> ( %s x. %s ) = ( %s x. %s ) )' % (TAU, ZTgB, TAU, ZTg(YB, 'm', 'y', PAR))), eq_(w, GK),
                                     w.s([], 'ovex', '( %s x. %s ) e. _V' % (TAU, ZTg(YB, 'm', 'y', PAR)))], 'fvmpt', '( m e. ZZ -> ( %s ` m ) = ( %s x. %s ) )' % (GK, TAU, ZTg(YB, 'm', 'y', PAR)))],
            '( %s ` m ) = ( %s x. %s )' % (GK, TAU, ZTg(YB, 'm', 'y', PAR)))
    zrbf = D(w, A, 'simpld', [hbb], '%s : ZZ --> CC' % ZRB)
    ALLM2 = 'A. m e. ZZ ( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) )' % (ZRB, GK, TAU, ZRB)
    alm2 = D(w, A, 'ralrimiva', [D(w, Am, 'jca', [D(w, Am, 'ffvelcdmd', [ad(w, Am, zrbf, '%s : ZZ --> CC' % ZRB), mz_], '( %s ` m ) e. CC' % ZRB),
                                                  D(w, Am, 'eqtr4d', [gkm, D(w, Am, 'oveq2d', [zrbm], '( %s x. ( %s ` m ) ) = ( %s x. %s )' % (TAU, ZRB, TAU, ZTg(YB, 'm', 'y', PAR)))], '( %s ` m ) = ( %s x. ( %s ` m ) )' % (GK, TAU, ZRB))],
                                    '( ( %s ` m ) e. CC /\\ ( %s ` m ) = ( %s x. ( %s ` m ) ) )' % (ZRB, GK, TAU, ZRB))], ALLM2)
    tauc = D(w, A, 'syl', [ch, w.inst('dchrgscl')], '%s e. CC' % TAU)
    zxa = lambda X: w.s([w.s([w.s([], 'zex', 'ZZ e. _V')], 'mptex', '%s e. _V' % X)], 'a1i', '( %s -> %s e. _V )' % (A, X))
    pzm2 = D(w, A, 'syl2anc', [D(w, A, '3jca', [tauc, zxa(GK), zxa(ZRB)], '( %s e. CC /\\ %s e. _V /\\ %s e. _V )' % (TAU, GK, ZRB)),
                               D(w, A, 'jca', [alm2, cvb], '( %s /\\ seq 1 ( + , %s ) e. dom ~~> )' % (ALLM2, pairmap(ZRB, 'm'))), w.inst('zl3pzm')], '%s = ( %s x. %s )' % (L.PZF(GK), TAU, L.PZF(ZRB)))
    pzb, _ = w.rewrite(L.PZF(ZTYB), {ZTYB: (ZRB, eqbA)}, A)
    # the constant
    YP = '( y ^c ( %s + ( 1 / 2 ) ) )' % PAR
    cs = D(w, A, 'syl2anc', [D(w, A, '3jca', [mn, pp, yrp], '( M e. NN /\\ %s e. { 0 , 1 } /\\ y e. RR+ )' % PAR), tauc, w.inst('zl3cst')],
           '( %s x. %s ) = ( %s x. %s )' % (K1, TAU, EPS, YP))
    PB = L.PZF(ZTYB); PBR = L.PZF(ZRB)
    pbc = D(w, A, 'eqeltrrd', [pzb, pz_cl(w, A, ZRB, zrbf, D(w, A, 'simpld', [pztb], 'seq 1 ( + , %s ) e. dom ~~>' % pairmap(ZRB, 'n')))], '%s e. CC' % PB) if False else None
    pbrc = pz_cl(w, A, ZRB, zrbf, D(w, A, 'simpld', [pztb], 'seq 1 ( + , %s ) e. dom ~~>' % pairmap(ZRB, 'n')))
    epsc = D(w, A, 'divcld', [tauc, D(w, A, 'mulcld', [D(w, A, 'expcld', [cst(w, A, 'ax-icn', '_i e. CC'), pn], '( _i ^ %s ) e. CC' % PAR), D(w, A, 'cxpcld', [mc, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) e. CC')],
                                                         '( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) ) e. CC' % PAR),
                              D(w, A, 'mulne0d', [D(w, A, 'expcld', [cst(w, A, 'ax-icn', '_i e. CC'), pn], '( _i ^ %s ) e. CC' % PAR), D(w, A, 'expne0d', [cst(w, A, 'ax-icn', '_i e. CC'), cst(w, A, 'ine0', '_i =/= 0'), D(w, A, 'nn0zd', [pn], '%s e. ZZ' % PAR)], '( _i ^ %s ) =/= 0' % PAR),
                                                  D(w, A, 'cxpcld', [mc, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) e. CC'), D(w, A, 'cxpne0d', [mc, mne, cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) =/= 0')],
                                '( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) ) =/= 0' % PAR)], '%s e. CC' % EPS)
    ypc = D(w, A, 'cxpcld', [yc, D(w, A, 'addcld', [D(w, A, 'nn0cnd', [pn], '%s e. CC' % PAR), cst(w, A, 'halfcn', '( 1 / 2 ) e. CC')], '( %s + ( 1 / 2 ) ) e. CC' % PAR)], '%s e. CC' % YP)
    SGB = 'sum_ b e. ( 0 ..^ M ) %s' % L.PZF(HCb)
    fin = chain(w, A, [L.PZF(ZTY1), L.PZF(ZR1), 'sum_ b e. ( 0 ..^ M ) %s' % L.PZF(GBr), 'sum_ b e. ( 0 ..^ M ) ( %s x. %s )' % (K1, L.PZF(HCb)), '( %s x. %s )' % (K1, SGB),
                       '( %s x. %s )' % (K1, L.PZF(KSUM)), '( %s x. %s )' % (K1, L.PZF(GK)), '( %s x. ( %s x. %s ) )' % (K1, TAU, PBR), '( ( %s x. %s ) x. %s )' % (K1, TAU, PBR),
                       '( ( %s x. %s ) x. %s )' % (EPS, YP, PBR), '( %s x. ( %s x. %s ) )' % (EPS, YP, PBR), '( %s x. ( %s x. %s ) )' % (EPS, YP, PB)],
                [pz1, rg, s1, ('r', s2), D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [pzf], '%s = %s' % (SGB, L.PZF(KSUM)))], '( %s x. %s ) = ( %s x. %s )' % (K1, SGB, K1, L.PZF(KSUM))),
                 D(w, A, 'oveq2d', [pzk], '( %s x. %s ) = ( %s x. %s )' % (K1, L.PZF(KSUM), K1, L.PZF(GK))),
                 D(w, A, 'oveq2d', [pzm2], '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (K1, L.PZF(GK), K1, TAU, PBR)),
                 ('r', D(w, A, 'mulassd', [k1c, tauc, pbrc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (K1, TAU, PBR, K1, TAU, PBR))),
                 D(w, A, 'oveq1d', [cs], '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (K1, TAU, PBR, EPS, YP, PBR)),
                 D(w, A, 'mulassd', [epsc, ypc, pbrc], '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (EPS, YP, PBR, EPS, YP, PBR)),
                 D(w, A, 'oveq2d', [D(w, A, 'oveq2d', [D(w, A, 'eqcomd', [pzb], '%s = %s' % (PBR, PB))], '( %s x. %s ) = ( %s x. %s )' % (YP, PBR, YP, PB))], '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (EPS, YP, PBR, EPS, YP, PB))])
    w.qed([fin], 'idi', S['zl3thy'])
    go(w)


if want('zl3tc'):
    w = W('zl3tc', 'The half theta series of a character converges: ` TH e. CC ` .')
    A, Cc = ante_of('zl3tc')
    C0 = '( exp ` ( 1 / ( _pi x. ( X / M ) ) ) )'
    zt = D(w, A, 'id' if False else 'idi', [], '') if False else D(w, A, 'syl', [D(w, A, 'id', [], A), w.inst('zl3zt')], L.split_imp(S['zl3zt'])[1])
    hb = D(w, A, 'simpld', [zt], L.HBF(ZTZ, C0))
    ff = D(w, A, 'simpld', [hb], '%s : ZZ --> CC' % ZTZ)
    r_ = D(w, A, 'simprd', [hb], '( %s e. RR /\\ A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) ) )' % (C0, ZTZ, C0))
    c0r = D(w, A, 'simpld', [r_], '%s e. RR' % C0); bnd = D(w, A, 'simprd', [r_], 'A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) )' % (ZTZ, C0))
    ZQ = '( q e. ZZ |-> %s )' % ZTv('q')
    cbq = w.s([_ztsub(w, 'n', 'q')], 'cbvmptv', '%s = %s' % (ZTZ, ZQ))
    fq = lambda A2, v: w.s([w.s([cbq], 'fveq1i', '( %s ` %s ) = ( %s ` %s )' % (ZTZ, v, ZQ, v))], 'a1i', '( %s -> ( %s ` %s ) = ( %s ` %s ) )' % (A2, ZTZ, v, ZQ, v))
    Ak = '( %s /\\ k e. NN )' % A
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    kz = D(w, Ak, 'nnzd', [kn], 'k e. ZZ')
    zkc = D(w, Ak, 'ffvelcdmd', [ad(w, Ak, ff, '%s : ZZ --> CC' % ZTZ), kz], '( %s ` k ) e. CC' % ZTZ)
    bdk = D(w, Ak, 'rspcdva', [w.s([w.s([w.s([], 'fveq2', '( i = k -> ( %s ` i ) = ( %s ` k ) )' % (ZTZ, ZTZ))], 'fveq2d', '( i = k -> ( abs ` ( %s ` i ) ) = ( abs ` ( %s ` k ) ) )' % (ZTZ, ZTZ)),
                                    w.s([w.s([w.s([], 'fveq2', '( i = k -> ( abs ` i ) = ( abs ` k ) )')], 'oveq2d', '( i = k -> ( ( 1 / 2 ) ^ ( abs ` i ) ) = ( ( 1 / 2 ) ^ ( abs ` k ) ) )')], 'oveq2d',
                                        '( i = k -> ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) ) = ( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) ) )' % (C0, C0))], 'breq12d',
                                   '( i = k -> ( ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) ) <-> ( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) ) ) )' % (ZTZ, C0, ZTZ, C0)),
                               ad(w, Ak, bnd, 'A. i e. ZZ ( abs ` ( %s ` i ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` i ) ) )' % (ZTZ, C0)), kz], '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) )' % (ZTZ, C0))
    kab = D(w, Ak, 'absidd', [D(w, Ak, 'nnred', [kn], 'k e. RR'), D(w, Ak, 'nn0ge0d', [D(w, Ak, 'nnnn0d', [kn], 'k e. NN0')], '0 <_ k')], '( abs ` k ) = k')
    bdk2 = D(w, Ak, 'breqtrd', [bdk, D(w, Ak, 'oveq2d', [D(w, Ak, 'oveq2d', [kab], '( ( 1 / 2 ) ^ ( abs ` k ) ) = ( ( 1 / 2 ) ^ k )')], '( %s x. ( ( 1 / 2 ) ^ ( abs ` k ) ) ) = ( %s x. ( ( 1 / 2 ) ^ k ) )' % (C0, C0))],
             '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (ZTZ, C0))
    zqk = D(w, Ak, 'eqeltrrd', [fq(Ak, 'k'), zkc], '( %s ` k ) e. CC' % ZQ)
    bq = D(w, Ak, 'eqbrtrrd', [D(w, Ak, 'fveq2d', [fq(Ak, 'k')], '( abs ` ( %s ` k ) ) = ( abs ` ( %s ` k ) )' % (ZTZ, ZQ)), bdk2], '( abs ` ( %s ` k ) ) <_ ( %s x. ( ( 1 / 2 ) ^ k ) )' % (ZQ, C0))
    ms = D(w, A, 'zl3mser', [c0r, cst(w, A, 'halfre', '( 1 / 2 ) e. RR'), cst(w, A, 'halfge0', '0 <_ ( 1 / 2 )'), cst(w, A, 'halflt1', '( 1 / 2 ) < 1'), zqk, bq],
           '( seq 1 ( + , %s ) e. dom ~~> /\\ ( abs ` sum_ k e. NN ( %s ` k ) ) <_ ( ( %s x. ( 1 / 2 ) ) / ( 1 - ( 1 / 2 ) ) ) )' % (ZQ, ZQ, C0))
    An = '( %s /\\ n e. NN )' % A
    nn_ = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    zqn = D(w, An, 'eqeltrrd', [fq(An, 'n'), D(w, An, 'ffvelcdmd', [ad(w, An, ff, '%s : ZZ --> CC' % ZTZ), D(w, An, 'nnzd', [nn_], 'n e. ZZ')], '( %s ` n ) e. CC' % ZTZ)], '( %s ` n ) e. CC' % ZQ)
    sc = D(w, A, 'isumcl', [w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), cst(w, A, '1z', '1 e. ZZ'), D(w, An, 'eqidd', [], '( %s ` n ) = ( %s ` n )' % (ZQ, ZQ)), zqn, D(w, A, 'simpld', [ms], 'seq 1 ( + , %s ) e. dom ~~>' % ZQ)],
           'sum_ n e. NN ( %s ` n ) e. CC' % ZQ)
    CZZ = L.CZ('Z')
    THv = lambda v: '( ( %s ` %s ) x. ( ( %s ^ P ) x. %s ) )' % (CZZ, v, v, EXn(v))
    czn = D(w, An, 'syl', [nn_, w.s([w.s([w.s([], 'fveq2', '( a = n -> ( %s ` a ) = ( %s ` n ) )' % (LMr, LMr))], 'fveq2d', '( a = n -> ( Z ` ( %s ` a ) ) = ( Z ` ( %s ` n ) ) )' % (LMr, LMr)),
                                     eq_(w, CZZ), w.s([], 'fvex', '( Z ` ( %s ` n ) ) e. _V' % LMr)], 'fvmpt', '( n e. NN -> ( %s ` n ) = ( Z ` ( %s ` n ) ) )' % (CZZ, LMr))],
            '( %s ` n ) = ( Z ` ( %s ` n ) )' % (CZZ, LMr))
    qth = D(w, An, 'eqtr4d', [D(w, An, 'eqtr3d', [fq(An, 'n'), ztval(w, An, 'n', D(w, An, 'nnzd', [nn_], 'n e. ZZ'))], '( %s ` n ) = %s' % (ZQ, ZTv('n'))),
                              D(w, An, 'oveq1d', [czn], '%s = ( ( Z ` ( %s ` n ) ) x. ( ( n ^ P ) x. %s ) )' % (THv('n'), LMr, EXn('n')))], '( %s ` n ) = %s' % (ZQ, THv('n')))
    w.qed([D(w, A, 'sumeq2dv', [qth], 'sum_ n e. NN ( %s ` n ) = %s' % (ZQ, L.THP(CZZ, 'X', 'P'))), sc], 'eqeltrrd', S['zl3tc'])
    go(w)


if want('zl3thfe'):
    w = W('zl3thfe', 'The theta functional equation of a primitive Dirichlet character ( Davenport ch. 9 ): ` RM / 2 + TH ( Y , 1 / y ) = EPS y ^ ( a + 1/2 ) ( RM / 2 + TH ( YB , y ) ) ` .')
    A, Cc = ante_of('zl3thfe')
    RM = L.ZL3.RM
    Ay = '( %s /\\ y e. RR+ )' % A
    pr = w.s([], 'simpl', '( %s -> %s )' % (Ay, L.PR)); yrp = w.s([], 'simpr', '( %s -> y e. RR+ )' % Ay)
    ch = D(w, Ay, 'simpld', [pr], L.CH()); mn = D(w, Ay, 'simpld', [ch], 'M e. NN')
    par = D(w, Ay, 'syl', [ch, w.inst('zl3par')], L.split_imp(S['zl3par'])[1])
    pp = D(w, Ay, 'simplld', [par], '%s e. { 0 , 1 }' % PAR); ybd = D(w, Ay, 'simplrd', [par], '%s e. %s' % (YB, DB))
    ym1 = D(w, Ay, 'simprld', [par], '( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (LMr, PAR)); ybm1 = D(w, Ay, 'simprrd', [par], '( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s )' % (YB, LMr, PAR))
    X1 = '( 1 / y )'
    ha = D(w, Ay, 'jca', [pp, ym1], '( %s e. { 0 , 1 } /\\ ( Y ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, LMr, PAR))
    hb_ = D(w, Ay, 'jca', [pp, ybm1], '( %s e. { 0 , 1 } /\\ ( %s ` ( %s ` -u 1 ) ) = ( -u 1 ^ %s ) )' % (PAR, YB, LMr, PAR))
    chb = D(w, Ay, 'jca', [mn, ybd], L.CH(YB))
    x1p = D(w, Ay, 'rpreccld', [yrp], '%s e. RR+' % X1)
    def zt_(Z, chz, hz, X, xp):
        C0 = '( exp ` ( 1 / ( _pi x. ( %s / M ) ) ) )' % X
        return D(w, Ay, 'syl3anc', [chz, hz, xp, w.inst('zl3zt')],
                 L.split_imp(S['zl3zt'])[1].replace(L.ZT('Z', 'X', 'P'), L.ZT(Z, X, PAR)).replace('( exp ` ( 1 / ( _pi x. ( X / M ) ) ) )', C0).replace(L.THP(L.CZ('Z'), 'X', 'P'), L.THP(L.CZ(Z), X, PAR)))
    za = zt_('Y', ch, ha, X1, x1p); zb = zt_(YB, chb, hb_, 'y', yrp)
    PA_, PB_ = L.PZF(L.ZT('Y', X1, PAR)), L.PZF(L.ZT(YB, 'y', PAR))
    TA, TB = L.THP(L.CZ('Y'), X1, PAR), L.THP(L.CZ(YB), 'y', PAR)
    pa = D(w, Ay, 'simprd', [za], '%s = ( %s + ( 2 x. %s ) )' % (PA_, RM, TA)); pb = D(w, Ay, 'simprd', [zb], '%s = ( %s + ( 2 x. %s ) )' % (PB_, RM, TB))
    tac = D(w, Ay, 'syl3anc', [ch, ha, x1p, w.inst('zl3tc')], '%s e. CC' % TA); tbc = D(w, Ay, 'syl3anc', [chb, hb_, yrp, w.inst('zl3tc')], '%s e. CC' % TB)
    thy = D(w, Ay, 'syl2anc', [pr, yrp, w.inst('zl3thy')], '%s = ( %s x. ( ( y ^c ( %s + ( 1 / 2 ) ) ) x. %s ) )' % (PA_, EPS, PAR, PB_))
    rmc = D(w, Ay, 'ifcld', [cst(w, Ay, 'ax-1cn', '1 e. CC'), cst(w, Ay, '0cn', '0 e. CC')], '%s e. CC' % RM)
    tc = cst(w, Ay, '2cn', '2 e. CC'); tne = cst(w, Ay, '2ne0', '2 =/= 0')
    def half(T, tcl):
        """( ( RM + ( 2 x. T ) ) / 2 ) = ( ( RM / 2 ) + T )"""
        return D(w, Ay, 'eqtrd', [D(w, Ay, 'divdird', [rmc, D(w, Ay, 'mulcld', [tc, tcl], '( 2 x. %s ) e. CC' % T), tc, tne], '( ( %s + ( 2 x. %s ) ) / 2 ) = ( ( %s / 2 ) + ( ( 2 x. %s ) / 2 ) )' % (RM, T, RM, T)),
                                  D(w, Ay, 'oveq2d', [D(w, Ay, 'divcan3d', [tcl, tc, tne], '( ( 2 x. %s ) / 2 ) = %s' % (T, T))], '( ( %s / 2 ) + ( ( 2 x. %s ) / 2 ) ) = ( ( %s / 2 ) + %s )' % (RM, T, RM, T))],
                 '( ( %s + ( 2 x. %s ) ) / 2 ) = ( ( %s / 2 ) + %s )' % (RM, T, RM, T))
    YP = '( y ^c ( %s + ( 1 / 2 ) ) )' % PAR
    ypc = D(w, Ay, 'cxpcld', [D(w, Ay, 'rpcnd', [yrp], 'y e. CC'), D(w, Ay, 'addcld', [D(w, Ay, 'nn0cnd', [par_nn0(w, Ay, pp, PAR)], '%s e. CC' % PAR), cst(w, Ay, 'halfcn', '( 1 / 2 ) e. CC')], '( %s + ( 1 / 2 ) ) e. CC' % PAR)], '%s e. CC' % YP)
    mc = D(w, Ay, 'nncnd', [mn], 'M e. CC'); mne = D(w, Ay, 'nnne0d', [mn], 'M =/= 0')
    pn = par_nn0(w, Ay, pp, PAR)
    qq = '( ( _i ^ %s ) x. ( M ^c ( 1 / 2 ) ) )' % PAR
    epsc = D(w, Ay, 'divcld', [D(w, Ay, 'syl', [ch, w.inst('dchrgscl')], '( M DChrGS Y ) e. CC'),
                               D(w, Ay, 'mulcld', [D(w, Ay, 'expcld', [cst(w, Ay, 'ax-icn', '_i e. CC'), pn], '( _i ^ %s ) e. CC' % PAR), D(w, Ay, 'cxpcld', [mc, cst(w, Ay, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) e. CC')], '%s e. CC' % qq),
                               D(w, Ay, 'mulne0d', [D(w, Ay, 'expcld', [cst(w, Ay, 'ax-icn', '_i e. CC'), pn], '( _i ^ %s ) e. CC' % PAR), D(w, Ay, 'expne0d', [cst(w, Ay, 'ax-icn', '_i e. CC'), cst(w, Ay, 'ine0', '_i =/= 0'), D(w, Ay, 'nn0zd', [pn], '%s e. ZZ' % PAR)], '( _i ^ %s ) =/= 0' % PAR),
                                                    D(w, Ay, 'cxpcld', [mc, cst(w, Ay, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) e. CC'), D(w, Ay, 'cxpne0d', [mc, mne, cst(w, Ay, 'halfcn', '( 1 / 2 ) e. CC')], '( M ^c ( 1 / 2 ) ) =/= 0')], '%s =/= 0' % qq)],
               '%s e. CC' % EPS)
    pbc = D(w, Ay, 'eqeltrd', [pb, D(w, Ay, 'addcld', [rmc, D(w, Ay, 'mulcld', [tc, tbc], '( 2 x. %s ) e. CC' % TB)], '( %s + ( 2 x. %s ) ) e. CC' % (RM, TB))], '%s e. CC' % PB_)
    LA, LB = '( ( %s / 2 ) + %s )' % (RM, TA), '( ( %s / 2 ) + %s )' % (RM, TB)
    fin = chain(w, Ay, [LA, '( ( %s + ( 2 x. %s ) ) / 2 )' % (RM, TA), '( %s / 2 )' % PA_, '( ( %s x. ( %s x. %s ) ) / 2 )' % (EPS, YP, PB_), '( %s x. ( ( %s x. %s ) / 2 ) )' % (EPS, YP, PB_),
                        '( %s x. ( %s x. ( %s / 2 ) ) )' % (EPS, YP, PB_), '( %s x. ( %s x. ( ( %s + ( 2 x. %s ) ) / 2 ) ) )' % (EPS, YP, RM, TB), '( %s x. ( %s x. %s ) )' % (EPS, YP, LB)],
                [('r', half(TA, tac)), ('r', D(w, Ay, 'oveq1d', [pa], '( %s / 2 ) = ( ( %s + ( 2 x. %s ) ) / 2 )' % (PA_, RM, TA))),
                 D(w, Ay, 'oveq1d', [thy], '( %s / 2 ) = ( ( %s x. ( %s x. %s ) ) / 2 )' % (PA_, EPS, YP, PB_)),
                 D(w, Ay, 'divassd', [epsc, D(w, Ay, 'mulcld', [ypc, pbc], '( %s x. %s ) e. CC' % (YP, PB_)), tc, tne], '( ( %s x. ( %s x. %s ) ) / 2 ) = ( %s x. ( ( %s x. %s ) / 2 ) )' % (EPS, YP, PB_, EPS, YP, PB_)),
                 D(w, Ay, 'oveq2d', [D(w, Ay, 'divassd', [ypc, pbc, tc, tne], '( ( %s x. %s ) / 2 ) = ( %s x. ( %s / 2 ) )' % (YP, PB_, YP, PB_))], '( %s x. ( ( %s x. %s ) / 2 ) ) = ( %s x. ( %s x. ( %s / 2 ) ) )' % (EPS, YP, PB_, EPS, YP, PB_)),
                 D(w, Ay, 'oveq2d', [D(w, Ay, 'oveq2d', [D(w, Ay, 'oveq1d', [pb], '( %s / 2 ) = ( ( %s + ( 2 x. %s ) ) / 2 )' % (PB_, RM, TB))], '( %s x. ( %s / 2 ) ) = ( %s x. ( ( %s + ( 2 x. %s ) ) / 2 ) )' % (YP, PB_, YP, RM, TB))],
                   '( %s x. ( %s x. ( %s / 2 ) ) ) = ( %s x. ( %s x. ( ( %s + ( 2 x. %s ) ) / 2 ) ) )' % (EPS, YP, PB_, EPS, YP, RM, TB)),
                 D(w, Ay, 'oveq2d', [D(w, Ay, 'oveq2d', [half(TB, tbc)], '( %s x. ( ( %s + ( 2 x. %s ) ) / 2 ) ) = ( %s x. %s )' % (YP, RM, TB, YP, LB))], '( %s x. ( %s x. ( ( %s + ( 2 x. %s ) ) / 2 ) ) ) = ( %s x. ( %s x. %s ) )' % (EPS, YP, RM, TB, EPS, YP, LB))])
    w.qed([D(w, A, 'ralrimiva', [fin], L.split_imp(S['zl3thfe'])[1])], 'idi', S['zl3thfe'])
    go(w)
