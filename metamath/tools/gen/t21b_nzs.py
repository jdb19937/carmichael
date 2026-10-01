"""Sortie T21b: t21nzs (norm_zeroSum_le)."""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from t21b_h import *
from ef3lib import ringeq
import cl as _cl


def gen_nzs():
    w = W('t21nzs', 'The zero sum of the explicit formula is at most ` 3 ` times the weighted sum ` sum ord Y ^ Re rho / ( 1 + abs Im rho ) ` : ` 1 + abs Im rho <_ 3 abs rho ` on ` Re rho >_ 1 / 2 ` (Lean ` norm_zeroSum_le ` ).')
    A0, concl = split_imp(SB['t21nzs'])
    s = S_(w, A0)
    u = unpackA(w, A0)
    nn = u['N e. NN']; xb = u['X e. ( Base ` ( DChr ` N ) )']; tr = u['T e. RR']; yp = u['Y e. RR+']
    yr = s([yp], 'rpred', 'Y e. RR')
    fin, tc, d = sc_terms(w, A0, 'N', 'X', nn, xb, tr, yr)
    C2, qf, ordn, qn0 = d['C2'], d['qf'], d['ordn'], d['qn0']
    s2 = S_(w, C2)
    Z = d['Z']
    O = '( %s holord q )' % EN
    G = '( abs ` ( Im ` q ) )'
    AQ = '( abs ` q )'
    YR = '( Y ^c ( Re ` q ) )'
    TERM = '( %s x. ( ( Y ^c q ) / q ) )' % O
    qc = qf['qc']
    orr = s2([ordn], 'nnred', '%s e. RR' % O); oc = s2([orr], 'recnd', '%s e. CC' % O)
    o0 = s2([s2([ordn], 'nnnn0d', '%s e. NN0' % O)], 'nn0ge0d', '0 <_ %s' % O)
    ypc = lift(w, yp, C2)
    yqc = s2([s2([ypc], 'rpcnd', 'Y e. CC'), qc], 'cxpcld', '( Y ^c q ) e. CC')
    a1 = s2([oc, s2([yqc, qc, qn0], 'divcld', '( ( Y ^c q ) / q ) e. CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( ( Y ^c q ) / q ) ) )' % (TERM, O))
    a2 = s2([orr, o0], 'absidd', '( abs ` %s ) = %s' % (O, O))
    a3 = s2([yqc, qc, qn0], 'absdivd', '( abs ` ( ( Y ^c q ) / q ) ) = ( ( abs ` ( Y ^c q ) ) / %s )' % AQ)
    a4 = ap(w, C2, [ypc, qc], 'abscxp', '( abs ` ( Y ^c q ) ) = %s' % YR)
    aqp = s2([qc, qn0], 'absrpcld', '%s e. RR+' % AQ)
    yrr = s2([ypc, qf['re']], 'rpcxpcld', '%s e. RR+' % YR)
    a5 = s2([s2([s2([a4], 'oveq1d', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s / %s )' % (AQ, YR, AQ)), s2([s2([yrr], 'rpcnd', '%s e. CC' % YR), s2([aqp], 'rpcnd', '%s e. CC' % AQ), s2([aqp], 'rpne0d', '%s =/= 0' % AQ)], 'divrecd',
                '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (YR, AQ, YR, AQ))], 'eqtrd', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s x. ( 1 / %s ) )' % (AQ, YR, AQ))], 'x', 'x') if False else None
    a5 = s2([s2([a4], 'oveq1d', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s / %s )' % (AQ, YR, AQ)), s2([s2([yrr], 'rpcnd', '%s e. CC' % YR), s2([aqp], 'rpcnd', '%s e. CC' % AQ), s2([aqp], 'rpne0d', '%s =/= 0' % AQ)], 'divrecd',
             '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (YR, AQ, YR, AQ))], 'eqtrd', '( ( abs ` ( Y ^c q ) ) / %s ) = ( %s x. ( 1 / %s ) )' % (AQ, YR, AQ))
    RQ = '( %s x. ( 1 / %s ) )' % (YR, AQ)
    ab = s2([a1, s2([a2, s2([a3, a5], 'eqtrd', '( abs ` ( ( Y ^c q ) / q ) ) = %s' % RQ)], 'oveq12d', '( ( abs ` %s ) x. ( abs ` ( ( Y ^c q ) / q ) ) ) = ( %s x. %s )' % (O, O, RQ))], 'eqtrd',
            '( abs ` %s ) = ( %s x. %s )' % (TERM, O, RQ))
    # ( 1 + g ) / 3 <_ abs q
    RE = '( Re ` q )'; ARE = '( abs ` ( Re ` q ) )'
    aqr = s2([aqp], 'rpred', '%s e. RR' % AQ)
    are_r = s2([qf['re']], 'recnd', '%s e. CC' % RE); are_r = s2([are_r], 'abscld', '%s e. RR' % ARE)
    h1 = s2([qf['re'], w.inst('leabs')], 'syl', '%s <_ %s' % (RE, ARE))
    h2 = s2([qc, w.inst('absrele')], 'syl', '%s <_ %s' % (ARE, AQ))
    h3 = s2([qc, w.inst('absimle')], 'syl', '%s <_ %s' % (G, AQ))
    g13 = '( ( 1 + %s ) / 3 )' % G
    lo = lin.linarith(w, C2, [h1, h2, h3, qf['lo']], '%s <_ %s' % (g13, AQ), leaves={RE: qf['re'], ARE: are_r, AQ: aqr, G: qf['imr']})
    g1p = s2([s2([s2([], '1red', '1 e. RR'), qf['imr']], 'readdcld', '( 1 + %s ) e. RR' % G), lin.linarith(w, C2, [qf['im0']], '0 < ( 1 + %s )' % G, leaves={G: qf['imr']})], 'elrpd', '( 1 + %s ) e. RR+' % G)
    g3p = s2([g1p, s2([w.s([], '3rp', '3 e. RR+')], 'a1i', '3 e. RR+')], 'rpdivcld', '%s e. RR+' % g13)
    rec = s2([lo, s2([g3p, aqp], 'lerecd', '( %s <_ %s <-> ( 1 / %s ) <_ ( 1 / %s ) )' % (g13, AQ, AQ, g13))], 'mpbid', '( 1 / %s ) <_ ( 1 / %s )' % (AQ, g13))
    B = '( 1 / ( 1 + %s ) )' % G
    g1c = s2([g1p], 'rpcnd', '( 1 + %s ) e. CC' % G)
    r2 = s2([g1c, s2([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC'), s2([g1p], 'rpne0d', '( 1 + %s ) =/= 0' % G), s2([w.s([], '3ne0', '3 =/= 0')], 'a1i', '3 =/= 0')], 'recdivd', '( 1 / %s ) = ( 3 / ( 1 + %s ) )' % (g13, G))
    r3 = s2([s2([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC'), g1c, s2([g1p], 'rpne0d', '( 1 + %s ) =/= 0' % G)], 'divrecd', '( 3 / ( 1 + %s ) ) = ( 3 x. %s )' % (G, B))
    rec2 = s2([rec, s2([r2, r3], 'eqtrd', '( 1 / %s ) = ( 3 x. %s )' % (g13, B))], 'breqtrd', '( 1 / %s ) <_ ( 3 x. %s )' % (AQ, B))
    br = s2([g1p], 'rprecred', '%s e. RR' % B)
    b3r = s2([s2([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), br], 'remulcld', '( 3 x. %s ) e. RR' % B)
    iqr = s2([aqp], 'rprecred', '( 1 / %s ) e. RR' % AQ)
    yrr_ = s2([yrr], 'rpred', '%s e. RR' % YR); yr0 = s2([yrr], 'rpge0d', '0 <_ %s' % YR)
    m1 = s2([iqr, b3r, yrr_, yr0, rec2], 'lemul2ad', '%s <_ ( %s x. ( 3 x. %s ) )' % (RQ, YR, B))
    RQ2 = '( %s x. ( 3 x. %s ) )' % (YR, B)
    m2 = s2([s2([yrr_, iqr], 'remulcld', '%s e. RR' % RQ), s2([yrr_, b3r], 'remulcld', '%s e. RR' % RQ2), orr, o0, m1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (O, RQ, O, RQ2))
    WTX = WT(EN)
    wt = s2([oc, g1c, s2([g1p], 'rpne0d', '( 1 + %s ) =/= 0' % G)], 'divrecd', '%s = ( %s x. %s )' % (WTX, O, B))
    RHS = '( 3 x. ( %s x. %s ) )' % (WTX, YR)
    cl = _cl.Closure(w, C2, {})
    for k_, st_ in ((O, orr), (YR, yrr_), (B, br)):
        cl.leaf(k_, 'RR', st_); cl.atom(k_)
    rq = ringeq(w, C2, '( %s x. %s )' % (O, RQ2), '( 3 x. ( ( %s x. %s ) x. %s ) )' % (O, B, YR), cl)
    rq2 = s2([rq, s2([s2([s2([wt], 'eqcomd', '( %s x. %s ) = %s' % (O, B, WTX))], 'oveq1d', '( ( %s x. %s ) x. %s ) = ( %s x. %s )' % (O, B, YR, WTX, YR))], 'oveq2d',
                                                                    '( 3 x. ( ( %s x. %s ) x. %s ) ) = %s' % (O, B, YR, RHS))], 'eqtrd', '( %s x. %s ) = %s' % (O, RQ2, RHS))
    pt = s2([s2([ab, m2], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. %s )' % (TERM, O, RQ2)), rq2], 'breqtrd', '( abs ` %s ) <_ %s' % (TERM, RHS))
    # sums
    fa = s([fin, tc], 'fsumabs', '( abs ` %s ) <_ sum_ q e. %s ( abs ` %s )' % (SC(EN, 'T', 'Y'), Z, TERM))
    wtr = s2([orr, g1p], 'rerpdivcld', '%s e. RR' % WTX)
    wyr = s2([wtr, yrr_], 'remulcld', '( %s x. %s ) e. RR' % (WTX, YR))
    rr_ = s2([s2([w.s([], '3re', '3 e. RR')], 'a1i', '3 e. RR'), wyr], 'remulcld', '%s e. RR' % RHS)
    fl = s([fin, s2([tc], 'abscld', '( abs ` %s ) e. RR' % TERM), rr_, pt], 'fsumle', 'sum_ q e. %s ( abs ` %s ) <_ sum_ q e. %s %s' % (Z, TERM, Z, RHS))
    fm = s([fin, s([w.s([], '3cn', '3 e. CC')], 'a1i', '3 e. CC'), s2([wyr], 'recnd', '( %s x. %s ) e. CC' % (WTX, YR))], 'fsummulc2', '( 3 x. sum_ q e. %s ( %s x. %s ) ) = sum_ q e. %s %s' % (Z, WTX, YR, Z, RHS))
    SR = 'sum_ q e. %s ( abs ` %s )' % (Z, TERM)
    c = s([fa, fl], 'x', 'x') if False else None
    lhsr = s([s([fin, tc], 'fsumcl', '%s e. CC' % SC(EN, 'T', 'Y'))], 'abscld', '( abs ` %s ) e. RR' % SC(EN, 'T', 'Y'))
    srr = s([fin, s2([tc], 'abscld', '( abs ` %s ) e. RR' % TERM)], 'fsumrecl', '%s e. RR' % SR)
    s3r = s([fin, rr_], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (Z, RHS))
    ch = s([lhsr, srr, s3r, fa, fl], 'letrd', '( abs ` %s ) <_ sum_ q e. %s %s' % (SC(EN, 'T', 'Y'), Z, RHS))
    w.qed([ch, fm], 'breqtrrd', SB['t21nzs'])
    return go(w)


if __name__ == '__main__':
    gen_nzs()
