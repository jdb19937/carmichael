"""Sortie Z6b, section 4: the anchor identity on Re w = 3.
z6anp   points of the segment: Re = 3, in DG, the term value and its majorant 32 R X^3 K^-2
z6anl   per height: the n-series integrated termwise converges to the segment integral of G3(R)
z6anv   each term integrates to c_K times the Mellin segment integral
z6anb   ML bound of each term
z6aerr  each term minus 2 pi i STERM is O ( K^-2 2^(-T/4) ) (z6mtail)
z6anchor
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_n.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp, lift
from z6a_e3 import conjs, build, unpack, c_
from z6a_mlib import mpval, cbvm
from z6b_m import inst_all
from z6b_r import dfacts
import lin
from lin import linarith
import num

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def segfacts(w, a, tr):
    """SA, SB e. CC , Re SA = 3 , SEG C_ CC"""
    st = mkst(w, a)
    three = c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')
    ntr = st([tr], 'renegcld', '-u T e. RR')
    ic = c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    sac = st([c_(w, a, w.s([], '3cn', '3 e. CC'), '3 e. CC'), st([ic, st([ntr], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % SA)
    sbc = st([c_(w, a, w.s([], '3cn', '3 e. CC'), '3 e. CC'), st([ic, st([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SB)
    ra = st([three, ntr], 'crred', '( Re ` %s ) = 3' % SA); rb = st([three, tr], 'crred', '( Re ` %s ) = 3' % SB)
    segcc = st([sac, sbc, w.inst('csegcl')], 'syl2anc', '%s C_ CC' % SEG)
    vre = st([sac, sbc, st([ra, rb], 'eqtr4d', '( Re ` %s ) = ( Re ` %s )' % (SA, SB)), w.inst('csegvre')], 'syl3anc', 'A. q e. %s ( Re ` q ) = ( Re ` %s )' % (SEG, SA))
    return dict(sac=sac, sbc=sbc, ra=ra, segcc=segcc, vre=vre, three=three)


def ptfacts(w, a, sf, vm, V):
    """( a -> Re V = 3 ) , V e. CC , V e. DG"""
    st = mkst(w, a)
    r0, _ = inst_all(w, a, sf['vre'], 'q', SEG, '( Re ` q ) = ( Re ` %s )' % SA, V, vm)
    rv = st([r0, sf['ra']], 'eqtrd', '( Re ` %s ) = 3' % V)
    vc = st([sf['segcc'], vm], 'sseldd', '%s e. CC' % V)
    rvr = st([vc], 'recld', '( Re ` %s ) e. RR' % V)
    m1 = linarith(w, a, [rv], '-u 1 < ( Re ` %s )' % V, leaves={'( Re ` %s )' % V: rvr})
    A0 = '( %s /\\ %s = 0 )' % (a, V); t0 = mkst(w, A0)
    r00 = t0([t0([t0([], 'simpr', '%s = 0' % V)], 'fveq2d', '( Re ` %s ) = ( Re ` 0 )' % V), c_(w, A0, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')], 'eqtrd',
             '( Re ` %s ) = 0' % V)
    rne = st([st([rv, c_(w, a, w.s([], '3ne0', '3 =/= 0'), '3 =/= 0')], 'eqnetrd', '( Re ` %s ) =/= 0' % V)], 'neneqd', '-. ( Re ` %s ) = 0' % V)
    nv = w.s([r00, lift(w, rne, A0)], 'pm2.65da', '( %s -> -. %s = 0 )' % (a, V))
    vn = st([nv], 'neqned', '%s =/= 0' % V)
    vdg = st([st([vc, st([m1, vn], 'jca', '( -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (V, V))], 'jca', '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ %s =/= 0 ) )' % (V, V, V)),
              w.inst('z6rdg')], 'syl', '%s e. %s' % (V, DG))
    return rv, vc, vdg


def z6anp():
    w = W('z6anp', 'The terms of the Mellin-expanded detector sum on the segment ` 3 - i T -- 3 + i T ` : its points have real part 3 and lie in the '
          'domain of Gamma; the value of the ` K ` -th term there and its majorant ` 32 R X ^ 3 K ^ -u 2 ` (Lean ` norm_Fterm_le ` ; ~ z6acoef , '
          '~ z6mg32 , ~ z6nx ).')
    a = ante('z6anp'); f = unpack(w, a); st = mkst(w, a)
    tr = st([f['T e. RR+']], 'rpred', 'T e. RR'); kn = f['K e. NN']; vm = f['V e. %s' % SEG]
    sf = segfacts(w, a, tr)
    rv, vc, vdg = ptfacts(w, a, sf, vm, 'V')
    d = dfacts(w, a, f)
    # the value
    FK = '( v e. %s |-> %s )' % (SEG, FBODY('K', 'v'))
    segv = st([], 'ovexd', '%s e. _V' % SEG)
    v1, _ = mpval(w, a, 'n', 'NN', '( v e. %s |-> %s )' % (SEG, FBODY('n', 'v')), 'K', kn, exs=st([segv], 'mptexd', '%s e. _V' % FK))
    v2 = st([v1], 'fveq1d', '( ( %s ` K ) ` V ) = ( %s ` V )' % (FNS, FK))
    v3, _ = mpval(w, a, 'v', SEG, FBODY('K', 'v'), 'V', vm)
    val = st([v2, v3], 'eqtrd', '( ( %s ` K ) ` V ) = %s' % (FNS, FBODY('K', 'V')))
    # the bound
    CN = CNK('K'); GV = '( _G ` V )'; YV = '( ( K / %s ) ^c -u V )' % XPD
    fa = {sub(HAB0, {'A': Z1D, 'B': Z2D}): d['hab'], 'R e. NN': f['R e. NN'], 'C : NN --> CC': f['C : NN --> CC'], CB: f[CB], 'S e. CC': f['S e. CC'],
          '0 <_ ( Re ` S )': f['0 <_ ( Re ` S )'], 'K e. NN': kn}
    b1, _ = applyn(w, a, 'z6acoef', {'A': Z1D, 'B': Z2D}, fa)
    cnc = st([b1, w.inst('z6absle')], 'syl', '%s e. CC' % CN)
    gc = st([vdg, w.inst('gamcl')], 'syl', '%s e. CC' % GV)
    kxr = st([st([kn], 'nnrpd', 'K e. RR+'), d['xrp']], 'rpdivcld', '( K / %s ) e. RR+' % XPD)
    nv = st([vc], 'negcld', '-u V e. CC')
    yvc = st([st([kxr], 'rpcnd', '( K / %s ) e. CC' % XPD), nv], 'cxpcld', '%s e. CC' % YV)
    G32 = st([vc, rv, w.inst('z6mg32')], 'syl2anc', '( abs ` %s ) <_ ( ; 3 2 x. %s )' % (GV, E4('( abs ` ( Im ` V ) )')))
    Y = '( abs ` ( Im ` V ) )'
    yr = st([st([st([vc], 'imcld', '( Im ` V ) e. RR')], 'recnd', '( Im ` V ) e. CC')], 'abscld', '%s e. RR' % Y)
    y0 = st([st([st([vc], 'imcld', '( Im ` V ) e. RR')], 'recnd', '( Im ` V ) e. CC')], 'absge0d', '0 <_ %s' % Y)
    ex = st([st([yr, c_(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'), c_(w, a, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')], 'redivcld', '( %s / 4 ) e. RR' % Y)], 'renegcld', '-u ( %s / 4 ) e. RR' % Y)
    e0 = linarith(w, a, [y0], '-u ( %s / 4 ) <_ 0' % Y, leaves={Y: yr})
    two = c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR')
    e41 = st([st([two, c_(w, a, w.s([], '1le2', '1 <_ 2'), '1 <_ 2'), ex, c_(w, a, w.s([], '0re', '0 e. RR'), '0 e. RR'), e0], 'cxplead', '%s <_ ( 2 ^c 0 )' % E4(Y)),
              st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), w.inst('cxp0')], 'syl', '( 2 ^c 0 ) = 1')], 'breqtrd', '%s <_ 1' % E4(Y))
    c32 = c_(w, a, num.real(w, '; 3 2'), '; 3 2 e. RR'); c320 = c_(w, a, num.fact(w, '; 3 2', 'ge0'), '0 <_ ; 3 2')
    e4r = st([st([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), ex], 'rpcxpcld', '%s e. RR+' % E4(Y))], 'rpred', '%s e. RR' % E4(Y))
    gr = st([gc], 'abscld', '( abs ` %s ) e. RR' % GV)
    m32 = st([e4r, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), c32, c320, e41], 'lemul2ad', '( ; 3 2 x. %s ) <_ ( ; 3 2 x. 1 )' % E4(Y))
    g1 = st([gr, st([c32, e4r], 'remulcld', '( ; 3 2 x. %s ) e. RR' % E4(Y)), st([c32, c_(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR')], 'remulcld', '( ; 3 2 x. 1 ) e. RR'), G32, m32],
            'letrd', '( abs ` %s ) <_ ( ; 3 2 x. 1 )' % GV)
    g2 = st([g1, st([st([c32], 'recnd', '; 3 2 e. CC')], 'mulridd', '( ; 3 2 x. 1 ) = ; 3 2')], 'breqtrd', '( abs ` %s ) <_ ; 3 2' % GV)
    Q = '( ( K / %s ) ^c -u 3 )' % XPD
    ay = st([st([kxr, nv, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( ( K / %s ) ^c ( Re ` -u V ) )' % (YV, XPD)),
             st([st([st([vc, w.inst('reneg')], 'syl', '( Re ` -u V ) = -u ( Re ` V )'), st([rv], 'negeqd', '-u ( Re ` V ) = -u 3')], 'eqtrd', '( Re ` -u V ) = -u 3')], 'oveq2d',
                '( ( K / %s ) ^c ( Re ` -u V ) ) = %s' % (XPD, Q))], 'eqtrd', '( abs ` %s ) = %s' % (YV, Q))
    qr = st([kxr, st([c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'renegcld', '-u 3 e. RR')], 'rpcxpcld', '%s e. RR+' % Q)
    GY_ = '( %s x. %s )' % (GV, YV)
    ab1 = st([cnc, st([gc, yvc], 'mulcld', '%s e. CC' % GY_)], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CN, GY_, CN, GY_))
    ab2 = st([gc, yvc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (GY_, GV, YV))
    ab2b = st([ab2, st([ay], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. %s )' % (GV, YV, GV, Q))], 'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) x. %s )' % (GY_, GV, Q))
    AB = st([ab1, st([ab2b], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. ( ( abs ` %s ) x. %s ) )' % (CN, GY_, CN, GV, Q))], 'eqtrd',
            '( abs ` %s ) = ( ( abs ` %s ) x. ( ( abs ` %s ) x. %s ) )' % (FBODY('K', 'V'), CN, GV, Q))
    qrr = st([qr], 'rpred', '%s e. RR' % Q); q0 = st([qr], 'rpge0d', '0 <_ %s' % Q)
    gq = st([gr, c32, qrr, qrr, st([gc], 'absge0d', '0 <_ ( abs ` %s )' % GV), q0, g2, st([qrr], 'leidd', '%s <_ %s' % (Q, Q))], 'lemul12ad',
            '( ( abs ` %s ) x. %s ) <_ ( ; 3 2 x. %s )' % (GV, Q, Q))
    kr = st([kn], 'nnred', 'K e. RR'); rr = st([f['R e. NN']], 'nnred', 'R e. RR')
    cnr = st([cnc], 'abscld', '( abs ` %s ) e. RR' % CN)
    krr = st([kr, rr], 'remulcld', '( K x. R ) e. RR')
    gqr = st([gr, qrr], 'remulcld', '( ( abs ` %s ) x. %s ) e. RR' % (GV, Q))
    b3 = st([cnr, krr, gqr, st([c32, qrr], 'remulcld', '( ; 3 2 x. %s ) e. RR' % Q), st([cnc], 'absge0d', '0 <_ ( abs ` %s )' % CN),
             st([gr, qrr, st([gc], 'absge0d', '0 <_ ( abs ` %s )' % GV), q0], 'mulge0d', '0 <_ ( ( abs ` %s ) x. %s )' % (GV, Q)), b1, gq], 'lemul12ad',
            '( ( abs ` %s ) x. ( ( abs ` %s ) x. %s ) ) <_ ( ( K x. R ) x. ( ; 3 2 x. %s ) )' % (CN, GV, Q, Q))
    old = lin.MAXDEG
    e1 = lin.lineq(w, a, '( ( K x. R ) x. ( ; 3 2 x. %s ) )' % Q, '( ( ; 3 2 x. R ) x. ( K x. %s ) )' % Q, leaves={'K': kr, 'R': rr, Q: qrr}, products=True)
    nx = st([st([kn], 'nnrpd', 'K e. RR+'), d['xrp'], w.inst('z6nx')], 'syl2anc', '( K x. %s ) = ( ( %s ^c 3 ) x. ( K ^c -u 2 ) )' % (Q, XPD))
    e2 = st([nx], 'oveq2d', '( ( ; 3 2 x. R ) x. ( K x. %s ) ) = ( ( ; 3 2 x. R ) x. ( ( %s ^c 3 ) x. ( K ^c -u 2 ) ) )' % (Q, XPD))
    c32r = st([c32, rr], 'remulcld', '( ; 3 2 x. R ) e. RR')
    x3c = st([st([st([d['xrp'], sf['three']], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)], 'recnd', '( %s ^c 3 ) e. CC' % XPD)
    k2c = st([st([kn], 'nncnd', 'K e. CC'), st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC')], 'negcld', '-u 2 e. CC')], 'cxpcld', '( K ^c -u 2 ) e. CC')
    e3 = st([st([st([c32r], 'recnd', '( ; 3 2 x. R ) e. CC'), x3c, k2c], 'mulassd', '( %s x. ( K ^c -u 2 ) ) = ( ( ; 3 2 x. R ) x. ( ( %s ^c 3 ) x. ( K ^c -u 2 ) ) )' % (K0A, XPD))],
            'eqcomd', '( ( ; 3 2 x. R ) x. ( ( %s ^c 3 ) x. ( K ^c -u 2 ) ) ) = ( %s x. ( K ^c -u 2 ) )' % (XPD, K0A))
    eqs = st([st([e1, e2], 'eqtrd', '( ( K x. R ) x. ( ; 3 2 x. %s ) ) = ( ( ; 3 2 x. R ) x. ( ( %s ^c 3 ) x. ( K ^c -u 2 ) ) )' % (Q, XPD)), e3], 'eqtrd',
             '( ( K x. R ) x. ( ; 3 2 x. %s ) ) = ( %s x. ( K ^c -u 2 ) )' % (Q, K0A))
    bnd = st([st([AB, b3], 'eqbrtrd', '( abs ` %s ) <_ ( ( K x. R ) x. ( ; 3 2 x. %s ) )' % (FBODY('K', 'V'), Q)), eqs], 'breqtrd',
             '( abs ` %s ) <_ ( %s x. ( K ^c -u 2 ) )' % (FBODY('K', 'V'), K0A))
    w.qed([st([rv, vdg], 'jca', '( ( Re ` V ) = 3 /\\ V e. %s )' % DG), st([val, bnd], 'jca', '( ( ( %s ` K ) ` V ) = %s /\\ ( abs ` %s ) <_ ( %s x. ( K ^c -u 2 ) ) )'
                                                                                % (FNS, FBODY('K', 'V'), FBODY('K', 'V'), K0A))], 'jca', STATEMENTS['z6anp'])
    return w


MN = '( n e. NN |-> ( %s x. ( n ^c -u 2 ) ) )' % K0A


def coefcc(w, a, f, d, K, kn):
    """( a -> CNK(K) e. CC ) and the z6acoef bound"""
    st = mkst(w, a)
    fa = {sub(HAB0, {'A': Z1D, 'B': Z2D}): d['hab'], 'R e. NN': f['R e. NN'], 'C : NN --> CC': f['C : NN --> CC'], CB: f[CB], 'S e. CC': f['S e. CC'],
          '0 <_ ( Re ` S )': f['0 <_ ( Re ` S )'], '%s e. NN' % K: kn}
    b1, _ = applyn(w, a, 'z6acoef', {'A': Z1D, 'B': Z2D, 'K': K}, fa)
    return st([b1, w.inst('z6absle')], 'syl', '%s e. CC' % CNK(K)), b1


def z6anl():
    w = W('z6anl', 'At every height ` T ` the ` n ` -series of the Mellin terms, integrated termwise along ` 3 - i T -- 3 + i T ` , converges to the '
          'segment integral of the anchor integrand ` G3 ( R ) ` (Lean ` integral_tsum_of_summable_integral_norm ` , ` tsum_Fterm ` ; ~ z6lsum with '
          'the majorant of ~ z6anp , ~ z5lser , ~ z6aterm ).')
    a = ante('z6anl'); f = unpack(w, a); st = mkst(w, a)
    trp = f['T e. RR+']; tr = st([trp], 'rpred', 'T e. RR')
    sf = segfacts(w, a, tr)
    d = dfacts(w, a, f)
    # SEG C_ DG
    au = '( %s /\\ u e. %s )' % (a, SEG)
    ru, uc, udg = ptfacts(w, au, LZ(w, sf, au), w.s([], 'simpr', '( %s -> u e. %s )' % (au, SEG)), 'u')
    sdg = st([w.s([udg], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (a, SEG, DG))], 'ssrdv', '%s C_ %s' % (SEG, DG))
    # FNS : NN --> ( SEG -cn-> CC )
    an = '( %s /\\ n e. NN )' % a; tn = mkst(w, an)
    nn = tn([], 'simpr', 'n e. NN')
    cnc, _ = coefcc(w, an, LZ(w, f, an), LZ(w, d, an), 'n', nn)
    segcc = lift(w, sf['segcc'], an); sdgn = lift(w, sdg, an)
    dgcc = c_(w, an, w.s([], 'difss', '%s C_ CC' % DG), '%s C_ CC' % DG)
    idm = tn([sdgn, dgcc, w.inst('cncfmptid')], 'syl2anc', '( v e. %s |-> v ) e. ( %s -cn-> %s )' % (SEG, SEG, DG))
    GZ = '( z e. %s |-> ( _G ` z ) )' % DG
    gam = c_(w, an, w.s([w.s([], 'z6gamhold', STATEMENTS['z6gamhold'])], 'simpli', '%s e. ( %s -cn-> CC )' % (GZ, DG)), '%s e. ( %s -cn-> CC )' % (GZ, DG))
    nf = w.s([], 'nfv', 'F/ v %s' % an)
    g1 = tn([nf, idm, gam, c_(w, an, w.s([], 'ssid', '%s C_ %s' % (DG, DG)), '%s C_ %s' % (DG, DG)), w.s([], 'fveq2', '( z = v -> ( _G ` z ) = ( _G ` v ) )')], 'cncfcompt2',
            '( v e. %s |-> ( _G ` v ) ) e. ( %s -cn-> CC )' % (SEG, SEG))
    Y = '( n / %s )' % XPD
    yrp = tn([tn([nn], 'nnrpd', 'n e. RR+'), lift(w, d['xrp'], an)], 'rpdivcld', '%s e. RR+' % Y)
    ccss = c_(w, an, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    NG = '( v e. %s |-> -u v )' % SEG
    ngc = w.s([w.s([], 'eqid', '%s = %s' % (NG, NG))], 'negcncf', '( %s C_ CC -> %s e. ( %s -cn-> CC ) )' % (SEG, NG, SEG))
    ng = w.s([segcc, ngc], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (an, NG, SEG))
    cx = tn([yrp, ccss, w.inst('cxfcn')], 'syl2anc', '( z e. CC |-> ( %s ^c z ) ) e. ( CC -cn-> CC )' % Y)
    g2 = tn([nf, ng, cx, ccss, w.s([], 'oveq2', '( z = -u v -> ( %s ^c z ) = ( %s ^c -u v ) )' % (Y, Y))], 'cncfcompt2',
            '( v e. %s |-> ( %s ^c -u v ) ) e. ( %s -cn-> CC )' % (SEG, Y, SEG))
    g12 = w.s([g1, g2], 'mulcncf', '( %s -> ( v e. %s |-> ( ( _G ` v ) x. ( %s ^c -u v ) ) ) e. ( %s -cn-> CC ) )' % (an, SEG, Y, SEG))
    cm = tn([cnc, segcc, ccss, w.inst('cncfmptc')], 'syl3anc', '( v e. %s |-> %s ) e. ( %s -cn-> CC )' % (SEG, CNK('n'), SEG))
    fcn = w.s([cm, g12], 'mulcncf', '( %s -> ( v e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (an, SEG, FBODY('n', 'v'), SEG))
    CNS = '( %s -cn-> CC )' % SEG
    ffn = st([fcn, w.s([], 'eqid', '%s = %s' % (FNS, FNS))], 'fmptd', '%s : NN --> %s' % (FNS, CNS))
    # the majorant sequence
    x3r = st([st([d['xrp'], sf['three']], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)
    rr = st([f['R e. NN']], 'nnred', 'R e. RR')
    k0r = st([st([c_(w, a, num.real(w, '; 3 2'), '; 3 2 e. RR'), rr], 'remulcld', '( ; 3 2 x. R ) e. RR'), x3r], 'remulcld', '%s e. RR' % K0A)
    n2 = tn([tn([nn], 'nnrpd', 'n e. RR+'), c_(w, an, w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR'), '-u 2 e. RR')], 'rpcxpcld',
            '( n ^c -u 2 ) e. RR+')
    mnr = tn([lift(w, k0r, an), tn([n2], 'rpred', '( n ^c -u 2 ) e. RR')], 'remulcld', '( %s x. ( n ^c -u 2 ) ) e. RR' % K0A)
    mf = st([mnr, w.s([], 'eqid', '%s = %s' % (MN, MN))], 'fmptd', '%s : NN --> RR' % MN)
    ZF = '( n e. NN |-> ( n ^c -u 2 ) )'
    ak = '( %s /\\ k e. NN )' % a; tk = mkst(w, ak)
    kn = tk([], 'simpr', 'k e. NN')
    zv, _ = mpval(w, ak, 'n', 'NN', '( n ^c -u 2 )', 'k', kn)
    re2 = c_(w, a, w.s([w.s([], '2re', '2 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 2 ) = 2'), '( Re ` 2 ) = 2')
    zc = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], '1lt2', '1 < 2'), '1 < 2'), re2], 'breqtrrd', '1 < ( Re ` 2 )'), zv], 'zetacvg', 'seq 1 ( + , %s ) e. dom ~~>' % ZF)
    ZFk = lambda k: '( %s ` %s )' % (ZF, k)
    k2rp = tk([tk([kn], 'nnrpd', 'k e. RR+'), c_(w, ak, w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR'), '-u 2 e. RR')], 'rpcxpcld', '( k ^c -u 2 ) e. RR+')
    zkre = tk([zv, tk([k2rp], 'rpred', '( k ^c -u 2 ) e. RR')], 'eqeltrd', '%s e. RR' % ZFk('k'))
    mv, _ = mpval(w, ak, 'n', 'NN', '( %s x. ( n ^c -u 2 ) )' % K0A, 'k', kn)
    mkc = tk([mv, tk([tk([lift(w, k0r, ak), tk([k2rp], 'rpred', '( k ^c -u 2 ) e. RR')], 'remulcld', '( %s x. ( k ^c -u 2 ) ) e. RR' % K0A)], 'recnd',
                     '( %s x. ( k ^c -u 2 ) ) e. CC' % K0A)], 'eqeltrd', '( %s ` k ) e. CC' % MN)
    rr0 = st([f['R e. NN']], 'nnrpd', 'R e. RR+')
    c32rp = c_(w, a, num.real(w, '; 3 2'), '; 3 2 e. RR')
    k0ge = st([st([c32rp, rr], 'remulcld', '( ; 3 2 x. R ) e. RR'), x3r, st([c32rp, rr, c_(w, a, num.fact(w, '; 3 2', 'ge0'), '0 <_ ; 3 2'), st([rr0], 'rpge0d', '0 <_ R')], 'mulge0d',
                                                                              '0 <_ ( ; 3 2 x. R )'), st([st([d['xrp'], sf['three']], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpge0d',
                                                                                                                '0 <_ ( %s ^c 3 )' % XPD)], 'mulge0d', '0 <_ %s' % K0A)
    amk = tk([tk([mv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` ( %s x. ( k ^c -u 2 ) ) )' % (MN, K0A)),
              tk([tk([lift(w, k0r, ak), tk([k2rp], 'rpred', '( k ^c -u 2 ) e. RR')], 'remulcld', '( %s x. ( k ^c -u 2 ) ) e. RR' % K0A),
                  tk([lift(w, k0r, ak), tk([k2rp], 'rpred', '( k ^c -u 2 ) e. RR'), lift(w, k0ge, ak), tk([k2rp], 'rpge0d', '0 <_ ( k ^c -u 2 )')], 'mulge0d',
                     '0 <_ ( %s x. ( k ^c -u 2 ) )' % K0A)], 'absidd', '( abs ` ( %s x. ( k ^c -u 2 ) ) ) = ( %s x. ( k ^c -u 2 ) )' % (K0A, K0A))], 'eqtrd',
             '( abs ` ( %s ` k ) ) = ( %s x. ( k ^c -u 2 ) )' % (MN, K0A))
    amk2 = tk([amk, tk([tk([zv], 'eqcomd', '( k ^c -u 2 ) = %s' % ZFk('k'))], 'oveq2d', '( %s x. ( k ^c -u 2 ) ) = ( %s x. %s )' % (K0A, K0A, ZFk('k')))], 'eqtrd',
              '( abs ` ( %s ` k ) ) = ( %s x. %s )' % (MN, K0A, ZFk('k')))
    ak1 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    kn1 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % ak1), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleq2i', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                       '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'syl', '( %s -> k e. NN )' % ak1)
    le_ = w.s([amk2], 'eqled', '( %s -> ( abs ` ( %s ` k ) ) <_ ( %s x. %s ) )' % (ak, MN, K0A, ZFk('k')))
    le_1 = w.s([w.s([w.s([le_], 'ex', '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( %s x. %s ) ) )' % (a, MN, K0A, ZFk('k')))], 'adantr',
                    '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( %s x. %s ) ) )' % (ak1, MN, K0A, ZFk('k'))), kn1], 'mpd',
               '( %s -> ( abs ` ( %s ` k ) ) <_ ( %s x. %s ) )' % (ak1, MN, K0A, ZFk('k')))
    mcv = st([c_(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN'), zkre, mkc, zc, k0r, le_1], 'cvgcmpce', 'seq 1 ( + , %s ) e. dom ~~>' % MN)
    # the bound for every j , y
    ajy = '( %s /\\ ( h e. NN /\\ y e. %s ) )' % (a, SEG); tj = mkst(w, ajy)
    fj = LZ(w, f, ajy)
    fj['T e. RR+'] = lift(w, trp, ajy); fj['h e. NN'] = tj([], 'simprl', 'h e. NN'); fj['y e. %s' % SEG] = tj([], 'simprr', 'y e. %s' % SEG)
    pj, pjc = applyn(w, ajy, 'z6anp', {'K': 'h', 'V': 'y'}, fj)
    pv = tj([pj], 'simprld', '( ( %s ` h ) ` y ) = %s' % (FNS, FBODY('h', 'y')))
    pb = tj([pj], 'simprrd', '( abs ` %s ) <_ ( %s x. ( h ^c -u 2 ) )' % (FBODY('h', 'y'), K0A))
    mj, _ = mpval(w, ajy, 'n', 'NN', '( %s x. ( n ^c -u 2 ) )' % K0A, 'h', fj['h e. NN'])
    bj = tj([tj([tj([pv], 'fveq2d', '( abs ` ( ( %s ` h ) ` y ) ) = ( abs ` %s )' % (FNS, FBODY('h', 'y'))), pb], 'eqbrtrd',
                '( abs ` ( ( %s ` h ) ` y ) ) <_ ( %s x. ( h ^c -u 2 ) )' % (FNS, K0A)), mj], 'breqtrrd', '( abs ` ( ( %s ` h ) ` y ) ) <_ ( %s ` h )' % (FNS, MN))
    MBND = 'A. h e. NN A. y e. %s ( abs ` ( ( %s ` h ) ` y ) ) <_ ( %s ` h )' % (SEG, FNS, MN)
    mb = st([bj], 'ralrimivva', MBND)
    fz = {'%s e. CC' % SA: sf['sac'], '%s e. CC' % SB: sf['sbc'], '( %s cseg %s ) C_ %s' % (SA, SB, SEG): st([], 'ssidd', '%s C_ %s' % (SEG, SEG)),
          '%s : NN --> %s' % (FNS, CNS): ffn, '%s : NN --> RR' % MN: mf, 'seq 1 ( + , %s ) e. dom ~~>' % MN: mcv, MBND: mb}
    ls, lsc = applyn(w, a, 'z6lsum', {'A': SA, 'B': SB, 'U': SEG, 'F': FNS, 'M': MN, 'j': 'h'}, fz)
    SUMM = '( z e. %s |-> sum_ k e. NN ( ( %s ` k ) ` z ) )' % (SEG, FNS)
    # linteq: SUMM and G3 agree on the segment
    cu = '( %s /\\ u e. ( %s cseg %s ) )' % (a, SA, SB); tu = mkst(w, cu)
    um = tu([], 'simpr', 'u e. %s' % SEG)
    fu = LZ(w, f, cu)
    du = LZ(w, d, cu)
    sfu = LZ(w, sf, cu)
    ru, uc, udg = ptfacts(w, cu, sfu, um, 'u')
    s1, _ = mpval(w, cu, 'z', SEG, 'sum_ k e. NN ( ( %s ` k ) ` z )' % FNS, 'u', um,
                  exs=w.s([w.s([], 'sumex', 'sum_ k e. NN ( ( %s ` k ) ` u ) e. _V' % FNS)], 'a1i', '( %s -> sum_ k e. NN ( ( %s ` k ) ` u ) e. _V )' % (cu, FNS)))
    # u e. HPT 2
    ur = tu([uc], 'recld', '( Re ` u ) e. RR')
    u2 = tu([tu([uc, linarith(w, cu, [ru], '2 < ( Re ` u )', leaves={'( Re ` u )': ur})], 'jca', '( u e. CC /\\ 2 < ( Re ` u ) )'),
             tu([c_(w, cu, w.s([], '2re', '2 e. RR'), '2 e. RR'), w.inst('elhp2')], 'syl', '( u e. %s <-> ( u e. CC /\\ 2 < ( Re ` u ) ) )' % HPT('2'))], 'mpbird', 'u e. %s' % HPT('2'))
    G3B = '( ( ( _G ` w ) x. ( %s ^c w ) ) x. ( sum_ k e. NN ( ( C ` k ) x. ( k ^c -u ( S + w ) ) ) x. %s ) )' % (XPD, MRr('R', '( S + w )'))
    g3v, g3val = mpval(w, cu, 'w', HPT('2'), G3B, 'u', u2)
    SU = '( S + u )'
    suc = tu([fu['S e. CC'], uc], 'addcld', '%s e. CC' % SU)
    rsu = tu([fu['S e. CC'], uc], 'readdd', '( Re ` %s ) = ( ( Re ` S ) + ( Re ` u ) )' % SU)
    rsr = tu([fu['S e. CC']], 'recld', '( Re ` S ) e. RR')
    g1u = tu([linarith(w, cu, [fu['0 <_ ( Re ` S )'], ru], '1 < ( ( Re ` S ) + ( Re ` u ) )', leaves={'( Re ` S )': rsr, '( Re ` u )': ur}), rsu], 'breqtrrd', '1 < ( Re ` %s )' % SU)
    fl = {sub(HAB0, {'A': Z1D, 'B': Z2D}): du['hab'], 'R e. NN': fu['R e. NN'], '( mmu ` R ) =/= 0': fu['( mmu ` R ) =/= 0'], CHR: fu[CHR], CB: fu[CB],
          '%s e. CC' % SU: suc, '1 < ( Re ` %s )' % SU: g1u}
    zl, zlc = applyn(w, cu, 'z5lser', {'A': Z1D, 'B': Z2D, 'S': SU}, fl)
    TN = lambda n: '( %s x. ( %s ^c -u %s ) )' % (COEFG(Z1D, Z2D, 'R', n), n, SU)
    TSEQ = '( n e. NN |-> %s )' % TN('n')
    zcv = tu([zl], 'simpld', 'seq 1 ( + , %s ) e. dom ~~>' % TSEQ)
    zeq = tu([zl], 'simprd', 'sum_ n e. NN %s = ( sum_ k e. NN ( ( C ` k ) x. ( k ^c -u %s ) ) x. %s )' % (TN('n'), SU, MRr('R', SU)))
    GX = '( ( _G ` u ) x. ( %s ^c u ) )' % XPD
    gxc = tu([tu([udg, w.inst('gamcl')], 'syl', '( _G ` u ) e. CC'), tu([tu([du['xrp']], 'rpcnd', '%s e. CC' % XPD), uc], 'cxpcld', '( %s ^c u ) e. CC' % XPD)],
             'mulcld', '%s e. CC' % GX)
    # the k-th term: value and CC-ness
    ck = '( %s /\\ k e. NN )' % cu; tk2 = mkst(w, ck)
    kk = tk2([], 'simpr', 'k e. NN')
    tvk, _ = mpval(w, ck, 'n', 'NN', TN('n'), 'k', kk)
    fck = LZ(w, fu, ck)
    cnk, _ = coefcc(w, ck, fck, LZ(w, du, ck), 'k', kk)
    bvk = tk2([tk2([lift(w, du['hab'], ck), kk], 'jca', '( %s /\\ k e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z5bvaabs')], 'syl',
              '( abs ` ( ( %s bvA %s ) ` k ) ) <_ k' % (Z1D, Z2D))
    COK = COEFG(Z1D, Z2D, 'R', 'k')
    bkc = tk2([bvk, w.inst('z6absle')], 'syl', '( ( %s bvA %s ) ` k ) e. CC' % (Z1D, Z2D))
    psk = tk2([tk2([fck['R e. NN'], kk, w.inst('z5psiabs')], 'syl2anc', '( abs ` ( ( mmu ` ( R gcd k ) ) x. ( phi ` ( R gcd k ) ) ) ) <_ R'), w.inst('z6absle')], 'syl',
              '( ( mmu ` ( R gcd k ) ) x. ( phi ` ( R gcd k ) ) ) e. CC')
    cck = tk2([fck['C : NN --> CC'], kk], 'ffvelcdmd', '( C ` k ) e. CC')
    coc = tk2([tk2([bkc, psk], 'mulcld', '( ( ( %s bvA %s ) ` k ) x. ( ( mmu ` ( R gcd k ) ) x. ( phi ` ( R gcd k ) ) ) ) e. CC' % (Z1D, Z2D)), cck], 'mulcld', '%s e. CC' % COK)
    kcxc = tk2([tk2([kk], 'nncnd', 'k e. CC'), tk2([lift(w, suc, ck)], 'negcld', '-u %s e. CC' % SU)], 'cxpcld', '( k ^c -u %s ) e. CC' % SU)
    tkc = tk2([coc, kcxc], 'mulcld', '%s e. CC' % TN('k'))
    tkc2 = tk2([tvk, tkc], 'eqeltrd', '( %s ` k ) e. CC' % TSEQ)
    # isummulc2
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    im = w.s([nnuz, c_(w, cu, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), tvk, tkc, zcv, gxc], 'isummulc2', '( %s -> ( %s x. sum_ k e. NN %s ) = sum_ k e. NN ( %s x. %s ) )'
             % (cu, GX, TN('k'), GX, TN('k')))
    idk = w.s([], 'id', '( n = k -> n = k )')
    sbn, _ = w.congr(TN('n'), {'n': 'k'}, 'n = k', {'n': idk})
    cbn = c_(w, cu, w.s([sbn], 'cbvsumv', 'sum_ n e. NN %s = sum_ k e. NN %s' % (TN('n'), TN('k'))), 'sum_ n e. NN %s = sum_ k e. NN %s' % (TN('n'), TN('k')))
    # term = FNS value
    fkp = LZ(w, fu, ck); fkp['T e. RR+'] = lift(w, trp, ck); fkp['K e. NN'] = kk; fkp['V e. %s' % SEG] = lift(w, um, ck)
    fkp['k e. NN'] = kk; fkp['u e. %s' % SEG] = lift(w, um, ck)
    pk, _ = applyn(w, ck, 'z6anp', {'K': 'k', 'V': 'u'}, fkp)
    pkv = tk2([pk], 'simprld', '( ( %s ` k ) ` u ) = %s' % (FNS, FBODY('k', 'u')))
    fat = {'k e. RR+': tk2([kk], 'nnrpd', 'k e. RR+'), '%s e. RR+' % XPD: lift(w, du['xrp'], ck), 'S e. CC': fck['S e. CC'], 'u e. CC': lift(w, uc, ck),
           '%s e. CC' % COK: coc, '( _G ` u ) e. CC': tk2([lift(w, udg, ck), w.inst('gamcl')], 'syl', '( _G ` u ) e. CC')}
    at, atc = applyn(w, ck, 'z6aterm', {'Y': 'k', 'X': XPD, 'W': 'u', 'A': COK, 'G': '( _G ` u )'}, fat)
    assert atc == '( ( ( _G ` u ) x. ( %s ^c u ) ) x. %s ) = %s' % (XPD, TN('k'), FBODY('k', 'u')), atc
    tq = tk2([at, tk2([pkv], 'eqcomd', '%s = ( ( %s ` k ) ` u )' % (FBODY('k', 'u'), FNS))], 'eqtrd', '( %s x. %s ) = ( ( %s ` k ) ` u )' % (GX, TN('k'), FNS))
    sq = tu([tq], 'sumeq2dv', 'sum_ k e. NN ( %s x. %s ) = sum_ k e. NN ( ( %s ` k ) ` u )' % (GX, TN('k'), FNS))
    # assemble: G3 ` u = SUMM ` u
    SK = 'sum_ k e. NN ( ( C ` k ) x. ( k ^c -u %s ) )' % SU
    e1 = tu([g3v, tu([tu([tu([zeq], 'eqcomd', '( %s x. %s ) = sum_ n e. NN %s' % (SK, MRr('R', SU), TN('n'))), cbn], 'eqtrd',
                        '( %s x. %s ) = sum_ k e. NN %s' % (SK, MRr('R', SU), TN('k')))], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. sum_ k e. NN %s )' % (GX, SK, MRr('R', SU), GX, TN('k')))],
            'eqtrd', '( %s ` u ) = ( %s x. sum_ k e. NN %s )' % (G3('R'), GX, TN('k')))
    e2 = tu([tu([e1, im], 'eqtrd', '( %s ` u ) = sum_ k e. NN ( %s x. %s )' % (G3('R'), GX, TN('k'))), sq], 'eqtrd', '( %s ` u ) = sum_ k e. NN ( ( %s ` k ) ` u )' % (G3('R'), FNS))
    e3 = tu([s1, e2], 'eqtr4d', '( %s ` u ) = ( %s ` u )' % (SUMM, G3('R')))
    ral = st([e3], 'ralrimiva', 'A. u e. ( %s cseg %s ) ( %s ` u ) = ( %s ` u )' % (SA, SB, SUMM, G3('R')))
    sv = st([sf['segcc'] if False else st([], 'ovexd', '%s e. _V' % SEG)], 'mptexd', '%s e. _V' % SUMM)
    hps = c_(w, a, w.s([w.s([], 'cnvimass', '%s C_ dom Re' % HPT('2')), w.s([w.s([], 'ref', 'Re : CC --> RR')], 'fdmi', 'dom Re = CC')], 'sseqtri', '%s C_ CC' % HPT('2')), '%s C_ CC' % HPT('2'))
    hpx = st([c_(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V'), hps], 'ssexd', '%s e. _V' % HPT('2'))
    g3e = st([hpx], 'mptexd', '%s e. _V' % G3('R'))
    le = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([sv, g3e], 'jca', '( %s e. _V /\\ %s e. _V )' % (SUMM, G3('R')))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (SA, SB, SUMM, G3('R'))), ral, w.inst('linteq')], 'syl2anc',
            '( %s lint <. %s , %s >. ) = %s' % (SUMM, SA, SB, LI(G3('R'), '3', 'T')))
    w.qed([ls, le], 'breqtrd', STATEMENTS['z6anl'])
    return w


def fcont(w, a, f, d, sf, K, kn):
    """( a -> ( v e. SEG |-> ( ( _G ` v ) x. ( ( K / X ) ^c -u v ) ) ) e. cn ) and ( a -> ( v e. SEG |-> FBODY(K,v) ) e. cn ), CN(K) e. CC"""
    st = mkst(w, a)
    au = '( %s /\\ u e. %s )' % (a, SEG)
    ru, uc, udg = ptfacts(w, au, LZ(w, sf, au), w.s([], 'simpr', '( %s -> u e. %s )' % (au, SEG)), 'u')
    sdg = st([w.s([udg], 'ex', '( %s -> ( u e. %s -> u e. %s ) )' % (a, SEG, DG))], 'ssrdv', '%s C_ %s' % (SEG, DG))
    cnc, cnb = coefcc(w, a, f, d, K, kn)
    segcc = sf['segcc']
    dgcc = c_(w, a, w.s([], 'difss', '%s C_ CC' % DG), '%s C_ CC' % DG)
    idm = st([sdg, dgcc, w.inst('cncfmptid')], 'syl2anc', '( v e. %s |-> v ) e. ( %s -cn-> %s )' % (SEG, SEG, DG))
    GZ = '( z e. %s |-> ( _G ` z ) )' % DG
    gam = c_(w, a, w.s([w.s([], 'z6gamhold', STATEMENTS['z6gamhold'])], 'simpli', '%s e. ( %s -cn-> CC )' % (GZ, DG)), '%s e. ( %s -cn-> CC )' % (GZ, DG))
    nf = w.s([], 'nfv', 'F/ v %s' % a)
    g1 = st([nf, idm, gam, c_(w, a, w.s([], 'ssid', '%s C_ %s' % (DG, DG)), '%s C_ %s' % (DG, DG)), w.s([], 'fveq2', '( z = v -> ( _G ` z ) = ( _G ` v ) )')], 'cncfcompt2',
            '( v e. %s |-> ( _G ` v ) ) e. ( %s -cn-> CC )' % (SEG, SEG))
    Y = '( %s / %s )' % (K, XPD)
    yrp = st([st([kn], 'nnrpd', '%s e. RR+' % K), d['xrp']], 'rpdivcld', '%s e. RR+' % Y)
    ccss = c_(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    NG = '( v e. %s |-> -u v )' % SEG
    ngc = w.s([w.s([], 'eqid', '%s = %s' % (NG, NG))], 'negcncf', '( %s C_ CC -> %s e. ( %s -cn-> CC ) )' % (SEG, NG, SEG))
    ng = w.s([segcc, ngc], 'syl', '( %s -> %s e. ( %s -cn-> CC ) )' % (a, NG, SEG))
    cx = st([yrp, ccss, w.inst('cxfcn')], 'syl2anc', '( z e. CC |-> ( %s ^c z ) ) e. ( CC -cn-> CC )' % Y)
    g2 = st([nf, ng, cx, ccss, w.s([], 'oveq2', '( z = -u v -> ( %s ^c z ) = ( %s ^c -u v ) )' % (Y, Y))], 'cncfcompt2',
            '( v e. %s |-> ( %s ^c -u v ) ) e. ( %s -cn-> CC )' % (SEG, Y, SEG))
    GK = '( v e. %s |-> ( ( _G ` v ) x. ( %s ^c -u v ) ) )' % (SEG, Y)
    g12 = w.s([g1, g2], 'mulcncf', '( %s -> %s e. ( %s -cn-> CC ) )' % (a, GK, SEG))
    cm = st([cnc, segcc, ccss, w.inst('cncfmptc')], 'syl3anc', '( v e. %s |-> %s ) e. ( %s -cn-> CC )' % (SEG, CNK(K), SEG))
    fcn = w.s([cm, g12], 'mulcncf', '( %s -> ( v e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (a, SEG, FBODY(K, 'v'), SEG))
    return dict(GK=GK, gk=g12, fcn=fcn, cnc=cnc, cnb=cnb, sdg=sdg)


def z6anv():
    w = W('z6anv', 'Each Mellin term integrates along the segment to ` c_K ` times the Mellin segment integral (Lean ` integral_Fterm ` before the limit; '
          '~ lintmulc2 , ~ linteq ).')
    a = ante('z6anv'); f = unpack(w, a); st = mkst(w, a)
    trp = f['T e. RR+']; tr = st([trp], 'rpred', 'T e. RR'); kn = f['K e. NN']
    sf = segfacts(w, a, tr); d = dfacts(w, a, f)
    fc = fcont(w, a, f, d, sf, 'K', kn)
    FK = '( v e. %s |-> %s )' % (SEG, FBODY('K', 'v'))
    v1, _ = mpval(w, a, 'n', 'NN', '( v e. %s |-> %s )' % (SEG, FBODY('n', 'v')), 'K', kn, exs=st([st([], 'ovexd', '%s e. _V' % SEG)], 'mptexd', '%s e. _V' % FK))
    FKs = '( %s ` K )' % FNS
    fkc = st([fc['fcn'], st([v1], 'eleq1d', '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (FKs, SEG, FK, SEG))], 'mpbird', '%s e. ( %s -cn-> CC )' % (FKs, SEG))
    az = '( %s /\\ z e. %s )' % (a, SEG); tz = mkst(w, az)
    zm = tz([], 'simpr', 'z e. %s' % SEG)
    e1 = tz([lift(w, v1, az)], 'fveq1d', '( %s ` z ) = ( %s ` z )' % (FKs, FK))
    e2, _ = mpval(w, az, 'v', SEG, FBODY('K', 'v'), 'z', zm)
    e3, _ = mpval(w, az, 'v', SEG, '( ( _G ` v ) x. ( ( K / %s ) ^c -u v ) )' % XPD, 'z', zm)
    GKz = '( %s ` z )' % fc['GK']
    e4 = tz([tz([e1, e2], 'eqtrd', '( %s ` z ) = %s' % (FKs, FBODY('K', 'z'))), tz([tz([e3], 'eqcomd', '( ( _G ` z ) x. ( ( K / %s ) ^c -u z ) ) = %s' % (XPD, GKz))], 'oveq2d',
                                                                                      '%s = ( %s x. %s )' % (FBODY('K', 'z'), CNK('K'), GKz))], 'eqtrd', '( %s ` z ) = ( %s x. %s )' % (FKs, CNK('K'), GKz))
    ral = st([e4], 'ralrimiva', 'A. z e. %s ( %s ` z ) = ( %s x. %s )' % (SEG, FKs, CNK('K'), GKz))
    segss = st([], 'ssidd', '%s C_ %s' % (SEG, SEG))
    lm = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([fkc, segss], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (FKs, SEG, SEG, SEG))],
                'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (SA, SB, FKs, SEG, SEG, SEG)),
             st([fc['gk'], fc['cnc']], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s e. CC )' % (fc['GK'], SEG, CNK('K'))), ral, w.inst('lintmulc2')], 'syl3anc',
            '%s = ( %s x. ( %s lint <. %s , %s >. ) )' % (LFK, CNK('K'), fc['GK'], SA, SB))
    # linteq: GK = GY ( K / X ) on the segment
    GYK = GY('( K / %s )' % XPD)
    au = '( %s /\\ z e. ( %s cseg %s ) )' % (a, SA, SB); tu = mkst(w, au)
    um = tu([], 'simpr', 'z e. %s' % SEG)
    udg = tu([lift(w, fc['sdg'], au), um], 'sseldd', 'z e. %s' % DG)
    g1, _ = mpval(w, au, 'v', SEG, '( ( _G ` v ) x. ( ( K / %s ) ^c -u v ) )' % XPD, 'z', um)
    g2, _ = mpval(w, au, 'w', DG, '( ( _G ` w ) x. ( ( K / %s ) ^c -u w ) )' % XPD, 'z', udg)
    geq = tu([g1, g2], 'eqtr4d', '( %s ` z ) = ( %s ` z )' % (fc['GK'], GYK))
    ral2 = st([geq], 'ralrimiva', 'A. z e. ( %s cseg %s ) ( %s ` z ) = ( %s ` z )' % (SA, SB, fc['GK'], GYK))
    gkv = st([st([], 'ovexd', '%s e. _V' % SEG)], 'mptexd', '%s e. _V' % fc['GK'])
    cnex = c_(w, a, w.s([], 'cnex', 'CC e. _V'), 'CC e. _V')
    dgv = st([cnex, c_(w, a, w.s([], 'difss', '%s C_ CC' % DG), '%s C_ CC' % DG)], 'ssexd', '%s e. _V' % DG)
    gyv = st([dgv], 'mptexd', '%s e. _V' % GYK)
    le = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([gkv, gyv], 'jca', '( %s e. _V /\\ %s e. _V )' % (fc['GK'], GYK))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (SA, SB, fc['GK'], GYK)), ral2, w.inst('linteq')], 'syl2anc',
            '( %s lint <. %s , %s >. ) = %s' % (fc['GK'], SA, SB, LI(GYK, '3', 'T')))
    w.qed([lm, st([le], 'oveq2d', '( %s x. ( %s lint <. %s , %s >. ) ) = ( %s x. %s )' % (CNK('K'), fc['GK'], SA, SB, CNK('K'), LI(GYK, '3', 'T')))], 'eqtrd', STATEMENTS['z6anv'])
    return w


def z6anb():
    w = W('z6anb', 'The ML bound of one Mellin term along the segment (~ lintabs with ~ z6anp ; the segment has length ` 2 T ` ).')
    a = ante('z6anb'); f = unpack(w, a); st = mkst(w, a)
    trp = f['T e. RR+']; tr = st([trp], 'rpred', 'T e. RR'); kn = f['K e. NN']
    sf = segfacts(w, a, tr); d = dfacts(w, a, f)
    fc = fcont(w, a, f, d, sf, 'K', kn)
    FK = '( v e. %s |-> %s )' % (SEG, FBODY('K', 'v'))
    v1, _ = mpval(w, a, 'n', 'NN', '( v e. %s |-> %s )' % (SEG, FBODY('n', 'v')), 'K', kn, exs=st([st([], 'ovexd', '%s e. _V' % SEG)], 'mptexd', '%s e. _V' % FK))
    FKs = '( %s ` K )' % FNS
    fkc = st([fc['fcn'], st([v1], 'eleq1d', '( %s e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (FKs, SEG, FK, SEG))], 'mpbird', '%s e. ( %s -cn-> CC )' % (FKs, SEG))
    az = '( %s /\\ z e. ( %s cseg %s ) )' % (a, SA, SB); tz = mkst(w, az)
    fz = LZ(w, f, az); fz['z e. %s' % SEG] = tz([], 'simpr', 'z e. %s' % SEG)
    pz, _ = applyn(w, az, 'z6anp', {'V': 'z'}, fz)
    M_ = '( %s x. ( K ^c -u 2 ) )' % K0A
    bz = tz([tz([tz([pz], 'simprld', '( %s ` z ) = %s' % (FKs, FBODY('K', 'z')))], 'fveq2d', '( abs ` ( %s ` z ) ) = ( abs ` %s )' % (FKs, FBODY('K', 'z'))),
             tz([pz], 'simprrd', '( abs ` %s ) <_ %s' % (FBODY('K', 'z'), M_))], 'eqbrtrd', '( abs ` ( %s ` z ) ) <_ %s' % (FKs, M_))
    ral = st([bz], 'ralrimiva', 'A. z e. ( %s cseg %s ) ( abs ` ( %s ` z ) ) <_ %s' % (SA, SB, FKs, M_))
    x3r = st([st([d['xrp'], sf['three']], 'rpcxpcld', '( %s ^c 3 ) e. RR+' % XPD)], 'rpred', '( %s ^c 3 ) e. RR' % XPD)
    rr = st([f['R e. NN']], 'nnred', 'R e. RR')
    k0r = st([st([c_(w, a, num.real(w, '; 3 2'), '; 3 2 e. RR'), rr], 'remulcld', '( ; 3 2 x. R ) e. RR'), x3r], 'remulcld', '%s e. RR' % K0A)
    k2 = st([st([kn], 'nnrpd', 'K e. RR+'), c_(w, a, w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR'), '-u 2 e. RR')], 'rpcxpcld', '( K ^c -u 2 ) e. RR+')
    mr = st([k0r, st([k2], 'rpred', '( K ^c -u 2 ) e. RR')], 'remulcld', '%s e. RR' % M_)
    la = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([fkc, st([], 'ssidd', '%s C_ %s' % (SEG, SEG))], 'jca',
                                                                                                     '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (FKs, SEG, SEG, SEG))],
                'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (SA, SB, FKs, SEG, SEG, SEG)), mr, ral, w.inst('lintabs')], 'syl3anc',
            '( abs ` %s ) <_ ( %s x. ( abs ` ( %s - %s ) ) )' % (LFK, M_, SB, SA))
    sl = st([c_(w, a, w.s([], '3cn', '3 e. CC'), '3 e. CC'), st([tr], 'recnd', 'T e. CC'), c_(w, a, w.s([], '0cn', '0 e. CC'), '0 e. CC'), w.inst('z6segl')], 'syl3anc',
            '( ( %s + ( 0 x. ( %s - %s ) ) ) = ( 3 + ( _i x. ( -u T + ( 0 x. ( T - -u T ) ) ) ) ) /\\ ( %s - %s ) = ( _i x. ( T - -u T ) ) )' % (SA, SB, SA, SB, SA))
    df = st([sl], 'simprd', '( %s - %s ) = ( _i x. ( T - -u T ) )' % (SB, SA))
    tt = linarith(w, a, [], '( T - -u T ) <_ ( 2 x. T )', leaves={'T': tr})
    tt2 = linarith(w, a, [], '( 2 x. T ) <_ ( T - -u T )', leaves={'T': tr})
    teq = lin.lineq(w, a, '( T - -u T )', '( 2 x. T )', leaves={'T': tr})
    t2r = st([c_(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), tr], 'remulcld', '( 2 x. T ) e. RR')
    t20 = linarith(w, a, [st([trp], 'rpge0d', '0 <_ T')], '0 <_ ( 2 x. T )', leaves={'T': tr})
    ic = c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    ab = st([st([df], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( _i x. ( T - -u T ) ) )' % (SB, SA)),
             st([st([ic, st([st([tr, st([tr], 'renegcld', '-u T e. RR')], 'resubcld', '( T - -u T ) e. RR')], 'recnd', '( T - -u T ) e. CC')], 'absmuld',
                    '( abs ` ( _i x. ( T - -u T ) ) ) = ( ( abs ` _i ) x. ( abs ` ( T - -u T ) ) )'),
                 st([c_(w, a, w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1'), st([st([teq], 'fveq2d', '( abs ` ( T - -u T ) ) = ( abs ` ( 2 x. T ) )'),
                                                                                           st([t2r, t20], 'absidd', '( abs ` ( 2 x. T ) ) = ( 2 x. T )')], 'eqtrd',
                                                                                          '( abs ` ( T - -u T ) ) = ( 2 x. T )')], 'oveq12d',
                    '( ( abs ` _i ) x. ( abs ` ( T - -u T ) ) ) = ( 1 x. ( 2 x. T ) )')], 'eqtrd', '( abs ` ( _i x. ( T - -u T ) ) ) = ( 1 x. ( 2 x. T ) )')], 'eqtrd',
            '( abs ` ( %s - %s ) ) = ( 1 x. ( 2 x. T ) )' % (SB, SA))
    ab2 = st([ab, st([st([t2r], 'recnd', '( 2 x. T ) e. CC')], 'mullidd', '( 1 x. ( 2 x. T ) ) = ( 2 x. T )')], 'eqtrd', '( abs ` ( %s - %s ) ) = ( 2 x. T )' % (SB, SA))
    w.qed([la, st([ab2], 'oveq2d', '( %s x. ( abs ` ( %s - %s ) ) ) = ( %s x. ( 2 x. T ) )' % (M_, SB, SA, M_))], 'breqtrd', STATEMENTS['z6anb'])
    return w


def z6aerr():
    w = W('z6aerr', 'Each Mellin term minus ` 2 pi i ` times the detector summand is ` O ( K ^ -u 2 2 ^ ( - T / 4 ) ) ` (the quantitative Mellin identity '
          '~ z6mtail at ` Y = K / X ` , ~ z6anv , ~ z6acoef , ~ z6nx ).')
    a = ante('z6aerr'); f = unpack(w, a); st = mkst(w, a)
    trp = f['T e. RR+']; tr = st([trp], 'rpred', 'T e. RR'); kn = f['K e. NN']
    sf = segfacts(w, a, tr); d = dfacts(w, a, f)
    fc = fcont(w, a, f, d, sf, 'K', kn)
    Y = '( K / %s )' % XPD
    yrp = st([st([kn], 'nnrpd', 'K e. RR+'), d['xrp']], 'rpdivcld', '%s e. RR+' % Y)
    GYK = GY(Y); LIK = LI(GYK, '3', 'T')
    anv, _ = applyn(w, a, 'z6anv', {}, f)
    mt = st([yrp, trp, w.inst('z6mtail')], 'syl2anc', '( abs ` ( %s - ( %s x. ( exp ` -u %s ) ) ) ) <_ ( ( %s ^c -u 3 ) x. ( ( ; ; 2 5 6 / ( log ` 2 ) ) x. %s ) )'
            % (LIK, TPI, Y, Y, E4('T')))
    gyh = st([yrp, w.inst('z6gyhol')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (GYK, DG, DG, GYK))
    lic = st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([st([gyh], 'simpld', '%s e. ( %s -cn-> CC )' % (GYK, DG)), fc['sdg']], 'jca',
                                                                                         '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GYK, DG, SEG, DG)), w.inst('lintcl')],
             'syl2anc', '%s e. CC' % LIK)
    t = TPI; e = '( exp ` -u %s )' % Y; k = '( K ^c -u S )'; c = COEFG(Z1D, Z2D, 'R', 'K')
    tc = st([c_(w, a, w.s([], '2cn', '2 e. CC'), '2 e. CC'), st([c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c_(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')],
                                                                  'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % t)
    ec = st([st([st([yrp], 'rpcnd', '%s e. CC' % Y)], 'negcld', '-u %s e. CC' % Y)], 'efcld', '%s e. CC' % e)
    kc = st([st([kn], 'nncnd', 'K e. CC'), st([f['S e. CC']], 'negcld', '-u S e. CC')], 'cxpcld', '%s e. CC' % k)
    # c e. CC
    cnb = fc['cnb']
    bvk = st([st([d['hab'], kn], 'jca', '( %s /\\ K e. NN )' % sub(HAB0, {'A': Z1D, 'B': Z2D})), w.inst('z5bvaabs')], 'syl', '( abs ` ( ( %s bvA %s ) ` K ) ) <_ K' % (Z1D, Z2D))
    bkc = st([bvk, w.inst('z6absle')], 'syl', '( ( %s bvA %s ) ` K ) e. CC' % (Z1D, Z2D))
    psk = st([st([f['R e. NN'], kn, w.inst('z5psiabs')], 'syl2anc', '( abs ` ( ( mmu ` ( R gcd K ) ) x. ( phi ` ( R gcd K ) ) ) ) <_ R'), w.inst('z6absle')], 'syl',
             '( ( mmu ` ( R gcd K ) ) x. ( phi ` ( R gcd K ) ) ) e. CC')
    cck = st([f['C : NN --> CC'], kn], 'ffvelcdmd', '( C ` K ) e. CC')
    cc = st([st([bkc, psk], 'mulcld', '( ( ( %s bvA %s ) ` K ) x. ( ( mmu ` ( R gcd K ) ) x. ( phi ` ( R gcd K ) ) ) ) e. CC' % (Z1D, Z2D)), cck], 'mulcld', '%s e. CC' % c)
    # 2 pi i STERM = CN ( 2 pi i e )
    ST = STERM('R', 'K')
    en = st([st([st([kn], 'nncnd', 'K e. CC'), st([d['xrp']], 'rpcnd', '%s e. CC' % XPD), st([d['xrp']], 'rpne0d', '%s =/= 0' % XPD)], 'divnegd',
                '-u %s = ( -u K / %s )' % (Y, XPD))], 'eqcomd', '( -u K / %s ) = -u %s' % (XPD, Y))
    s1 = st([st([st([en], 'fveq2d', '( exp ` ( -u K / %s ) ) = %s' % (XPD, e))], 'oveq1d', '( ( exp ` ( -u K / %s ) ) x. %s ) = ( %s x. %s )' % (XPD, k, e, k))], 'oveq2d',
            '%s = ( %s x. ( %s x. %s ) )' % (ST, c, e, k))
    s2 = st([s1], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (t, ST, t, c, e, k))
    ekc = st([ec, kc], 'mulcld', '( %s x. %s ) e. CC' % (e, k))
    s3 = st([tc, cc, ekc], 'mul12d', '( %s x. ( %s x. ( %s x. %s ) ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (t, c, e, k, c, t, e, k))
    s4 = st([st([tc, ec, kc], 'mulassd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (t, e, k, t, e, k))], 'eqcomd', '( %s x. ( %s x. %s ) ) = ( ( %s x. %s ) x. %s )' % (t, e, k, t, e, k))
    tec = st([tc, ec], 'mulcld', '( %s x. %s ) e. CC' % (t, e))
    s5 = st([tec, kc], 'mulcomd', '( ( %s x. %s ) x. %s ) = ( %s x. ( %s x. %s ) )' % (t, e, k, k, t, e))
    s6 = st([st([cc, kc, tec], 'mulassd', '( ( %s x. %s ) x. ( %s x. %s ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (c, k, t, e, c, k, t, e))], 'eqcomd',
            '( %s x. ( %s x. ( %s x. %s ) ) ) = ( ( %s x. %s ) x. ( %s x. %s ) )' % (c, k, t, e, c, k, t, e))
    CN = CNK('K')
    tst = st([st([st([s2, s3], 'eqtrd', '( %s x. %s ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (t, ST, c, t, e, k)),
                  st([st([s4, s5], 'eqtrd', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (t, e, k, k, t, e))], 'oveq2d',
                     '( %s x. ( %s x. ( %s x. %s ) ) ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (c, t, e, k, c, k, t, e))], 'eqtrd',
                 '( %s x. %s ) = ( %s x. ( %s x. ( %s x. %s ) ) )' % (t, ST, c, k, t, e)), s6], 'eqtrd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (t, ST, CN, t, e))
    DF = '( %s - ( %s x. %s ) )' % (LIK, t, e)
    cnc = fc['cnc']
    dfe = st([st([anv, tst], 'oveq12d', '( %s - ( %s x. %s ) ) = ( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) )' % (LFK, t, ST, CN, LIK, CN, t, e)),
              st([st([cnc, lic, tec], 'subdid', '( %s x. %s ) = ( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) )' % (CN, DF, CN, LIK, CN, t, e))], 'eqcomd',
                 '( ( %s x. %s ) - ( %s x. ( %s x. %s ) ) ) = ( %s x. %s )' % (CN, LIK, CN, t, e, CN, DF))], 'eqtrd', '( %s - ( %s x. %s ) ) = ( %s x. %s )' % (LFK, t, ST, CN, DF))
    dfc = st([lic, tec], 'subcld', '%s e. CC' % DF)
    ab = st([st([dfe], 'fveq2d', '( abs ` ( %s - ( %s x. %s ) ) ) = ( abs ` ( %s x. %s ) )' % (LFK, t, ST, CN, DF)), st([cnc, dfc], 'absmuld',
                                                                                                                 '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (CN, DF, CN, DF))],
            'eqtrd', '( abs ` ( %s - ( %s x. %s ) ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (LFK, t, ST, CN, DF))
    Q = '( %s ^c -u 3 )' % Y; C2 = '( ; ; 2 5 6 / ( log ` 2 ) )'; E_ = E4('T')
    kr = st([kn], 'nnred', 'K e. RR'); rr = st([f['R e. NN']], 'nnred', 'R e. RR')
    qr = st([st([yrp, st([c_(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR')], 'renegcld', '-u 3 e. RR')], 'rpcxpcld', '%s e. RR+' % Q)], 'rpred', '%s e. RR' % Q)
    l2r = st([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+')], 'relogcld', '( log ` 2 ) e. RR')
    l2p = linarith(w, a, [c_(w, a, w.s([], 'z5dlog2', '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )'), '( ; 5 6 / ; 8 1 ) <_ ( log ` 2 )')], '0 < ( log ` 2 )', leaves={'( log ` 2 )': l2r})
    c2r = st([c_(w, a, num.real(w, '; ; 2 5 6'), '; ; 2 5 6 e. RR'), l2r, st([l2p], 'gt0ne0d', '( log ` 2 ) =/= 0')], 'redivcld', '%s e. RR' % C2)
    er = st([st([c_(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([st([tr, c_(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'), c_(w, a, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                         'redivcld', '( T / 4 ) e. RR')], 'renegcld', '-u ( T / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E_)], 'rpred', '%s e. RR' % E_)
    cnr = st([cnc], 'abscld', '( abs ` %s ) e. RR' % CN); dfr = st([dfc], 'abscld', '( abs ` %s ) e. RR' % DF)
    krr = st([kr, rr], 'remulcld', '( K x. R ) e. RR')
    ce = st([c2r, er], 'remulcld', '( %s x. %s ) e. RR' % (C2, E_))
    qce = st([qr, ce], 'remulcld', '( %s x. ( %s x. %s ) ) e. RR' % (Q, C2, E_))
    b = st([cnr, krr, dfr, qce, st([cnc], 'absge0d', '0 <_ ( abs ` %s )' % CN), st([dfc], 'absge0d', '0 <_ ( abs ` %s )' % DF), cnb, mt], 'lemul12ad',
           '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( K x. R ) x. ( %s x. ( %s x. %s ) ) )' % (CN, DF, Q, C2, E_))
    old = lin.MAXDEG; lin.MAXDEG = 6
    L = {'K': kr, 'R': rr, Q: qr, C2: c2r, E_: er}
    q1 = lin.lineq(w, a, '( ( K x. R ) x. ( %s x. ( %s x. %s ) ) )' % (Q, C2, E_), '( ( ( R x. %s ) x. %s ) x. ( K x. %s ) )' % (C2, E_, Q), leaves=L, products=True)
    nx = st([st([kn], 'nnrpd', 'K e. RR+'), d['xrp'], w.inst('z6nx')], 'syl2anc', '( K x. %s ) = ( ( %s ^c 3 ) x. ( K ^c -u 2 ) )' % (Q, XPD))
    X3 = '( %s ^c 3 )' % XPD; K2 = '( K ^c -u 2 )'
    q2 = st([nx], 'oveq2d', '( ( ( R x. %s ) x. %s ) x. ( K x. %s ) ) = ( ( ( R x. %s ) x. %s ) x. ( %s x. %s ) )' % (C2, E_, Q, C2, E_, X3, K2))
    x3r = st([st([d['xrp'], sf['three']], 'rpcxpcld', '%s e. RR+' % X3)], 'rpred', '%s e. RR' % X3)
    k2r = st([st([st([kn], 'nnrpd', 'K e. RR+'), c_(w, a, w.s([w.s([], '2re', '2 e. RR')], 'renegcli', '-u 2 e. RR'), '-u 2 e. RR')], 'rpcxpcld', '%s e. RR+' % K2)], 'rpred', '%s e. RR' % K2)
    L2 = {'R': rr, C2: c2r, E_: er, X3: x3r, K2: k2r}
    q3 = lin.lineq(w, a, '( ( ( R x. %s ) x. %s ) x. ( %s x. %s ) )' % (C2, E_, X3, K2), '( ( %s x. %s ) x. %s )' % (K1A, E_, K2), leaves=L2, products=True)
    lin.MAXDEG = old
    eqq = st([st([q1, q2], 'eqtrd', '( ( K x. R ) x. ( %s x. ( %s x. %s ) ) ) = ( ( ( R x. %s ) x. %s ) x. ( %s x. %s ) )' % (Q, C2, E_, C2, E_, X3, K2)), q3], 'eqtrd',
             '( ( K x. R ) x. ( %s x. ( %s x. %s ) ) ) = ( ( %s x. %s ) x. %s )' % (Q, C2, E_, K1A, E_, K2))
    w.qed([ab, st([b, eqq], 'breqtrd', '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( %s x. %s ) x. %s )' % (CN, DF, K1A, E_, K2))], 'eqbrtrd', STATEMENTS['z6aerr'])
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6anp, z6anl, z6anv, z6anb, z6aerr]:
        if want(fn.__name__):
            if not run(fn()):
                break
