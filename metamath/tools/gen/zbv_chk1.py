"""Sortie ZBV, BVL2 section 3.2: RZA Lemma 3.1 at sigma = 1, q = 1 (abs_mCheck1_le).

HK(n) = sum_ m e. ( 1 ... ( |_ ` ( ( |_ ` X ) / n ) ) ) ( 1 / m ),  LG(n) = ( log ` ( X / n ) ),
RHO(n) = ( HK(n) - ( LG(n) + gamma ) ),  MQ(n) = ( ( mmu ` n ) / n )

bvmchk1lem1 ( ( HX /\\ K e. RX ) -> ( abs ` ( MQ(K) x. RHO(K) ) ) <_ ( 1 / X ) )
bvmchk1lem2 ( HX -> ( abs ` sum_ n e. RX ( MQ(n) x. RHO(n) ) ) <_ 1 )
bvmchk1lem3 ( HX -> 1 = ( MC + ( ( gamma x. MH ) + R ) ) )
bvmchk1     ( HX -> ( abs ` sum_ n e. RX ( MQ(n) x. LG(n) ) ) <_ ( ; 1 1 / 3 ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbvlib import *
from lin import linarith
from zbv_core import MU, FL, mufacts, HX, NX, RX, xfacts

HK = lambda n: 'sum_ m e. ( 1 ... %s ) ( 1 / m )' % FL('( %s / %s )' % (NX, n))
LG = lambda n: '( log ` ( X / %s ) )' % n
RHO = lambda n: '( %s - ( %s + gamma ) )' % (HK(n), LG(n))
MQ = lambda n: '( %s / %s )' % (MU(n), n)
MC = 'sum_ n e. %s ( %s x. %s )' % (RX, MQ('n'), LG('n'))
MH = 'sum_ n e. %s %s' % (RX, MQ('n'))
RS = 'sum_ n e. %s ( %s x. %s )' % (RX, MQ('n'), RHO('n'))
GM = '( gamma x. %s )' % MH


def kfacts(w, ante, kel, xr, xrp, k):
    """closures for one index k e. RX under ante: returns dict"""
    st = mkst(w, ante)
    knn = sy(w, ante, kel, 'elfznn', '%s e. NN' % k)
    krp = st([knn], 'nnrpd', '%s e. RR+' % k)
    kre = st([krp], 'rpred', '%s e. RR' % k); kcc = st([krp], 'rpcnd', '%s e. CC' % k); kne = st([krp], 'rpne0d', '%s =/= 0' % k)
    muz, mur, muc = mufacts(w, ante, knn, k)
    mqr = st([mur, krp], 'rerpdivcld', '%s e. RR' % MQ(k)); mqc = st([mqr], 'recnd', '%s e. CC' % MQ(k))
    Q = '( X / %s )' % k
    qrp = st([xrp, krp], 'rpdivcld', '%s e. RR+' % Q)
    lgr = st([qrp], 'relogcld', '%s e. RR' % LG(k))
    AM = '( %s /\\ m e. ( 1 ... %s ) )' % (ante, FL('( %s / %s )' % (NX, k)))
    sm = mkst(w, AM)
    mnn = sy(w, AM, sm([], 'simpr', 'm e. ( 1 ... %s )' % FL('( %s / %s )' % (NX, k))), 'elfznn', 'm e. NN')
    hkr = st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % FL('( %s / %s )' % (NX, k))), sm([mnn], 'nnrecred', '( 1 / m ) e. RR')], 'fsumrecl', '%s e. RR' % HK(k))
    gr = st([clo(w, 'emre', 'gamma e. RR')], 'a1i', 'gamma e. RR')
    lgg = st([lgr, gr], 'readdcld', '( %s + gamma ) e. RR' % LG(k))
    rhor = st([hkr, lgg], 'resubcld', '%s e. RR' % RHO(k)); rhoc = st([rhor], 'recnd', '%s e. CC' % RHO(k))
    return dict(nn=knn, rp=krp, re=kre, cc=kcc, ne=kne, muz=muz, mur=mur, muc=muc, mqr=mqr, mqc=mqc, Q=Q, qrp=qrp, lgr=lgr,
                hkr=hkr, gr=gr, lgg=lgg, rhor=rhor, rhoc=rhoc)


def bvmchk1lem1():
    w = W('bvmchk1lem1', 'One term of the remainder in RZA Lemma 3.1 at sigma = 1: '
                         '| ( mmu K / K ) ( H - log ( X / K ) - gamma ) | <= 1 / X (harmonicbnd4).')
    A = '( %s /\\ K e. %s )' % (HX, RX)
    st = mkst(w, A)
    hx = st([], 'simpl', HX)
    xr = st([hx], 'simpld', 'X e. RR'); x1 = st([hx], 'simprd', '1 <_ X')
    xrp = st([xr, linarith(w, A, [x1], '0 < X', leaves={'X': xr})], 'elrpd', 'X e. RR+')
    kel = st([], 'simpr', 'K e. %s' % RX)
    f = kfacts(w, A, kel, xr, xrp, 'K')
    Q = f['Q']
    hb = sy(w, A, f['qrp'], 'harmonicbnd4', '( abs ` ( sum_ m e. ( 1 ... %s ) ( 1 / m ) - ( ( log ` %s ) + gamma ) ) ) <_ ( 1 / %s )' % (FL(Q), Q, Q))
    fld = sy2(w, A, xr, f['nn'], 'fldiv', '%s = %s' % (FL('( %s / K )' % NX), FL(Q)))
    hkeq = st([st([fld], 'oveq2d', '( 1 ... %s ) = ( 1 ... %s )' % (FL('( %s / K )' % NX), FL(Q)))], 'sumeq1d', '%s = sum_ m e. ( 1 ... %s ) ( 1 / m )' % (HK('K'), FL(Q)))
    rhoeq = st([hkeq], 'oveq1d', '%s = ( sum_ m e. ( 1 ... %s ) ( 1 / m ) - ( ( log ` %s ) + gamma ) )' % (RHO('K'), FL(Q), Q))
    rhole = st([st([rhoeq], 'fveq2d', '( abs ` %s ) = ( abs ` ( sum_ m e. ( 1 ... %s ) ( 1 / m ) - ( ( log ` %s ) + gamma ) ) )' % (RHO('K'), FL(Q), Q)), hb], 'eqbrtrd',
               '( abs ` %s ) <_ ( 1 / %s )' % (RHO('K'), Q))
    rec = st([st([xrp], 'rpcnd', 'X e. CC'), f['cc'], st([xrp], 'rpne0d', 'X =/= 0'), f['ne']], 'recdivd', '( 1 / %s ) = ( K / X )' % Q)
    rhole2 = st([rhole, rec], 'breqtrd', '( abs ` %s ) <_ ( K / X )' % RHO('K'))
    # | mu / K | <_ 1 / K
    ad = st([f['muc'], f['cc'], f['ne']], 'absdivd', '( abs ` %s ) = ( ( abs ` %s ) / ( abs ` K ) )' % (MQ('K'), MU('K')))
    ak = st([f['re'], st([f['rp']], 'rpge0d', '0 <_ K')], 'absidd', '( abs ` K ) = K')
    ad2 = st([ad, st([ak], 'oveq2d', '( ( abs ` %s ) / ( abs ` K ) ) = ( ( abs ` %s ) / K )' % (MU('K'), MU('K')))], 'eqtrd', '( abs ` %s ) = ( ( abs ` %s ) / K )' % (MQ('K'), MU('K')))
    mule = sy(w, A, f['nn'], 'mule1', '( abs ` %s ) <_ 1' % MU('K'))
    amur = st([f['muc']], 'abscld', '( abs ` %s ) e. RR' % MU('K'))
    mqle = st([ad2, st([amur, st([], '1red', '1 e. RR'), f['rp'], mule], 'lediv1dd', '( ( abs ` %s ) / K ) <_ ( 1 / K )' % MU('K'))], 'eqbrtrd',
              '( abs ` %s ) <_ ( 1 / K )' % MQ('K'))
    # product
    am = st([f['mqc'], f['rhoc']], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (MQ('K'), RHO('K'), MQ('K'), RHO('K')))
    amq = st([f['mqc']], 'abscld', '( abs ` %s ) e. RR' % MQ('K')); arho = st([f['rhoc']], 'abscld', '( abs ` %s ) e. RR' % RHO('K'))
    rk = st([f['rp']], 'rprecred', '( 1 / K ) e. RR'); kx = st([f['re'], xrp], 'rerpdivcld', '( K / X ) e. RR')
    pl = st([amq, rk, arho, kx, st([f['mqc']], 'absge0d', '0 <_ ( abs ` %s )' % MQ('K')), st([f['rhoc']], 'absge0d', '0 <_ ( abs ` %s )' % RHO('K')), mqle, rhole2], 'lemul12ad',
            '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( ( 1 / K ) x. ( K / X ) )' % (MQ('K'), RHO('K')))
    xc = st([xrp], 'rpcnd', 'X e. CC'); xne = st([xrp], 'rpne0d', 'X =/= 0')
    e1 = st([st([], '1cnd', '1 e. CC'), f['cc'], f['cc'], xc, f['ne'], xne], 'divmuldivd', '( ( 1 / K ) x. ( K / X ) ) = ( ( 1 x. K ) / ( K x. X ) )')
    e2 = st([st([st([f['cc']], 'mullidd', '( 1 x. K ) = K'), st([f['cc']], 'mulridd', '( K x. 1 ) = K')], 'eqtr4d', '( 1 x. K ) = ( K x. 1 )')], 'oveq1d',
            '( ( 1 x. K ) / ( K x. X ) ) = ( ( K x. 1 ) / ( K x. X ) )')
    e3 = st([st([], '1cnd', '1 e. CC'), xc, xne, f['cc'], f['ne']], 'divcan5d', '( ( K x. 1 ) / ( K x. X ) ) = ( 1 / X )')
    ee = st([st([e1, e2], 'eqtrd', '( ( 1 / K ) x. ( K / X ) ) = ( ( K x. 1 ) / ( K x. X ) )'), e3], 'eqtrd', '( ( 1 / K ) x. ( K / X ) ) = ( 1 / X )')
    w.qed([am, st([pl, ee], 'breqtrd', '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( 1 / X )' % (MQ('K'), RHO('K')))], 'eqbrtrd',
          '( %s -> ( abs ` ( %s x. %s ) ) <_ ( 1 / X ) )' % (A, MQ('K'), RHO('K')))
    return w


def bvmchk1lem2():
    w = W('bvmchk1lem2', 'The remainder in RZA Lemma 3.1 at sigma = 1 is at most 1 in absolute value.')
    st, xr, x1, xrp, nnn, nre, nlex = xfacts(w)
    AN = '( %s /\\ n e. %s )' % (HX, RX)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % RX)
    f = kfacts(w, AN, nel, lift(w, xr, AN), lift(w, xrp, AN), 'n')
    TERM = '( %s x. %s )' % (MQ('n'), RHO('n'))
    tc = sn([f['mqc'], f['rhoc']], 'mulcld', '%s e. CC' % TERM)
    l1 = sn([], 'bvmchk1lem1', '( abs ` %s ) <_ ( 1 / X )' % TERM)
    fin = st([], 'fzfid', '%s e. Fin' % RX)
    fa = st([fin, tc], 'fsumabs', '( abs ` %s ) <_ sum_ n e. %s ( abs ` %s )' % (RS, RX, TERM))
    fl = st([fin, sn([tc], 'abscld', '( abs ` %s ) e. RR' % TERM), sn([lift(w, xrp, AN)], 'rprecred', '( 1 / X ) e. RR'), l1], 'fsumle',
            'sum_ n e. %s ( abs ` %s ) <_ sum_ n e. %s ( 1 / X )' % (RX, TERM, RX))
    xc = st([xrp], 'rpcnd', 'X e. CC'); xne = st([xrp], 'rpne0d', 'X =/= 0')
    cst = sy2(w, HX, fin, st([xc, xne], 'reccld', '( 1 / X ) e. CC'), 'fsumconst', 'sum_ n e. %s ( 1 / X ) = ( ( # ` %s ) x. ( 1 / X ) )' % (RX, RX))
    hsh = sy(w, HX, st([nnn], 'nnnn0d', '%s e. NN0' % NX), 'hashfz1', '( # ` %s ) = %s' % (RX, NX))
    ncc = st([nre], 'recnd', '%s e. CC' % NX)
    cst2 = st([cst, st([st([hsh], 'oveq1d', '( ( # ` %s ) x. ( 1 / X ) ) = ( %s x. ( 1 / X ) )' % (RX, NX)), st([st([ncc, xc, xne], 'divrecd', '( %s / X ) = ( %s x. ( 1 / X ) )' % (NX, NX))], 'eqcomd', '( %s x. ( 1 / X ) ) = ( %s / X )' % (NX, NX))], 'eqtrd',
                        '( ( # ` %s ) x. ( 1 / X ) ) = ( %s / X )' % (RX, NX))], 'eqtrd', 'sum_ n e. %s ( 1 / X ) = ( %s / X )' % (RX, NX))
    le1 = st([st([nlex, st([xc], 'mulridd', '( X x. 1 ) = X')], 'breqtrrd', '%s <_ ( X x. 1 )' % NX), st([nre, st([], '1red', '1 e. RR'), xrp], 'ledivmuld', '( ( %s / X ) <_ 1 <-> %s <_ ( X x. 1 ) )' % (NX, NX))], 'mpbird',
              '( %s / X ) <_ 1' % NX)
    rsc = st([fin, tc], 'fsumcl', '%s e. CC' % RS)
    absr = st([rsc], 'abscld', '( abs ` %s ) e. RR' % RS)
    sar = st([fin, sn([tc], 'abscld', '( abs ` %s ) e. RR' % TERM)], 'fsumrecl', 'sum_ n e. %s ( abs ` %s ) e. RR' % (RX, TERM))
    nxr = st([nre, xrp], 'rerpdivcld', '( %s / X ) e. RR' % NX)
    ch = st([sar, nxr, st([], '1red', '1 e. RR'), st([fl, cst2], 'breqtrd', 'sum_ n e. %s ( abs ` %s ) <_ ( %s / X )' % (RX, TERM, NX)), le1], 'letrd',
            'sum_ n e. %s ( abs ` %s ) <_ 1' % (RX, TERM))
    w.qed([absr, sar, st([], '1red', '1 e. RR'), fa, ch], 'letrd', '( %s -> ( abs ` %s ) <_ 1 )' % (HX, RS))
    return w


def bvmchk1lem3():
    w = W('bvmchk1lem3', 'Identity (B) decomposed through the harmonic asymptotics: '
                         '1 = mCheck1 + gamma mHarm + R.')
    st, xr, x1, xrp, nnn, nre, nlex = xfacts(w)
    AN = '( %s /\\ n e. %s )' % (HX, RX)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % RX)
    f = kfacts(w, AN, nel, lift(w, xr, AN), lift(w, xrp, AN), 'n')
    idb = sy(w, HX, nnn, 'bvidb', 'sum_ n e. %s ( %s x. %s ) = 1' % (RX, MQ('n'), HK('n')))
    lggc = sn([f['lgg']], 'recnd', '( %s + gamma ) e. CC' % LG('n'))
    hkc = sn([f['hkr']], 'recnd', '%s e. CC' % HK('n'))
    dec = sn([lggc, hkc], 'pncan3d', '( ( %s + gamma ) + %s ) = %s' % (LG('n'), RHO('n'), HK('n')))
    lgc = sn([f['lgr']], 'recnd', '%s e. CC' % LG('n')); gc = sn([f['gr']], 'recnd', 'gamma e. CC')
    A1 = '( %s x. %s )' % (MQ('n'), LG('n')); A2 = '( %s x. gamma )' % MQ('n'); A3 = '( %s x. %s )' % (MQ('n'), RHO('n'))
    d1 = sn([f['mqc'], lggc, f['rhoc']], 'adddid', '( %s x. ( ( %s + gamma ) + %s ) ) = ( ( %s x. ( %s + gamma ) ) + %s )' % (MQ('n'), LG('n'), RHO('n'), MQ('n'), LG('n'), A3))
    d2 = sn([f['mqc'], lgc, gc], 'adddid', '( %s x. ( %s + gamma ) ) = ( %s + %s )' % (MQ('n'), LG('n'), A1, A2))
    a1c = sn([f['mqc'], lgc], 'mulcld', '%s e. CC' % A1); a2c = sn([f['mqc'], gc], 'mulcld', '%s e. CC' % A2); a3c = sn([f['mqc'], f['rhoc']], 'mulcld', '%s e. CC' % A3)
    d3 = sn([a1c, a2c, a3c], 'addassd', '( ( %s + %s ) + %s ) = ( %s + ( %s + %s ) )' % (A1, A2, A3, A1, A2, A3))
    term = sn([sn([sn([dec], 'eqcomd', '%s = ( ( %s + gamma ) + %s )' % (HK('n'), LG('n'), RHO('n')))], 'oveq2d', '( %s x. %s ) = ( %s x. ( ( %s + gamma ) + %s ) )' % (MQ('n'), HK('n'), MQ('n'), LG('n'), RHO('n'))),
              sn([sn([d1, sn([d2], 'oveq1d', '( ( %s x. ( %s + gamma ) ) + %s ) = ( ( %s + %s ) + %s )' % (MQ('n'), LG('n'), A3, A1, A2, A3))], 'eqtrd',
                     '( %s x. ( ( %s + gamma ) + %s ) ) = ( ( %s + %s ) + %s )' % (MQ('n'), LG('n'), RHO('n'), A1, A2, A3)), d3], 'eqtrd',
                 '( %s x. ( ( %s + gamma ) + %s ) ) = ( %s + ( %s + %s ) )' % (MQ('n'), LG('n'), RHO('n'), A1, A2, A3))], 'eqtrd',
              '( %s x. %s ) = ( %s + ( %s + %s ) )' % (MQ('n'), HK('n'), A1, A2, A3))
    fin = st([], 'fzfid', '%s e. Fin' % RX)
    S2 = 'sum_ n e. %s %s' % (RX, A2)
    s1 = st([term], 'sumeq2dv', 'sum_ n e. %s ( %s x. %s ) = sum_ n e. %s ( %s + ( %s + %s ) )' % (RX, MQ('n'), HK('n'), RX, A1, A2, A3))
    s2 = st([fin, a1c, sn([a2c, a3c], 'addcld', '( %s + %s ) e. CC' % (A2, A3))], 'fsumadd', 'sum_ n e. %s ( %s + ( %s + %s ) ) = ( %s + sum_ n e. %s ( %s + %s ) )' % (RX, A1, A2, A3, MC, RX, A2, A3))
    s3 = st([fin, a2c, a3c], 'fsumadd', 'sum_ n e. %s ( %s + %s ) = ( %s + %s )' % (RX, A2, A3, S2, RS))
    mc1 = st([fin, st([st([clo(w, 'emre', 'gamma e. RR')], 'a1i', 'gamma e. RR')], 'recnd', 'gamma e. CC'), f['mqc']], 'fsummulc1', '( %s x. gamma ) = %s' % (MH, S2))
    mhc = st([fin, f['mqc']], 'fsumcl', '%s e. CC' % MH)
    gm = st([st([mc1], 'eqcomd', '%s = ( %s x. gamma )' % (S2, MH)), st([mhc, st([st([clo(w, 'emre', 'gamma e. RR')], 'a1i', 'gamma e. RR')], 'recnd', 'gamma e. CC')], 'mulcomd', '( %s x. gamma ) = %s' % (MH, GM))], 'eqtrd', '%s = %s' % (S2, GM))
    s4 = st([s3, st([gm], 'oveq1d', '( %s + %s ) = ( %s + %s )' % (S2, RS, GM, RS))], 'eqtrd', 'sum_ n e. %s ( %s + %s ) = ( %s + %s )' % (RX, A2, A3, GM, RS))
    tot = st([st([s1, s2], 'eqtrd', 'sum_ n e. %s ( %s x. %s ) = ( %s + sum_ n e. %s ( %s + %s ) )' % (RX, MQ('n'), HK('n'), MC, RX, A2, A3)), st([s4], 'oveq2d', '( %s + sum_ n e. %s ( %s + %s ) ) = ( %s + ( %s + %s ) )' % (MC, RX, A2, A3, MC, GM, RS))], 'eqtrd',
             'sum_ n e. %s ( %s x. %s ) = ( %s + ( %s + %s ) )' % (RX, MQ('n'), HK('n'), MC, GM, RS))
    w.qed([idb, tot], 'eqtr3d', '( %s -> 1 = ( %s + ( %s + %s ) ) )' % (HX, MC, GM, RS))
    return w


def bvmchk1():
    w = W('bvmchk1', 'RZA Lemma 3.1 at sigma = 1, q = 1 with constant 11/3: the absolute value of '
                     'sum_ n <= X ( mmu n / n ) log ( X / n ) is at most 11 / 3 (Lean abs_mCheck1_le; '
                     'the proof gives 3).')
    st, xr, x1, xrp, nnn, nre, nlex = xfacts(w)
    AN = '( %s /\\ n e. %s )' % (HX, RX)
    sn = mkst(w, AN)
    nel = sn([], 'simpr', 'n e. %s' % RX)
    f = kfacts(w, AN, nel, lift(w, xr, AN), lift(w, xrp, AN), 'n')
    fin = st([], 'fzfid', '%s e. Fin' % RX)
    mcr = st([fin, sn([f['mqr'], f['lgr']], 'remulcld', '( %s x. %s ) e. RR' % (MQ('n'), LG('n')))], 'fsumrecl', '%s e. RR' % MC)
    mhr = st([fin, f['mqr']], 'fsumrecl', '%s e. RR' % MH)
    rsr = st([fin, sn([f['mqr'], f['rhor']], 'remulcld', '( %s x. %s ) e. RR' % (MQ('n'), RHO('n')))], 'fsumrecl', '%s e. RR' % RS)
    gr = st([clo(w, 'emre', 'gamma e. RR')], 'a1i', 'gamma e. RR')
    gmr = st([gr, mhr], 'remulcld', '%s e. RR' % GM)
    S = '( %s + %s )' % (GM, RS)
    sr = st([gmr, rsr], 'readdcld', '%s e. RR' % S)
    mcc = st([mcr], 'recnd', '%s e. CC' % MC); sc = st([sr], 'recnd', '%s e. CC' % S)
    l3 = st([], 'bvmchk1lem3', '1 = ( %s + %s )' % (MC, S))
    e1 = st([l3], 'oveq1d', '( 1 - %s ) = ( ( %s + %s ) - %s )' % (S, MC, S, S))
    e2 = st([mcc, sc], 'pncand', '( ( %s + %s ) - %s ) = %s' % (MC, S, S, MC))
    mceq = st([e1, e2], 'eqtr2d', '%s = ( 1 - %s )' % (MC, S))
    ng = st([st([], '1cnd', '1 e. CC'), sc], 'negsubd', '( 1 + -u %s ) = ( 1 - %s )' % (S, S))
    tri = sy2(w, HX, st([], '1cnd', '1 e. CC'), st([sc], 'negcld', '-u %s e. CC' % S), 'abstri', '( abs ` ( 1 + -u %s ) ) <_ ( ( abs ` 1 ) + ( abs ` -u %s ) )' % (S, S))
    an = st([sc], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (S, S))
    a1 = st([clo(w, 'abs1', '( abs ` 1 ) = 1')], 'a1i', '( abs ` 1 ) = 1')
    tri2 = st([st([st([mceq, st([ng], 'eqcomd', '( 1 - %s ) = ( 1 + -u %s )' % (S, S))], 'eqtrd', '%s = ( 1 + -u %s )' % (MC, S))], 'fveq2d', '( abs ` %s ) = ( abs ` ( 1 + -u %s ) )' % (MC, S)),
               st([tri, st([a1, an], 'oveq12d', '( ( abs ` 1 ) + ( abs ` -u %s ) ) = ( 1 + ( abs ` %s ) )' % (S, S))], 'breqtrd', '( abs ` ( 1 + -u %s ) ) <_ ( 1 + ( abs ` %s ) )' % (S, S))], 'eqbrtrd',
              '( abs ` %s ) <_ ( 1 + ( abs ` %s ) )' % (MC, S))
    tri3 = sy2(w, HX, st([gmr], 'recnd', '%s e. CC' % GM), st([rsr], 'recnd', '%s e. CC' % RS), 'abstri', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (S, GM, RS))
    # | gamma MH | <_ 1
    g0 = st([w.s([w.s([], '0re', '0 e. RR'), w.s([], 'emre', 'gamma e. RR'), w.s([], 'emgt0', '0 < gamma')], 'ltleii', '0 <_ gamma')], 'a1i', '0 <_ gamma')
    icb = w.s([w.s([w.s([], '1re', '1 e. RR'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR')], 'resubcli', '( 1 - ( log ` 2 ) ) e. RR'), w.s([], '1re', '1 e. RR')], 'elicc2i',
               '( gamma e. ( ( 1 - ( log ` 2 ) ) [,] 1 ) <-> ( gamma e. RR /\\ ( 1 - ( log ` 2 ) ) <_ gamma /\\ gamma <_ 1 ) )')
    g1 = st([w.s([w.s([w.s([], 'emcl', 'gamma e. ( ( 1 - ( log ` 2 ) ) [,] 1 )'), icb], 'mpbi', '( gamma e. RR /\\ ( 1 - ( log ` 2 ) ) <_ gamma /\\ gamma <_ 1 )')], 'simp3i', 'gamma <_ 1')], 'a1i', 'gamma <_ 1')
    mhle = st([], 'bvmharm', '( abs ` %s ) <_ 1' % MH)
    amh = st([st([mhr], 'recnd', '%s e. CC' % MH)], 'abscld', '( abs ` %s ) e. RR' % MH)
    agm = st([st([gr], 'recnd', 'gamma e. CC'), st([mhr], 'recnd', '%s e. CC' % MH)], 'absmuld', '( abs ` %s ) = ( ( abs ` gamma ) x. ( abs ` %s ) )' % (GM, MH))
    ag = st([gr, g0], 'absidd', '( abs ` gamma ) = gamma')
    pl = st([gr, st([], '1red', '1 e. RR'), amh, st([], '1red', '1 e. RR'), g0, st([st([mhr], 'recnd', '%s e. CC' % MH)], 'absge0d', '0 <_ ( abs ` %s )' % MH), g1, mhle], 'lemul12ad',
            '( gamma x. ( abs ` %s ) ) <_ ( 1 x. 1 )' % MH)
    one = w.s([w.s([], 'ax-1cn', '1 e. CC'), w.inst('mullid')], 'ax-mp', '( 1 x. 1 ) = 1')
    gmle = st([st([agm, st([ag], 'oveq1d', '( ( abs ` gamma ) x. ( abs ` %s ) ) = ( gamma x. ( abs ` %s ) )' % (MH, MH))], 'eqtrd', '( abs ` %s ) = ( gamma x. ( abs ` %s ) )' % (GM, MH)),
              st([pl, st([one], 'a1i', '( 1 x. 1 ) = 1')], 'breqtrd', '( gamma x. ( abs ` %s ) ) <_ 1' % MH)], 'eqbrtrd', '( abs ` %s ) <_ 1' % GM)
    rle = st([], 'bvmchk1lem2', '( abs ` %s ) <_ 1' % RS)
    amc = st([mcc], 'abscld', '( abs ` %s ) e. RR' % MC); asr = st([sc], 'abscld', '( abs ` %s ) e. RR' % S)
    agmr = st([st([gmr], 'recnd', '%s e. CC' % GM)], 'abscld', '( abs ` %s ) e. RR' % GM); arsr = st([st([rsr], 'recnd', '%s e. CC' % RS)], 'abscld', '( abs ` %s ) e. RR' % RS)
    linarith(w, HX, [tri2, tri3, gmle, rle], '( abs ` %s ) <_ ( ; 1 1 / 3 )' % MC,
             leaves={'( abs ` %s )' % MC: amc, '( abs ` %s )' % S: asr, '( abs ` %s )' % GM: agmr, '( abs ` %s )' % RS: arsr}, name='qed')
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['bvmchk1lem1', 'bvmchk1lem2', 'bvmchk1lem3', 'bvmchk1']:
        globals()[f]().run()
