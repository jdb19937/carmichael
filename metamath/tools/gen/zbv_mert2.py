"""Sortie ZBV, block Z-MP part 2: the prime reciprocal sum and the Mertens product.

T( i ) = sum_ d e. ( 1 ... i ) ( ( Lam ` d ) / d ),  W( i ) = ( 1 / ( log ` i ) ),  c = ( ( log ` 4 ) + 4 )

zdmabel   ( N e. ( ZZ>= ` 2 ) -> sum_ i e. ( 2 ... N ) ( W(i) x. ( ( Lam ` i ) / i ) )
             = ( ( W(N) x. T(N) ) + sum_ i e. ( 2 ... ( N - 1 ) ) ( ( W(i) - W(i+1) ) x. T(i) ) ) )
zdmpsum1  ( N e. ( ZZ>= ` 2 ) -> sum_ p e. PR(N) ( 1 / p ) <_ sum_ i e. ( 2 ... N ) ( W(i) x. ( ( Lam ` i ) / i ) ) )
zdmpsum2  ( I e. ( ZZ>= ` 2 ) -> ( ( W(I) - W(I+1) ) x. T(I) ) <_ ( ( LL(I+1) - LL(I) ) + ( c x. ( W(I) - W(I+1) ) ) ) )
zdmpsum3  ( N e. ( ZZ>= ` 2 ) -> sum_ i e. ( 2 ... ( N - 1 ) ) ( ( W(i) - W(i+1) ) x. T(i) )
             <_ ( ( LL(N) - LL(2) ) + ( c x. ( W(2) - W(N) ) ) ) )
zdmpsum   ( N e. ( ZZ>= ` 2 ) -> sum_ p e. PR(N) ( 1 / p ) <_ ( LL(N) + ( ( 1 + ( ( 2 x. c ) / ( log ` 2 ) ) ) - LL(2) ) ) )
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from zbvlib import *
from lin import linarith, nlinarith, lineq

PR = lambda N: '( ( 1 ... %s ) i^i Prime )' % N
T = lambda m, d='d': 'sum_ %s e. ( 1 ... %s ) ( ( Lam ` %s ) / %s )' % (d, m, d, d)
WL = lambda m: '( 1 / ( log ` %s ) )' % m
LAM = lambda m: '( ( Lam ` %s ) / %s )' % (m, m)
LL = lambda m: '( log ` ( log ` %s ) )' % m
C4 = '( ( log ` 4 ) + 4 )'
P1 = lambda m: '( %s + 1 )' % m


def tcl(w, ante, m, d='d'):
    """( ante -> T(m) e. RR ), ( ante -> T(m) e. CC ) for any m"""
    st = mkst(w, ante)
    AD = '( %s /\\ %s e. ( 1 ... %s ) )' % (ante, d, m)
    sd = mkst(w, AD)
    dnn = sy(w, AD, sd([], 'simpr', '%s e. ( 1 ... %s )' % (d, m)), 'elfznn', '%s e. NN' % d)
    body = sd([sy(w, AD, dnn, 'vmacl', '( Lam ` %s ) e. RR' % d), sd([dnn], 'nnrpd', '%s e. RR+' % d)], 'rerpdivcld',
              '%s e. RR' % LAM(d))
    fin = st([], 'fzfid', '( 1 ... %s ) e. Fin' % m)
    re = st([fin, body], 'fsumrecl', '%s e. RR' % T(m, d))
    return re, st([re], 'recnd', '%s e. CC' % T(m, d))


def wfacts(w, ante, m, mre, m1):
    """for m real with 1 < m (steps mre, m1): log m e. RR+, W(m) e. RR+, W(m) e. RR, W(m) e. CC"""
    st = mkst(w, ante)
    lrp = sy2(w, ante, mre, m1, 'rplogcl', '( log ` %s ) e. RR+' % m)
    wrp = st([lrp], 'rpreccld', '%s e. RR+' % WL(m))
    return lrp, wrp, st([wrp], 'rpred', '%s e. RR' % WL(m)), st([wrp], 'rpcnd', '%s e. CC' % WL(m))


def uz2facts(w, ante, iu, m):
    """from iu: ( ante -> m e. ( ZZ>= ` 2 ) ): m e. NN, ZZ, RR, CC, 1 < m, 2 <_ m"""
    st = mkst(w, ante)
    nn = sy(w, ante, iu, 'eluz2nn', '%s e. NN' % m)
    z = st([nn], 'nnzd', '%s e. ZZ' % m)
    re = st([nn], 'nnred', '%s e. RR' % m)
    cc = st([nn], 'nncnd', '%s e. CC' % m)
    gt1 = sy(w, ante, iu, 'eluz2gt1', '1 < %s' % m)
    ge2 = sy(w, ante, iu, 'eluzle', '2 <_ %s' % m)
    return nn, z, re, cc, gt1, ge2


def zdmabel():
    w = W('zdmabel', 'Discrete Abel summation for the von Mangoldt sum against 1 / log '
                     '(Lean abel_identity), from fsumparts.')
    PH = 'N e. ( ZZ>= ` 2 )'
    st = mkst(w, PH)
    nu = st([], 'id', PH)
    nnn, nz, nre, ncc, n1, n2 = uz2facts(w, PH, nu, 'N')
    one = st([], '1red', '1 e. RR'); onec = st([], '1cnd', '1 e. CC')
    two = st([clo(w, '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ')
    # ---- fsumparts substitution hypotheses (closed)
    A = WL('k'); V = T('( k - 1 )')
    def subh(Tk):
        eq = 'k = %s' % Tk
        idk = w.s([], 'id', '( %s -> %s )' % (eq, eq))
        s1, a1 = w.congr(A, {'k': Tk}, eq, {'k': idk})
        s2, v1 = w.congr(V, {'k': Tk}, eq, {'k': idk})
        return w.s([s1, s2], 'jca', '( %s -> ( %s = %s /\\ %s = %s ) )' % (eq, A, a1, V, v1)), a1, v1
    hb, B, Wj = subh('i')
    hc, Cc, X = subh(P1('i'))
    hd, D, Y = subh('2')
    he, E, Z = subh('N')
    # ---- closures on ( 2 ... N ) for the sequence variable k
    AK = '( %s /\\ k e. ( 2 ... N ) )' % PH
    sk = mkst(w, AK)
    kel = sk([], 'simpr', 'k e. ( 2 ... N )')
    ku = sy(w, AK, kel, 'elfzuz', 'k e. ( ZZ>= ` 2 )')
    knn, kz, kre, kcc, k1, k2 = uz2facts(w, AK, ku, 'k')
    _, _, _, wkc = wfacts(w, AK, 'k', kre, k1)
    _, tkc = tcl(w, AK, '( k - 1 )')
    parts = st([hb, hc, hd, he, nu, wkc, tkc], 'fsumparts',
               'sum_ i e. ( 2 ..^ N ) ( %s x. ( %s - %s ) ) = ( ( ( %s x. %s ) - ( %s x. %s ) ) - sum_ i e. ( 2 ..^ N ) ( ( %s - %s ) x. %s ) )'
               % (B, X, Wj, E, Z, D, Y, Cc, B, X))
    # ---- rewrites under i e. ( 2 ..^ N )
    AI = '( %s /\\ i e. ( 2 ..^ N ) )' % PH
    si = mkst(w, AI)
    iel = si([], 'simpr', 'i e. ( 2 ..^ N )')
    ifz = sy(w, AI, iel, 'elfzofz', 'i e. ( 2 ... N )')
    iu = sy(w, AI, ifz, 'elfzuz', 'i e. ( ZZ>= ` 2 )')
    inn, iz, ire, icc, i1, i2 = uz2facts(w, AI, iu, 'i')
    # X = T(i)
    pc = si([icc, lift(w, onec, AI)], 'pncand', '( ( i + 1 ) - 1 ) = i')
    xeq = si([si([pc], 'oveq2d', '( 1 ... ( ( i + 1 ) - 1 ) ) = ( 1 ... i )')], 'sumeq1d', '%s = %s' % (X, T('i')))
    # T(i) = T(i-1) + LAM(i)   (fsumm1 at M = 1, N = i)
    iuz1 = si([inn, si([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', 'i e. ( ZZ>= ` 1 )')
    AD = '( %s /\\ d e. ( 1 ... i ) )' % AI
    sd = mkst(w, AD)
    dnn = sy(w, AD, sd([], 'simpr', 'd e. ( 1 ... i )'), 'elfznn', 'd e. NN')
    bodyc = sd([sd([sy(w, AD, dnn, 'vmacl', '( Lam ` d ) e. RR' ), sd([dnn], 'nnrpd', 'd e. RR+')], 'rerpdivcld',
                   '%s e. RR' % LAM('d'))], 'recnd', '%s e. CC' % LAM('d'))
    idd = w.s([], 'id', '( d = i -> d = i )')
    subm, _ = w.congr(LAM('d'), {'d': 'i'}, 'd = i', {'d': idd})
    m1 = si([iuz1, bodyc, subm], 'fsumm1', '%s = ( %s + %s )' % (T('i'), T('( i - 1 )'), LAM('i')))
    tir, tic = tcl(w, AI, 'i'); tmr, tmc = tcl(w, AI, '( i - 1 )')
    lamr = si([sy(w, AI, inn, 'vmacl', '( Lam ` i ) e. RR'), si([inn], 'nnrpd', 'i e. RR+')], 'rerpdivcld', '%s e. RR' % LAM('i'))
    lamc = si([lamr], 'recnd', '%s e. CC' % LAM('i'))
    diff = si([si([m1], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (T('i'), T('( i - 1 )'), T('( i - 1 )'), LAM('i'), T('( i - 1 )'))),
               si([tmc, lamc], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (T('( i - 1 )'), LAM('i'), T('( i - 1 )'), LAM('i')))], 'eqtrd',
              '( %s - %s ) = %s' % (T('i'), T('( i - 1 )'), LAM('i')))
    xw = si([si([xeq], 'oveq1d', '( %s - %s ) = ( %s - %s )' % (X, Wj, T('i'), Wj)), diff], 'eqtrd', '( %s - %s ) = %s' % (X, Wj, LAM('i')))
    body1 = si([xw], 'oveq2d', '( %s x. ( %s - %s ) ) = ( %s x. %s )' % (B, X, Wj, B, LAM('i')))
    body2 = si([xeq], 'oveq2d', '( ( %s - %s ) x. %s ) = ( ( %s - %s ) x. %s )' % (Cc, B, X, Cc, B, T('i')))
    S2o = 'sum_ i e. ( 2 ..^ N ) ( %s x. %s )' % (B, LAM('i'))
    S3o = 'sum_ i e. ( 2 ..^ N ) ( ( %s - %s ) x. %s )' % (Cc, B, T('i'))
    e1 = st([body1], 'sumeq2dv', 'sum_ i e. ( 2 ..^ N ) ( %s x. ( %s - %s ) ) = %s' % (B, X, Wj, S2o))
    e2 = st([body2], 'sumeq2dv', 'sum_ i e. ( 2 ..^ N ) ( ( %s - %s ) x. %s ) = %s' % (Cc, B, X, S3o))
    # ( 2 ..^ N ) = ( 2 ... ( N - 1 ) )
    fzo = sy(w, PH, nz, 'fzoval', '( 2 ..^ N ) = ( 2 ... ( N - 1 ) )')
    S2 = 'sum_ i e. ( 2 ... ( N - 1 ) ) ( %s x. %s )' % (B, LAM('i'))
    S3 = 'sum_ i e. ( 2 ... ( N - 1 ) ) ( ( %s - %s ) x. %s )' % (Cc, B, T('i'))
    S4 = 'sum_ i e. ( 2 ... ( N - 1 ) ) ( ( %s - %s ) x. %s )' % (B, Cc, T('i'))
    e3 = st([fzo], 'sumeq1d', '%s = %s' % (S2o, S2))
    e4 = st([fzo], 'sumeq1d', '%s = %s' % (S3o, S3))
    lhs = st([e1, e3], 'eqtrd', 'sum_ i e. ( 2 ..^ N ) ( %s x. ( %s - %s ) ) = %s' % (B, X, Wj, S2))
    rhsS = st([e2, e4], 'eqtrd', 'sum_ i e. ( 2 ..^ N ) ( ( %s - %s ) x. %s ) = %s' % (Cc, B, X, S3))
    # Y = T(1) = 0, so D x. Y = 0
    y1 = st([st([clo(w, '2m1e1', '( 2 - 1 ) = 1')], 'a1i', '( 2 - 1 ) = 1')], 'oveq2d', '( 1 ... ( 2 - 1 ) ) = ( 1 ... 1 )')
    yeq = st([y1], 'sumeq1d', '%s = %s' % (Y, T('1')))
    idd1 = w.s([], 'id', '( d = 1 -> d = 1 )')
    sub1, _ = w.congr(LAM('d'), {'d': '1'}, 'd = 1', {'d': idd1})
    lam1 = w.s([w.s([clo(w, 'vma1', '( Lam ` 1 ) = 0')], 'oveq1i', '( ( Lam ` 1 ) / 1 ) = ( 0 / 1 )'),
                w.s([w.s([], '0cn', '0 e. CC'), w.inst('div1')], 'ax-mp', '( 0 / 1 ) = 0')], 'eqtri', '( ( Lam ` 1 ) / 1 ) = 0')
    # fsum1 with B := ( ( Lam ` 1 ) / 1 ) then rewrite to 0
    inst1 = w.s([sub1], 'fsum1', '( ( 1 e. ZZ /\\ ( ( Lam ` 1 ) / 1 ) e. CC ) -> %s = ( ( Lam ` 1 ) / 1 ) )' % T('1'))
    lam1c = w.s([lam1, w.s([], '0cn', '0 e. CC')], 'eqeltri', '( ( Lam ` 1 ) / 1 ) e. CC')
    t1v = w.s([w.s([], '1z', '1 e. ZZ'), lam1c, inst1], 'mp2an', '%s = ( ( Lam ` 1 ) / 1 )' % T('1'))
    t1z = w.s([t1v, lam1], 'eqtri', '%s = 0' % T('1'))
    yz = st([yeq, st([t1z], 'a1i', '%s = 0' % T('1'))], 'eqtrd', '%s = 0' % Y)
    lrp2 = w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2'), w.inst('rplogcl')], 'mp2an', '( log ` 2 ) e. RR+')
    dcc = st([st([w.s([lrp2, w.inst('rpreccl')], 'ax-mp', '%s e. RR+' % D)], 'a1i', '%s e. RR+' % D)], 'rpcnd', '%s e. CC' % D)
    dy0 = st([st([yz], 'oveq2d', '( %s x. %s ) = ( %s x. 0 )' % (D, Y, D)), st([dcc], 'mul01d', '( %s x. 0 ) = 0' % D)], 'eqtrd',
             '( %s x. %s ) = 0' % (D, Y))
    # S4 = -u S3
    tirc = tic
    AI2 = '( %s /\\ i e. ( 2 ... ( N - 1 ) ) )' % PH
    si2 = mkst(w, AI2)
    iel2 = si2([], 'simpr', 'i e. ( 2 ... ( N - 1 ) )')
    iu2 = sy(w, AI2, iel2, 'elfzuz', 'i e. ( ZZ>= ` 2 )')
    inn2, iz2, ire2, icc2, i12, i22 = uz2facts(w, AI2, iu2, 'i')
    _, _, wir2, wic2 = wfacts(w, AI2, 'i', ire2, i12)
    ip1re = si2([ire2, lift(w, one, AI2)], 'readdcld', '( i + 1 ) e. RR')
    ip11 = linarith(w, AI2, [i12], '1 < ( i + 1 )', leaves={'i': ire2})
    _, _, wipr2, wipc2 = wfacts(w, AI2, P1('i'), ip1re, ip11)
    tir2, tic2 = tcl(w, AI2, 'i')
    cmb = si2([wipc2, wic2], 'subcld', '( %s - %s ) e. CC' % (Cc, B))
    term3 = si2([cmb, tic2], 'mulcld', '( ( %s - %s ) x. %s ) e. CC' % (Cc, B, T('i')))
    neg1 = si2([wipc2, wic2], 'negsubdi2d', '-u ( %s - %s ) = ( %s - %s )' % (Cc, B, B, Cc))
    neg2 = si2([cmb, tic2], 'mulneg1d', '( -u ( %s - %s ) x. %s ) = -u ( ( %s - %s ) x. %s )' % (Cc, B, T('i'), Cc, B, T('i')))
    neg3 = si2([si2([neg1], 'oveq1d', '( -u ( %s - %s ) x. %s ) = ( ( %s - %s ) x. %s )' % (Cc, B, T('i'), B, Cc, T('i'))), neg2], 'eqtr3d',
               '( ( %s - %s ) x. %s ) = -u ( ( %s - %s ) x. %s )' % (B, Cc, T('i'), Cc, B, T('i')))
    fin2 = st([], 'fzfid', '( 2 ... ( N - 1 ) ) e. Fin')
    s4a = st([neg3], 'sumeq2dv', '%s = sum_ i e. ( 2 ... ( N - 1 ) ) -u ( ( %s - %s ) x. %s )' % (S4, Cc, B, T('i')))
    s4b = st([fin2, term3], 'fsumneg', 'sum_ i e. ( 2 ... ( N - 1 ) ) -u ( ( %s - %s ) x. %s ) = -u %s' % (Cc, B, T('i'), S3))
    s4 = st([s4a, s4b], 'eqtrd', '%s = -u %s' % (S4, S3))
    # SF = S2 + f(N) ; T(N) = Z + LAM(N)
    SF = 'sum_ i e. ( 2 ... N ) ( %s x. %s )' % (B, LAM('i'))
    AI3 = '( %s /\\ i e. ( 2 ... N ) )' % PH
    si3 = mkst(w, AI3)
    iu3 = sy(w, AI3, si3([], 'simpr', 'i e. ( 2 ... N )'), 'elfzuz', 'i e. ( ZZ>= ` 2 )')
    inn3, iz3, ire3, icc3, i13, i23 = uz2facts(w, AI3, iu3, 'i')
    _, _, wir3, wic3 = wfacts(w, AI3, 'i', ire3, i13)
    lamc3 = si3([si3([sy(w, AI3, inn3, 'vmacl', '( Lam ` i ) e. RR'), si3([inn3], 'nnrpd', 'i e. RR+')], 'rerpdivcld',
                    '%s e. RR' % LAM('i'))], 'recnd', '%s e. CC' % LAM('i'))
    fbody = si3([wic3, lamc3], 'mulcld', '( %s x. %s ) e. CC' % (B, LAM('i')))
    idi = w.s([], 'id', '( i = N -> i = N )')
    subN, FN = w.congr('( %s x. %s )' % (B, LAM('i')), {'i': 'N'}, 'i = N', {'i': idi})
    sfm1 = st([nu, fbody, subN], 'fsumm1', '%s = ( %s + %s )' % (SF, S2, FN))
    nuz1 = st([nnn, st([clo(w, 'nnuz', NNUZ)], 'a1i', NNUZ)], 'eleqtrd', 'N e. ( ZZ>= ` 1 )')
    ADN = '( %s /\\ d e. ( 1 ... N ) )' % PH
    sdn = mkst(w, ADN)
    dnnN = sy(w, ADN, sdn([], 'simpr', 'd e. ( 1 ... N )'), 'elfznn', 'd e. NN')
    bodyN = sdn([sdn([sy(w, ADN, dnnN, 'vmacl', '( Lam ` d ) e. RR'), sdn([dnnN], 'nnrpd', 'd e. RR+')], 'rerpdivcld',
                     '%s e. RR' % LAM('d'))], 'recnd', '%s e. CC' % LAM('d'))
    iddN = w.s([], 'id', '( d = N -> d = N )')
    subdN, _ = w.congr(LAM('d'), {'d': 'N'}, 'd = N', {'d': iddN})
    tnm1 = st([nuz1, bodyN, subdN], 'fsumm1', '%s = ( %s + %s )' % (T('N'), Z, LAM('N')))
    _, _, wnr, wnc = wfacts(w, PH, 'N', nre, n1)
    zr, zc = tcl(w, PH, '( N - 1 )')
    tnr, tnc = tcl(w, PH, 'N')
    lamNre = st([sy(w, PH, nnn, 'vmacl', '( Lam ` N ) e. RR'), st([nnn], 'nnrpd', 'N e. RR+')], 'rerpdivcld', '%s e. RR' % LAM('N'))
    lamNc = st([lamNre], 'recnd', '%s e. CC' % LAM('N'))
    wtn = st([st([tnm1], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s + %s ) )' % (E, T('N'), E, Z, LAM('N'))),
              st([wnc, zc, lamNc], 'adddid', '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (E, Z, LAM('N'), E, Z, E, LAM('N')))],
             'eqtrd', '( %s x. %s ) = ( ( %s x. %s ) + %s )' % (E, T('N'), E, Z, FN))
    # ---- assembly by lineq
    main = st([parts, lhs], 'eqtr3d', '%s = ( ( ( %s x. %s ) - ( %s x. %s ) ) - sum_ i e. ( 2 ..^ N ) ( ( %s - %s ) x. %s ) )' % (S2, E, Z, D, Y, Cc, B, X))
    main2 = st([main, st([rhsS], 'oveq2d', '( ( ( %s x. %s ) - ( %s x. %s ) ) - sum_ i e. ( 2 ..^ N ) ( ( %s - %s ) x. %s ) ) = ( ( ( %s x. %s ) - ( %s x. %s ) ) - %s )' % (E, Z, D, Y, Cc, B, X, E, Z, D, Y, S3))],
               'eqtrd', '%s = ( ( ( %s x. %s ) - ( %s x. %s ) ) - %s )' % (S2, E, Z, D, Y, S3))
    # real closures of the atoms
    AI2r = si2([wir2, si2([sy(w, AI2, inn2, 'vmacl', '( Lam ` i ) e. RR'), si2([inn2], 'nnrpd', 'i e. RR+')], 'rerpdivcld', '%s e. RR' % LAM('i'))], 'remulcld',
                '( %s x. %s ) e. RR' % (B, LAM('i')))
    s2r = st([fin2, AI2r], 'fsumrecl', '%s e. RR' % S2)
    s3r = st([fin2, si2([si2([wipr2, wir2], 'resubcld', '( %s - %s ) e. RR' % (Cc, B)), tir2], 'remulcld', '( ( %s - %s ) x. %s ) e. RR' % (Cc, B, T('i')))],
             'fsumrecl', '%s e. RR' % S3)
    s4r = st([fin2, si2([si2([wir2, wipr2], 'resubcld', '( %s - %s ) e. RR' % (B, Cc)), tir2], 'remulcld', '( ( %s - %s ) x. %s ) e. RR' % (B, Cc, T('i')))],
             'fsumrecl', '%s e. RR' % S4)
    sfr = st([st([], 'fzfid', '( 2 ... N ) e. Fin'), si3([wir3, si3([sy(w, AI3, inn3, 'vmacl', '( Lam ` i ) e. RR'), si3([inn3], 'nnrpd', 'i e. RR+')], 'rerpdivcld', '%s e. RR' % LAM('i'))], 'remulcld',
                                                        '( %s x. %s ) e. RR' % (B, LAM('i')))], 'fsumrecl', '%s e. RR' % SF)
    ezr = st([wnr, zr], 'remulcld', '( %s x. %s ) e. RR' % (E, Z))
    etr = st([wnr, tnr], 'remulcld', '( %s x. %s ) e. RR' % (E, T('N')))
    fnr = st([wnr, lamNre], 'remulcld', '%s e. RR' % FN)
    dre = st([st([w.s([lrp2, w.inst('rpreccl')], 'ax-mp', '%s e. RR+' % D)], 'a1i', '%s e. RR+' % D)], 'rpred', '%s e. RR' % D)
    yre, _ = tcl(w, PH, '( 2 - 1 )')
    dyr = st([dre, yre], 'remulcld', '( %s x. %s ) e. RR' % (D, Y))
    leaves = {S2: s2r, S3: s3r, S4: s4r, SF: sfr, '( %s x. %s )' % (E, Z): ezr, '( %s x. %s )' % (E, T('N')): etr,
              FN: fnr, '( %s x. %s )' % (D, Y): dyr}
    goal = '%s + %s' % ('( %s x. %s )' % (E, T('N')), S4)
    lineq(w, PH, SF, '( ( %s x. %s ) + %s )' % (E, T('N'), S4), hyps=[main2, dy0, s4, sfm1, wtn], leaves=leaves, name='qed')
    return w



def zdmpsum1():
    w = W('zdmpsum1', 'The prime reciprocal sum is dominated by the 1 / log-weighted von '
                      'Mangoldt sum over ( 2 ... N ).')
    PH = 'N e. ( ZZ>= ` 2 )'
    st = mkst(w, PH)
    BODY = lambda v: '( %s x. %s )' % (WL(v), LAM(v))
    # termwise identity on the primes
    AP = '( %s /\\ p e. %s )' % (PH, PR('N'))
    sp = mkst(w, AP)
    pel = sp([], 'simpr', 'p e. %s' % PR('N'))
    pp = sy(w, AP, pel, 'elinel2', 'p e. Prime')
    pnn = sy(w, AP, pp, 'prmnn', 'p e. NN')
    pre = sp([pnn], 'nnred', 'p e. RR'); pcc = sp([pnn], 'nncnd', 'p e. CC'); pne = sp([pnn], 'nnne0d', 'p =/= 0')
    p1 = sy(w, AP, pp, 'prmgt1', '1 < p')
    lrp, wrp, wre, wcc = wfacts(w, AP, 'p', pre, p1)
    L = '( log ` p )'
    lcc = sp([lrp], 'rpcnd', '%s e. CC' % L); lne = sp([lrp], 'rpne0d', '%s =/= 0' % L)
    vp = sy(w, AP, pp, 'vmaprm', '( Lam ` p ) = %s' % L)
    e1 = sp([sp([vp], 'oveq1d', '%s = ( %s / p )' % (LAM('p'), L))], 'oveq2d', '%s = ( %s x. ( %s / p ) )' % (BODY('p'), WL('p'), L))
    e2 = sp([sp([], '1cnd', '1 e. CC'), lcc, lcc, pcc, lne, pne], 'divmuldivd',
            '( %s x. ( %s / p ) ) = ( ( 1 x. %s ) / ( %s x. p ) )' % (WL('p'), L, L, L))
    e3 = sp([sp([sp([lcc], 'mullidd', '( 1 x. %s ) = %s' % (L, L)), sp([lcc], 'mulridd', '( %s x. 1 ) = %s' % (L, L))], 'eqtr4d',
                '( 1 x. %s ) = ( %s x. 1 )' % (L, L))], 'oveq1d', '( ( 1 x. %s ) / ( %s x. p ) ) = ( ( %s x. 1 ) / ( %s x. p ) )' % (L, L, L, L))
    e4 = sp([sp([], '1cnd', '1 e. CC'), pcc, pne, lcc, lne], 'divcan5d', '( ( %s x. 1 ) / ( %s x. p ) ) = ( 1 / p )' % (L, L))
    ident = sp([sp([e1, e2], 'eqtrd', '%s = ( ( 1 x. %s ) / ( %s x. p ) )' % (BODY('p'), L, L)), sp([e3, e4], 'eqtrd',
                '( ( 1 x. %s ) / ( %s x. p ) ) = ( 1 / p )' % (L, L))], 'eqtrd', '%s = ( 1 / p )' % BODY('p'))
    seq1 = st([sp([ident], 'eqcomd', '( 1 / p ) = %s' % BODY('p'))], 'sumeq2dv',
              'sum_ p e. %s ( 1 / p ) = sum_ p e. %s %s' % (PR('N'), PR('N'), BODY('p')))
    # fsumless over ( 2 ... N ) with variable p
    A2 = '( %s /\\ p e. ( 2 ... N ) )' % PH
    s2 = mkst(w, A2)
    pel2 = s2([], 'simpr', 'p e. ( 2 ... N )')
    pu2 = sy(w, A2, pel2, 'elfzuz', 'p e. ( ZZ>= ` 2 )')
    pnn2, pz2, pre2, pcc2, p12, p22 = uz2facts(w, A2, pu2, 'p')
    lrp2, wrp2, wre2, wcc2 = wfacts(w, A2, 'p', pre2, p12)
    lamre2 = s2([sy(w, A2, pnn2, 'vmacl', '( Lam ` p ) e. RR'), s2([pnn2], 'nnrpd', 'p e. RR+')], 'rerpdivcld', '%s e. RR' % LAM('p'))
    lamge2 = s2([sy(w, A2, pnn2, 'vmacl', '( Lam ` p ) e. RR'), s2([pnn2], 'nnrpd', 'p e. RR+'), sy(w, A2, pnn2, 'vmage0', '0 <_ ( Lam ` p )')],
                'divge0d', '0 <_ %s' % LAM('p'))
    bre = s2([wre2, lamre2], 'remulcld', '%s e. RR' % BODY('p'))
    bge = s2([wre2, lamre2, s2([wrp2], 'rpge0d', '0 <_ %s' % WL('p')), lamge2], 'mulge0d', '0 <_ %s' % BODY('p'))
    fin = st([], 'fzfid', '( 2 ... N ) e. Fin')
    ss = st([clo(w, 'zdmprss', '%s C_ ( 2 ... N )' % PR('N'))], 'a1i', '%s C_ ( 2 ... N )' % PR('N'))
    less = st([fin, bre, bge, ss], 'fsumless', 'sum_ p e. %s %s <_ sum_ p e. ( 2 ... N ) %s' % (PR('N'), BODY('p'), BODY('p')))
    idp = w.s([], 'id', '( p = i -> p = i )')
    cs, _ = w.congr(BODY('p'), {'p': 'i'}, 'p = i', {'p': idp})
    cb = w.s([cs], 'cbvsumv', 'sum_ p e. ( 2 ... N ) %s = sum_ i e. ( 2 ... N ) %s' % (BODY('p'), BODY('i')))
    less2 = st([less, st([cb], 'a1i', 'sum_ p e. ( 2 ... N ) %s = sum_ i e. ( 2 ... N ) %s' % (BODY('p'), BODY('i')))], 'breqtrd',
               'sum_ p e. %s %s <_ sum_ i e. ( 2 ... N ) %s' % (PR('N'), BODY('p'), BODY('i')))
    w.qed([seq1, less2], 'eqbrtrd', '( %s -> sum_ p e. %s ( 1 / p ) <_ sum_ i e. ( 2 ... N ) %s )' % (PH, PR('N'), BODY('i')))
    return w


def zdmpsum2():
    w = W('zdmpsum2', 'One term of the Abel-summed series: ( W(I) - W(I+1) ) T(I) is at most the '
                      'log log increment plus c ( W(I) - W(I+1) ).')
    PH = 'I e. ( ZZ>= ` 2 )'
    st = mkst(w, PH)
    iu = st([], 'id', PH)
    inn, iz, ire, icc, i1, i2 = uz2facts(w, PH, iu, 'I')
    one = st([], '1red', '1 e. RR')
    ipre = st([ire, one], 'readdcld', '( I + 1 ) e. RR')
    ip1 = linarith(w, PH, [i1], '1 < ( I + 1 )', leaves={'I': ire})
    larp, warp, war, wac = wfacts(w, PH, 'I', ire, i1)
    lbrp, wbrp, wbr, wbc = wfacts(w, PH, P1('I'), ipre, ip1)
    LA = '( log ` I )'; LB = '( log ` ( I + 1 ) )'
    WA = WL('I'); WB = WL(P1('I'))
    DW = '( %s - %s )' % (WA, WB)
    dwr = st([war, wbr], 'resubcld', '%s e. RR' % DW)
    # 0 <_ DW
    lale = st([st([ire], 'ltp1d', 'I < ( I + 1 )'), sy2(w, PH, st([ire, linarith(w, PH, [i1], '0 < I', leaves={'I': ire})], 'elrpd', 'I e. RR+'),
                                                       st([ipre, linarith(w, PH, [i1], '0 < ( I + 1 )', leaves={'I': ire})], 'elrpd', '( I + 1 ) e. RR+'),
                                                       'logltb', '( I < ( I + 1 ) <-> %s < %s )' % (LA, LB))], 'mpbid', '%s < %s' % (LA, LB))
    lale2 = st([st([larp], 'rpred', '%s e. RR' % LA), st([lbrp], 'rpred', '%s e. RR' % LB), lale], 'ltled', '%s <_ %s' % (LA, LB))
    wle = st([lale2, st([larp, lbrp], 'lerecd', '( %s <_ %s <-> %s <_ %s )' % (LA, LB, WB, WA))], 'mpbid', '%s <_ %s' % (WB, WA))
    dw0 = st([wle, st([war, wbr], 'subge0d', '( 0 <_ %s <-> %s <_ %s )' % (DW, WB, WA))], 'mpbird', '0 <_ %s' % DW)
    # T(I) <_ log I + c
    tre, tcc = tcl(w, PH, 'I')
    ige1 = linarith(w, PH, [i1], '1 <_ I', leaves={'I': ire})
    m1 = sy2(w, PH, ire, ige1, 'mertens1le', '%s <_ ( %s + %s )' % (T('( |_ ` I )'), LA, C4))
    fl = sy(w, PH, iz, 'flid', '( |_ ` I ) = I')
    tle = st([st([st([fl], 'oveq2d', '( 1 ... ( |_ ` I ) ) = ( 1 ... I )')], 'sumeq1d', '%s = %s' % (T('( |_ ` I )'), T('I'))), m1], 'eqbrtrrd',
             '%s <_ ( %s + %s )' % (T('I'), LA, C4))
    c4r = w.s([w.s([w.s([], '4rp', '4 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 4 ) e. RR'), w.s([], '4re', '4 e. RR')], 'readdcli', '%s e. RR' % C4)
    c4d = st([c4r], 'a1i', '%s e. RR' % C4)
    lar = st([larp], 'rpred', '%s e. RR' % LA)
    sumr = st([lar, c4d], 'readdcld', '( %s + %s ) e. RR' % (LA, C4))
    P = '( %s x. %s )' % (DW, T('I'))
    Q = '( %s x. ( %s + %s ) )' % (DW, LA, C4)
    pq = st([tre, sumr, dwr, dw0, tle], 'lemul2ad', '%s <_ %s' % (P, Q))
    # Q = R + Cw
    dwc = st([dwr], 'recnd', '%s e. CC' % DW)
    lac = st([larp], 'rpcnd', '%s e. CC' % LA); c4c = st([c4d], 'recnd', '%s e. CC' % C4)
    R = '( %s x. %s )' % (DW, LA)
    CW = '( %s x. %s )' % (C4, DW)
    qeq = st([st([dwc, lac, c4c], 'adddid', '%s = ( %s + ( %s x. %s ) )' % (Q, R, DW, C4)),
              st([st([dwc, c4c], 'mulcomd', '( %s x. %s ) = %s' % (DW, C4, CW))], 'oveq2d', '( %s + ( %s x. %s ) ) = ( %s + %s )' % (R, DW, C4, R, CW))],
             'eqtrd', '%s = ( %s + %s )' % (Q, R, CW))
    # R = 1 - LA / LB
    U = '( 1 - ( %s / %s ) )' % (LA, LB)
    lbc = st([lbrp], 'rpcnd', '%s e. CC' % LB); lbne = st([lbrp], 'rpne0d', '%s =/= 0' % LB); lane = st([larp], 'rpne0d', '%s =/= 0' % LA)
    r1 = st([wac, wbc, lac], 'subdird', '%s = ( ( %s x. %s ) - ( %s x. %s ) )' % (R, WA, LA, WB, LA))
    r2 = st([lac, lane], 'recid2d', '( %s x. %s ) = 1' % (WA, LA))
    r3 = st([lac, lbc, lbne], 'divrec2d', '( %s / %s ) = ( %s x. %s )' % (LA, LB, WB, LA))
    r4 = st([r2, st([r3], 'eqcomd', '( %s x. %s ) = ( %s / %s )' % (WB, LA, LA, LB))], 'oveq12d',
            '( ( %s x. %s ) - ( %s x. %s ) ) = %s' % (WA, LA, WB, LA, U))
    req = st([r1, r4], 'eqtrd', '%s = %s' % (R, U))
    V = '( %s - %s )' % (LL(P1('I')), LL('I'))
    uv = st([iu, w.inst('zdmlogl')], 'syl', '%s <_ %s' % (U, V))
    # assemble
    pr = st([dwr, tre], 'remulcld', '%s e. RR' % P)
    qr = st([dwr, sumr], 'remulcld', '%s e. RR' % Q)
    rr = st([dwr, lar], 'remulcld', '%s e. RR' % R)
    qr_ = st([lar, lbrp], 'rerpdivcld', '( %s / %s ) e. RR' % (LA, LB))
    ur = st([one, qr_], 'resubcld', '%s e. RR' % U)
    llb = st([lbrp], 'relogcld', '%s e. RR' % LL(P1('I'))); lla = st([larp], 'relogcld', '%s e. RR' % LL('I'))
    vr = st([llb, lla], 'resubcld', '%s e. RR' % V)
    cwr = st([c4d, dwr], 'remulcld', '%s e. RR' % CW)
    linarith(w, PH, [pq, qeq, req, uv], '%s <_ ( %s + %s )' % (P, V, CW),
             leaves={P: pr, Q: qr, R: rr, U: ur, V: vr, CW: cwr, '( %s / %s )' % (LA, LB): qr_, LL(P1('I')): llb, LL('I'): lla}, name='qed')
    return w


def zdmpsum3():
    w = W('zdmpsum3', 'The interior sum of the Abel summation telescopes: it is at most '
                      '( log log N - log log 2 ) + c ( W(2) - W(N) ).')
    PH = 'N e. ( ZZ>= ` 2 )'
    st = mkst(w, PH)
    nu = st([], 'id', PH)
    nnn, nz, nre, ncc, n1, n2 = uz2facts(w, PH, nu, 'N')
    one = st([], '1red', '1 e. RR'); onec = st([], '1cnd', '1 e. CC')
    DW = lambda v: '( %s - %s )' % (WL(v), WL(P1(v)))
    V = lambda v: '( %s - %s )' % (LL(P1(v)), LL(v))
    CW = lambda v: '( %s x. %s )' % (C4, DW(v))
    RNG = '( 2 ... ( N - 1 ) )'
    AI = '( %s /\\ i e. %s )' % (PH, RNG)
    si = mkst(w, AI)
    iu = sy(w, AI, si([], 'simpr', 'i e. %s' % RNG), 'elfzuz', 'i e. ( ZZ>= ` 2 )')
    inn, iz, ire, icc, i1, i2 = uz2facts(w, AI, iu, 'i')
    ipre = si([ire, lift(w, one, AI)], 'readdcld', '( i + 1 ) e. RR')
    ip1 = linarith(w, AI, [i1], '1 < ( i + 1 )', leaves={'i': ire})
    larp, warp, war, wac = wfacts(w, AI, 'i', ire, i1)
    lbrp, wbrp, wbr, wbc = wfacts(w, AI, P1('i'), ipre, ip1)
    tre, tcc = tcl(w, AI, 'i')
    c4r = w.s([w.s([w.s([], '4rp', '4 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 4 ) e. RR'), w.s([], '4re', '4 e. RR')], 'readdcli', '%s e. RR' % C4)
    c4i = si([c4r], 'a1i', '%s e. RR' % C4)
    dwr = si([war, wbr], 'resubcld', '%s e. RR' % DW('i'))
    lhsb = si([dwr, tre], 'remulcld', '( %s x. %s ) e. RR' % (DW('i'), T('i')))
    vr = si([si([lbrp], 'relogcld', '%s e. RR' % LL(P1('i'))), si([larp], 'relogcld', '%s e. RR' % LL('i'))], 'resubcld', '%s e. RR' % V('i'))
    cwr = si([c4i, dwr], 'remulcld', '%s e. RR' % CW('i'))
    rhsb = si([vr, cwr], 'readdcld', '( %s + %s ) e. RR' % (V('i'), CW('i')))
    tw = si([iu, w.inst('zdmpsum2')], 'syl', '( %s x. %s ) <_ ( %s + %s )' % (DW('i'), T('i'), V('i'), CW('i')))
    fin = st([], 'fzfid', '%s e. Fin' % RNG)
    SL = 'sum_ i e. %s ( %s x. %s )' % (RNG, DW('i'), T('i'))
    SR = 'sum_ i e. %s ( %s + %s )' % (RNG, V('i'), CW('i'))
    le1 = st([fin, lhsb, rhsb, tw], 'fsumle', '%s <_ %s' % (SL, SR))
    SV = 'sum_ i e. %s %s' % (RNG, V('i')); SC = 'sum_ i e. %s %s' % (RNG, CW('i')); SD = 'sum_ i e. %s %s' % (RNG, DW('i'))
    add = st([fin, si([vr], 'recnd', '%s e. CC' % V('i')), si([cwr], 'recnd', '%s e. CC' % CW('i'))], 'fsumadd', '%s = ( %s + %s )' % (SR, SV, SC))
    c4c = st([st([c4r], 'a1i', '%s e. RR' % C4)], 'recnd', '%s e. CC' % C4)
    mul = st([fin, c4c, si([dwr], 'recnd', '%s e. CC' % DW('i'))], 'fsummulc2', '( %s x. %s ) = %s' % (C4, SD, SC))
    # telescoping: both over ( 2 ... ( N - 1 ) ) with telfsum's N := ( N - 1 )
    NM = '( N - 1 )'
    nm1z = sy(w, PH, nz, 'peano2zm', '%s e. ZZ' % NM)
    npc = st([ncc, onec], 'npcand', '( %s + 1 ) = N' % NM)
    nm1uz = st([st([npc], 'eqcomd', 'N = ( %s + 1 )' % NM), nu], 'eqeltrrd', '( %s + 1 ) e. ( ZZ>= ` 2 )' % NM)
    # closure on ( 2 ... ( ( N - 1 ) + 1 ) ) for k
    AK = '( %s /\\ k e. ( 2 ... ( %s + 1 ) ) )' % (PH, NM)
    sk = mkst(w, AK)
    ku = sy(w, AK, sk([], 'simpr', 'k e. ( 2 ... ( %s + 1 ) )' % NM), 'elfzuz', 'k e. ( ZZ>= ` 2 )')
    knn, kz, kre, kcc, k1, k2 = uz2facts(w, AK, ku, 'k')
    lkrp, wkrp, wkr, wkc = wfacts(w, AK, 'k', kre, k1)
    llkc = sk([sk([lkrp], 'relogcld', '%s e. RR' % LL('k'))], 'recnd', '%s e. CC' % LL('k'))
    def subs(expr):
        outs = []
        for Tk in ('i', P1('i'), '2', '( %s + 1 )' % NM):
            eq = 'k = %s' % Tk
            idk = w.s([], 'id', '( %s -> %s )' % (eq, eq))
            s1, _ = w.congr(expr, {'k': Tk}, eq, {'k': idk})
            outs.append(s1)
        return outs
    sw = subs(WL('k'))
    tel1 = st(sw + [nm1z, nm1uz, wkc], 'telfsum', '%s = ( %s - %s )' % (SD, WL('2'), WL('( %s + 1 )' % NM)))
    sl = subs(LL('k'))
    tel2 = st(sl + [nm1z, nm1uz, llkc], 'telfsum2', '%s = ( %s - %s )' % (SV, LL('( %s + 1 )' % NM), LL('2')))
    # rewrite ( N - 1 ) + 1 = N
    t1 = st([tel1, st([st([st([npc], 'fveq2d', '( log ` ( %s + 1 ) ) = ( log ` N )' % NM)], 'oveq2d', '%s = %s' % (WL('( %s + 1 )' % NM), WL('N')))],
                       'oveq2d', '( %s - %s ) = ( %s - %s )' % (WL('2'), WL('( %s + 1 )' % NM), WL('2'), WL('N')))], 'eqtrd',
            '%s = ( %s - %s )' % (SD, WL('2'), WL('N')))
    t2 = st([tel2, st([st([st([npc], 'fveq2d', '( log ` ( %s + 1 ) ) = ( log ` N )' % NM)], 'fveq2d', '%s = %s' % (LL('( %s + 1 )' % NM), LL('N')))],
                       'oveq1d', '( %s - %s ) = ( %s - %s )' % (LL('( %s + 1 )' % NM), LL('2'), LL('N'), LL('2')))], 'eqtrd',
            '%s = ( %s - %s )' % (SV, LL('N'), LL('2')))
    sc2 = st([st([mul], 'eqcomd', '%s = ( %s x. %s )' % (SC, C4, SD)), st([t1], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s - %s ) )' % (C4, SD, C4, WL('2'), WL('N')))],
             'eqtrd', '%s = ( %s x. ( %s - %s ) )' % (SC, C4, WL('2'), WL('N')))
    fin2 = st([add, st([t2, sc2], 'oveq12d', '( %s + %s ) = ( ( %s - %s ) + ( %s x. ( %s - %s ) ) )' % (SV, SC, LL('N'), LL('2'), C4, WL('2'), WL('N')))],
              'eqtrd', '%s = ( ( %s - %s ) + ( %s x. ( %s - %s ) ) )' % (SR, LL('N'), LL('2'), C4, WL('2'), WL('N')))
    w.qed([le1, fin2], 'breqtrd', '( %s -> %s <_ ( ( %s - %s ) + ( %s x. ( %s - %s ) ) ) )' % (PH, SL, LL('N'), LL('2'), C4, WL('2'), WL('N')))
    return w


def zdmpsum():
    w = W('zdmpsum', 'Mertens second theorem, upper form with explicit constant: the sum of the '
                     'reciprocals of the primes up to N is at most log log N + ( 1 + 2 ( log 4 + 4 ) / log 2 - log log 2 ) '
                     '(Lean sum_prime_inv_le).')
    PH = 'N e. ( ZZ>= ` 2 )'
    st = mkst(w, PH)
    nu = st([], 'id', PH)
    nnn, nz, nre, ncc, n1, n2 = uz2facts(w, PH, nu, 'N')
    one = st([], '1red', '1 e. RR')
    BODY = lambda v: '( %s x. %s )' % (WL(v), LAM(v))
    DW = lambda v: '( %s - %s )' % (WL(v), WL(P1(v)))
    SP = 'sum_ p e. %s ( 1 / p )' % PR('N')
    SF = 'sum_ i e. ( 2 ... N ) %s' % BODY('i')
    S4 = 'sum_ i e. ( 2 ... ( N - 1 ) ) ( %s x. %s )' % (DW('i'), T('i'))
    WT = '( %s x. %s )' % (WL('N'), T('N'))
    s1 = st([], 'zdmpsum1', '%s <_ %s' % (SP, SF))
    ab = st([], 'zdmabel', '%s = ( %s + %s )' % (SF, WT, S4))
    s3 = st([], 'zdmpsum3', '%s <_ ( ( %s - %s ) + ( %s x. ( %s - %s ) ) )' % (S4, LL('N'), LL('2'), C4, WL('2'), WL('N')))
    # W(N) T(N) <_ 1 + c W(N)
    lnrp, wnrp, wnr, wnc = wfacts(w, PH, 'N', nre, n1)
    l2rp = w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2'), w.inst('rplogcl')], 'mp2an', '( log ` 2 ) e. RR+')
    l2d = st([l2rp], 'a1i', '( log ` 2 ) e. RR+')
    w2rp = st([l2d], 'rpreccld', '%s e. RR+' % WL('2'))
    w2r = st([w2rp], 'rpred', '%s e. RR' % WL('2'))
    tre, tcc = tcl(w, PH, 'N')
    ige1 = linarith(w, PH, [n1], '1 <_ N', leaves={'N': nre})
    LN = '( log ` N )'
    m1 = sy2(w, PH, nre, ige1, 'mertens1le', '%s <_ ( %s + %s )' % (T('( |_ ` N )'), LN, C4))
    fl = sy(w, PH, nz, 'flid', '( |_ ` N ) = N')
    tle = st([st([st([fl], 'oveq2d', '( 1 ... ( |_ ` N ) ) = ( 1 ... N )')], 'sumeq1d', '%s = %s' % (T('( |_ ` N )'), T('N'))), m1], 'eqbrtrrd',
             '%s <_ ( %s + %s )' % (T('N'), LN, C4))
    c4r = w.s([w.s([w.s([], '4rp', '4 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 4 ) e. RR'), w.s([], '4re', '4 e. RR')], 'readdcli', '%s e. RR' % C4)
    c4d = st([c4r], 'a1i', '%s e. RR' % C4); c4c = st([c4d], 'recnd', '%s e. CC' % C4)
    l4ge = w.s([w.s([], '4re', '4 e. RR'), w.s([w.s([], '1re', '1 e. RR'), w.s([], '4re', '4 e. RR'), w.s([], '1lt4', '1 < 4')], 'ltleii', '1 <_ 4'), w.inst('logge0')],
               'mp2an', '0 <_ ( log ` 4 )')
    c4ge = linarith(w, PH, [st([l4ge], 'a1i', '0 <_ ( log ` 4 )')], '0 <_ %s' % C4, leaves={'( log ` 4 )': st([w.s([w.s([], '4rp', '4 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 4 ) e. RR')], 'a1i', '( log ` 4 ) e. RR')})
    lnr = st([lnrp], 'rpred', '%s e. RR' % LN); lnc = st([lnrp], 'rpcnd', '%s e. CC' % LN); lnne = st([lnrp], 'rpne0d', '%s =/= 0' % LN)
    sumr = st([lnr, c4d], 'readdcld', '( %s + %s ) e. RR' % (LN, C4))
    wt1 = st([tre, sumr, wnr, st([wnrp], 'rpge0d', '0 <_ %s' % WL('N')), tle], 'lemul2ad', '%s <_ ( %s x. ( %s + %s ) )' % (WT, WL('N'), LN, C4))
    CWN = '( %s x. %s )' % (WL('N'), C4)
    wt2 = st([st([wnc, lnc, c4c], 'adddid', '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + %s )' % (WL('N'), LN, C4, WL('N'), LN, CWN)),
              st([st([lnc, lnne], 'recid2d', '( %s x. %s ) = 1' % (WL('N'), LN))], 'oveq1d', '( ( %s x. %s ) + %s ) = ( 1 + %s )' % (WL('N'), LN, CWN, CWN))],
             'eqtrd', '( %s x. ( %s + %s ) ) = ( 1 + %s )' % (WL('N'), LN, C4, CWN))
    # W(N) <_ W(2) and c W(N) <_ c W(2) = c / log 2
    l2le = st([linarith(w, PH, [n2], '2 <_ N', leaves={'N': nre}), sy2(w, PH, st([clo(w, '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), st([nre, linarith(w, PH, [n1], '0 < N', leaves={'N': nre})], 'elrpd', 'N e. RR+'),
                                                                        'logleb', '( 2 <_ N <-> ( log ` 2 ) <_ %s )' % LN)], 'mpbid', '( log ` 2 ) <_ %s' % LN)
    wle = st([l2le, st([l2d, lnrp], 'lerecd', '( ( log ` 2 ) <_ %s <-> %s <_ %s )' % (LN, WL('N'), WL('2')))], 'mpbid', '%s <_ %s' % (WL('N'), WL('2')))
    CW2 = '( %s x. %s )' % (WL('N'), C4)
    K = '( %s / ( log ` 2 ) )' % C4
    cwle = st([wnr, w2r, c4d, c4ge, wle], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (WL('N'), C4, WL('2'), C4))
    keq = st([st([c4c, st([l2d], 'rpcnd', '( log ` 2 ) e. CC'), st([l2d], 'rpne0d', '( log ` 2 ) =/= 0')], 'divrecd', '%s = ( %s x. %s )' % (K, C4, WL('2'))),
              st([c4c, st([w2rp], 'rpcnd', '%s e. CC' % WL('2'))], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (C4, WL('2'), WL('2'), C4))], 'eqtrd',
             '%s = ( %s x. %s )' % (K, WL('2'), C4))
    # c ( W(2) - W(N) ) = K - CWN
    cdist = st([c4c, st([w2rp], 'rpcnd', '%s e. CC' % WL('2')), wnc], 'subdid', '( %s x. ( %s - %s ) ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (C4, WL('2'), WL('N'), C4, WL('2'), C4, WL('N')))
    cm1 = st([c4c, st([w2rp], 'rpcnd', '%s e. CC' % WL('2'))], 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (C4, WL('2'), WL('2'), C4))
    cm2 = st([c4c, wnc], 'mulcomd', '( %s x. %s ) = %s' % (C4, WL('N'), CWN))
    cdist2 = st([cdist, st([cm1, cm2], 'oveq12d', '( ( %s x. %s ) - ( %s x. %s ) ) = ( ( %s x. %s ) - %s )' % (C4, WL('2'), C4, WL('N'), WL('2'), C4, CWN))], 'eqtrd',
                '( %s x. ( %s - %s ) ) = ( ( %s x. %s ) - %s )' % (C4, WL('2'), WL('N'), WL('2'), C4, CWN))
    cwn0 = st([wnr, c4d, st([wnrp], 'rpge0d', '0 <_ %s' % WL('N')), c4ge], 'mulge0d', '0 <_ %s' % CWN)
    # 2c / log 2 = 2 K
    k2 = st([st([clo(w, '2cn', '2 e. CC')], 'a1i', '2 e. CC'), c4c, st([l2d], 'rpcnd', '( log ` 2 ) e. CC'), st([l2d], 'rpne0d', '( log ` 2 ) =/= 0')], 'divassd',
            '( ( 2 x. %s ) / ( log ` 2 ) ) = ( 2 x. %s )' % (C4, K))
    # closures for linarith
    AP = '( %s /\\ p e. %s )' % (PH, PR('N'))
    sp = mkst(w, AP)
    pnn = sy(w, AP, sy(w, AP, sp([], 'simpr', 'p e. %s' % PR('N')), 'elinel2', 'p e. Prime'), 'prmnn', 'p e. NN')
    prfin = st([st([], 'fzfid', '( 1 ... N ) e. Fin'), st([clo(w, 'inss1', '%s C_ ( 1 ... N )' % PR('N'))], 'a1i', '%s C_ ( 1 ... N )' % PR('N'))], 'ssfid', '%s e. Fin' % PR('N'))
    spr = st([prfin, sp([pnn], 'nnrecred', '( 1 / p ) e. RR')], 'fsumrecl', '%s e. RR' % SP)
    AI = '( %s /\\ i e. ( 2 ... N ) )' % PH
    si = mkst(w, AI)
    iu = sy(w, AI, si([], 'simpr', 'i e. ( 2 ... N )'), 'elfzuz', 'i e. ( ZZ>= ` 2 )')
    inn, iz, ire, icc, i1, i2 = uz2facts(w, AI, iu, 'i')
    _, _, wir, _ = wfacts(w, AI, 'i', ire, i1)
    sfr = st([st([], 'fzfid', '( 2 ... N ) e. Fin'), si([wir, si([sy(w, AI, inn, 'vmacl', '( Lam ` i ) e. RR'), si([inn], 'nnrpd', 'i e. RR+')], 'rerpdivcld', '%s e. RR' % LAM('i'))], 'remulcld', '%s e. RR' % BODY('i'))],
             'fsumrecl', '%s e. RR' % SF)
    AI2 = '( %s /\\ i e. ( 2 ... ( N - 1 ) ) )' % PH
    si2 = mkst(w, AI2)
    iu2 = sy(w, AI2, si2([], 'simpr', 'i e. ( 2 ... ( N - 1 ) )'), 'elfzuz', 'i e. ( ZZ>= ` 2 )')
    inn2, iz2, ire2, icc2, i12, i22 = uz2facts(w, AI2, iu2, 'i')
    _, _, wir2, _ = wfacts(w, AI2, 'i', ire2, i12)
    ipre2 = si2([ire2, lift(w, one, AI2)], 'readdcld', '( i + 1 ) e. RR')
    _, _, wipr2, _ = wfacts(w, AI2, P1('i'), ipre2, linarith(w, AI2, [i12], '1 < ( i + 1 )', leaves={'i': ire2}))
    tir2, _ = tcl(w, AI2, 'i')
    s4r = st([st([], 'fzfid', '( 2 ... ( N - 1 ) ) e. Fin'), si2([si2([wir2, wipr2], 'resubcld', '%s e. RR' % DW('i')), tir2], 'remulcld', '( %s x. %s ) e. RR' % (DW('i'), T('i')))],
             'fsumrecl', '%s e. RR' % S4)
    wtr = st([wnr, tre], 'remulcld', '%s e. RR' % WT)
    lln = st([lnrp], 'relogcld', '%s e. RR' % LL('N')); ll2 = st([l2d], 'relogcld', '%s e. RR' % LL('2'))
    cwnr = st([wnr, c4d], 'remulcld', '%s e. RR' % CWN)
    w2c4 = st([w2r, c4d], 'remulcld', '( %s x. %s ) e. RR' % (WL('2'), C4))
    kr = st([c4d, l2d], 'rerpdivcld', '%s e. RR' % K)
    cd2 = st([c4d, st([w2r, wnr], 'resubcld', '( %s - %s ) e. RR' % (WL('2'), WL('N')))], 'remulcld', '( %s x. ( %s - %s ) ) e. RR' % (C4, WL('2'), WL('N')))
    twok = st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), c4d], 'remulcld', '( 2 x. %s ) e. RR' % C4)
    tk = st([twok, l2d], 'rerpdivcld', '( ( 2 x. %s ) / ( log ` 2 ) ) e. RR' % C4)
    qr = st([wnr, sumr], 'remulcld', '( %s x. ( %s + %s ) ) e. RR' % (WL('N'), LN, C4))
    leaves = {SP: spr, SF: sfr, S4: s4r, WT: wtr, LL('N'): lln, LL('2'): ll2, CWN: cwnr, '( %s x. %s )' % (WL('2'), C4): w2c4, K: kr,
              '( %s x. ( %s - %s ) )' % (C4, WL('2'), WL('N')): cd2, '( ( 2 x. %s ) / ( log ` 2 ) )' % C4: tk,
              '( %s x. ( %s + %s ) )' % (WL('N'), LN, C4): qr}
    goal = '%s <_ ( %s + ( ( 1 + ( ( 2 x. %s ) / ( log ` 2 ) ) ) - %s ) )' % (SP, LL('N'), C4, LL('2'))
    linarith(w, PH, [s1, ab, s3, wt1, wt2, cwle, keq, cdist2, cwn0, k2], goal, leaves=leaves, name='qed')
    return w



PRODM = lambda N: 'prod_ p e. %s ( 1 / ( 1 - ( 1 / p ) ) )' % PR(N)
KM = '( ( 3 + ( ( 2 x. %s ) / ( log ` 2 ) ) ) - %s )' % (C4, LL('2'))


def c4facts(w, ante):
    st = mkst(w, ante)
    c4r = w.s([w.s([w.s([], '4rp', '4 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 4 ) e. RR'), w.s([], '4re', '4 e. RR')], 'readdcli', '%s e. RR' % C4)
    l2rp = w.s([w.s([], '2re', '2 e. RR'), w.s([], '1lt2', '1 < 2'), w.inst('rplogcl')], 'mp2an', '( log ` 2 ) e. RR+')
    c4d = st([c4r], 'a1i', '%s e. RR' % C4)
    l2d = st([l2rp], 'a1i', '( log ` 2 ) e. RR+')
    tk = st([st([st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR'), c4d], 'remulcld', '( 2 x. %s ) e. RR' % C4), l2d], 'rerpdivcld',
            '( ( 2 x. %s ) / ( log ` 2 ) ) e. RR' % C4)
    ll2 = st([l2d], 'relogcld', '%s e. RR' % LL('2'))
    kr = st([st([st([clo(w, '3re', '3 e. RR')], 'a1i', '3 e. RR'), tk], 'readdcld', '( 3 + ( ( 2 x. %s ) / ( log ` 2 ) ) ) e. RR' % C4), ll2], 'resubcld', '%s e. RR' % KM)
    return c4d, l2d, tk, ll2, kr


def zdmertlem1():
    w = W('zdmertlem1', 'The Mertens product up to N is at most exp of the prime reciprocal sum plus 2 '
                        '(termwise zdminv, then the reciprocal squares sum to at most 1).')
    PH = 'N e. ( ZZ>= ` 2 )'
    st = mkst(w, PH)
    nu = st([], 'id', PH)
    nnn, nz, nre, ncc, n1, n2 = uz2facts(w, PH, nu, 'N')
    X = '( 1 / p )'
    BODY = lambda v: '( ( 1 / %s ) + ( 2 x. ( ( 1 / %s ) ^ 2 ) ) )' % (v, v)
    AP = '( %s /\\ p e. %s )' % (PH, PR('N'))
    sp = mkst(w, AP)
    pel = sp([], 'simpr', 'p e. %s' % PR('N'))
    pp = sy(w, AP, pel, 'elinel2', 'p e. Prime')
    pu = sy(w, AP, pp, 'prmuz2', 'p e. ( ZZ>= ` 2 )')
    pnn, pz, pre, pcc, p1, p2 = uz2facts(w, AP, pu, 'p')
    prp = sp([pnn], 'nnrpd', 'p e. RR+')
    xrp = sp([prp], 'rpreccld', '%s e. RR+' % X)
    xr = sp([xrp], 'rpred', '%s e. RR' % X); x0 = sp([xrp], 'rpge0d', '0 <_ %s' % X)
    xh = sp([p2, sp([sp([clo(w, '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), prp], 'lerecd', '( 2 <_ p <-> %s <_ ( 1 / 2 ) )' % X)], 'mpbid', '%s <_ ( 1 / 2 )' % X)
    inv = sy3(w, AP, xr, x0, xh, 'zdminv', '( 1 / ( 1 - %s ) ) <_ ( exp ` %s )' % (X, BODY('p')))
    one = sp([], '1red', '1 e. RR')
    mx = sp([one, xr], 'resubcld', '( 1 - %s ) e. RR' % X)
    mxrp = sp([mx, linarith(w, AP, [xh], '0 < ( 1 - %s )' % X, leaves={X: xr})], 'elrpd', '( 1 - %s ) e. RR+' % X)
    brp = sp([mxrp], 'rpreccld', '( 1 / ( 1 - %s ) ) e. RR+' % X)
    bre = sp([brp], 'rpred', '( 1 / ( 1 - %s ) ) e. RR' % X); bge = sp([brp], 'rpge0d', '0 <_ ( 1 / ( 1 - %s ) )' % X)
    x2r = sp([xr], 'resqcld', '( %s ^ 2 ) e. RR' % X)
    two = sp([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR')
    bodyr = sp([xr, sp([two, x2r], 'remulcld', '( 2 x. ( %s ^ 2 ) ) e. RR' % X)], 'readdcld', '%s e. RR' % BODY('p'))
    cre = sp([bodyr], 'reefcld', '( exp ` %s ) e. RR' % BODY('p'))
    prfin = st([st([], 'fzfid', '( 1 ... N ) e. Fin'), st([clo(w, 'inss1', '%s C_ ( 1 ... N )' % PR('N'))], 'a1i', '%s C_ ( 1 ... N )' % PR('N'))], 'ssfid', '%s e. Fin' % PR('N'))
    nf = w.s([], 'nfv', 'F/ p %s' % PH)
    PE = 'prod_ p e. %s ( exp ` %s )' % (PR('N'), BODY('p'))
    ple = st([nf, prfin, bre, bge, cre, inv], 'fprodle', '%s <_ %s' % (PRODM('N'), PE))
    # product of exps = exp of sum
    F = '( t e. %s |-> %s )' % (PR('N'), BODY('t'))
    fv, _ = mpv(w, AP, 't', PR('N'), BODY('t'), 'p', pel)
    fvc = sp([fv, sp([bodyr], 'recnd', '%s e. CC' % BODY('p'))], 'eqeltrd', '( %s ` p ) e. CC' % F)
    pes = st([prfin, fvc], 'fprodefsumfi', 'prod_ p e. %s ( exp ` ( %s ` p ) ) = ( exp ` sum_ p e. %s ( %s ` p ) )' % (PR('N'), F, PR('N'), F))
    SB = 'sum_ p e. %s %s' % (PR('N'), BODY('p'))
    pe1 = st([sp([fv], 'fveq2d', '( exp ` ( %s ` p ) ) = ( exp ` %s )' % (F, BODY('p')))], 'prodeq2dv', 'prod_ p e. %s ( exp ` ( %s ` p ) ) = %s' % (PR('N'), F, PE))
    se1 = st([fv], 'sumeq2dv', 'sum_ p e. %s ( %s ` p ) = %s' % (PR('N'), F, SB))
    peq = st([st([pe1], 'eqcomd', '%s = prod_ p e. %s ( exp ` ( %s ` p ) )' % (PE, PR('N'), F)), st([pes, st([se1], 'fveq2d', '( exp ` sum_ p e. %s ( %s ` p ) ) = ( exp ` %s )' % (PR('N'), F, SB))], 'eqtrd',
                 'prod_ p e. %s ( exp ` ( %s ` p ) ) = ( exp ` %s )' % (PR('N'), F, SB))], 'eqtrd', '%s = ( exp ` %s )' % (PE, SB))
    # the sum
    SP = 'sum_ p e. %s ( 1 / p )' % PR('N')
    SQ = 'sum_ p e. %s ( ( 1 / p ) ^ 2 )' % PR('N')
    S2Q = 'sum_ p e. %s ( 2 x. ( ( 1 / p ) ^ 2 ) )' % PR('N')
    add = st([prfin, sp([xr], 'recnd', '%s e. CC' % X), sp([sp([two, x2r], 'remulcld', '( 2 x. ( %s ^ 2 ) ) e. RR' % X)], 'recnd', '( 2 x. ( %s ^ 2 ) ) e. CC' % X)], 'fsumadd',
             '%s = ( %s + %s )' % (SB, SP, S2Q))
    mul = st([prfin, st([clo(w, '2cn', '2 e. CC')], 'a1i', '2 e. CC'), sp([x2r], 'recnd', '( %s ^ 2 ) e. CC' % X)], 'fsummulc2', '( 2 x. %s ) = %s' % (SQ, S2Q))
    A2 = '( %s /\\ p e. ( 2 ... N ) )' % PH
    s2 = mkst(w, A2)
    pu2 = sy(w, A2, s2([], 'simpr', 'p e. ( 2 ... N )'), 'elfzuz', 'p e. ( ZZ>= ` 2 )')
    pnn2, pz2, pre2, pcc2, p12, p22 = uz2facts(w, A2, pu2, 'p')
    x2r2 = s2([s2([s2([pnn2], 'nnrpd', 'p e. RR+')], 'rprecred', '( 1 / p ) e. RR')], 'resqcld', '( ( 1 / p ) ^ 2 ) e. RR')
    x2g2 = s2([s2([s2([pnn2], 'nnrpd', 'p e. RR+')], 'rprecred', '( 1 / p ) e. RR')], 'sqge0d', '0 <_ ( ( 1 / p ) ^ 2 )')
    less = st([st([], 'fzfid', '( 2 ... N ) e. Fin'), x2r2, x2g2, st([clo(w, 'zdmprss', '%s C_ ( 2 ... N )' % PR('N'))], 'a1i', '%s C_ ( 2 ... N )' % PR('N'))], 'fsumless',
              '%s <_ sum_ p e. ( 2 ... N ) ( ( 1 / p ) ^ 2 )' % SQ)
    cb = w.s([w.s([w.s([], 'oveq2', '( p = n -> ( 1 / p ) = ( 1 / n ) )')], 'oveq1d', '( p = n -> ( ( 1 / p ) ^ 2 ) = ( ( 1 / n ) ^ 2 ) )')], 'cbvsumv',
             'sum_ p e. ( 2 ... N ) ( ( 1 / p ) ^ 2 ) = sum_ n e. ( 2 ... N ) ( ( 1 / n ) ^ 2 )')
    isq = sy(w, PH, nnn, 'zdmisq', 'sum_ n e. ( 2 ... N ) ( ( 1 / n ) ^ 2 ) <_ 1')
    sqr = st([prfin, sp([xr], 'resqcld', '( %s ^ 2 ) e. RR' % X)], 'fsumrecl', '%s e. RR' % SQ)
    less2 = st([less, st([cb], 'a1i', 'sum_ p e. ( 2 ... N ) ( ( 1 / p ) ^ 2 ) = sum_ n e. ( 2 ... N ) ( ( 1 / n ) ^ 2 )')], 'breqtrd',
               '%s <_ sum_ n e. ( 2 ... N ) ( ( 1 / n ) ^ 2 )' % SQ)
    AN = '( %s /\\ n e. ( 2 ... N ) )' % PH
    sn = mkst(w, AN)
    nnn2 = sy(w, AN, sy(w, AN, sn([], 'simpr', 'n e. ( 2 ... N )'), 'elfzuz', 'n e. ( ZZ>= ` 2 )'), 'eluz2nn', 'n e. NN')
    snr = st([st([], 'fzfid', '( 2 ... N ) e. Fin'), sn([sn([sn([nnn2], 'nnrpd', 'n e. RR+')], 'rprecred', '( 1 / n ) e. RR')], 'resqcld', '( ( 1 / n ) ^ 2 ) e. RR')], 'fsumrecl',
             'sum_ n e. ( 2 ... N ) ( ( 1 / n ) ^ 2 ) e. RR')
    sqle = st([sqr, snr, st([], '1red', '1 e. RR'), less2, isq], 'letrd', '%s <_ 1' % SQ)
    spr = st([prfin, xr], 'fsumrecl', '%s e. RR' % SP)
    sbr = st([prfin, bodyr], 'fsumrecl', '%s e. RR' % SB)
    s2qr = st([prfin, sp([two, x2r], 'remulcld', '( 2 x. ( %s ^ 2 ) ) e. RR' % X)], 'fsumrecl', '%s e. RR' % S2Q)
    ele = linarith(w, PH, [add, mul, sqle], '%s <_ ( %s + 2 )' % (SB, SP), leaves={SP: spr, SB: sbr, SQ: sqr, S2Q: s2qr})
    sp2r = st([spr, st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '( %s + 2 ) e. RR' % SP)
    efl = st([ele, st([sbr, sp2r, w.inst('efle')], 'syl2anc', '( %s <_ ( %s + 2 ) <-> ( exp ` %s ) <_ ( exp ` ( %s + 2 ) ) )' % (SB, SP, SB, SP))], 'mpbid',
             '( exp ` %s ) <_ ( exp ` ( %s + 2 ) )' % (SB, SP))
    per = st([prfin, bre], 'fprodrecl', '%s e. RR' % PRODM('N'))
    pee = st([prfin, cre], 'fprodrecl', '%s e. RR' % PE)
    esb = st([sbr], 'reefcld', '( exp ` %s ) e. RR' % SB)
    esp = st([sp2r], 'reefcld', '( exp ` ( %s + 2 ) ) e. RR' % SP)
    ch1 = st([ple, peq], 'breqtrd', '%s <_ ( exp ` %s )' % (PRODM('N'), SB))
    w.qed([per, esb, esp, ch1, efl], 'letrd', '( %s -> %s <_ ( exp ` ( %s + 2 ) ) )' % (PH, PRODM('N'), SP))
    return w


def zdmert():
    w = W('zdmert', 'Mertens third theorem, upper bound with explicit constant: the product of '
                    '1 / ( 1 - 1 / p ) over the primes up to R is at most CM log R with '
                    'CM = exp ( 3 + 2 ( log 4 + 4 ) / log 2 - log log 2 ) (Lean mertensProd_le_log).')
    PH = '( R e. RR /\\ 2 <_ R )'
    st = mkst(w, PH)
    rre = st([], 'simpl', 'R e. RR'); r2 = st([], 'simpr', '2 <_ R')
    N = '( |_ ` R )'
    nz = sy(w, PH, rre, 'flcl', '%s e. ZZ' % N)
    n2 = st([r2, sy2(w, PH, rre, st([clo(w, '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), 'flge', '( 2 <_ R <-> 2 <_ %s )' % N)], 'mpbid', '2 <_ %s' % N)
    nu = st([st([st([clo(w, '2z', '2 e. ZZ')], 'a1i', '2 e. ZZ'), nz, n2], '3jca', '( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s )' % (N, N)),
             st([clo(w, 'eluz2', '( %s e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s ) )' % (N, N, N))], 'a1i',
                '( %s e. ( ZZ>= ` 2 ) <-> ( 2 e. ZZ /\\ %s e. ZZ /\\ 2 <_ %s ) )' % (N, N, N))], 'mpbird', '%s e. ( ZZ>= ` 2 )' % N)
    nnn, _, nre, ncc, n1, _ = uz2facts(w, PH, nu, N)
    SP = 'sum_ p e. %s ( 1 / p )' % PR(N)
    l1 = sy(w, PH, nu, 'zdmertlem1', '%s <_ ( exp ` ( %s + 2 ) )' % (PRODM(N), SP))
    c4d, l2d, tk, ll2, kr = c4facts(w, PH)
    ps = sy(w, PH, nu, 'zdmpsum', '%s <_ ( %s + ( ( 1 + ( ( 2 x. %s ) / ( log ` 2 ) ) ) - %s ) )' % (SP, LL(N), C4, LL('2')))
    # log log N <_ log log R
    nrp = st([nre, linarith(w, PH, [n1], '0 < %s' % N, leaves={N: nre})], 'elrpd', '%s e. RR+' % N)
    rrp = st([rre, linarith(w, PH, [r2], '0 < R', leaves={'R': rre})], 'elrpd', 'R e. RR+')
    nler = sy(w, PH, rre, 'flle', '%s <_ R' % N)
    lnlr = st([nler, sy2(w, PH, nrp, rrp, 'logleb', '( %s <_ R <-> ( log ` %s ) <_ ( log ` R ) )' % (N, N))], 'mpbid', '( log ` %s ) <_ ( log ` R )' % N)
    lnrp = sy2(w, PH, nre, n1, 'rplogcl', '( log ` %s ) e. RR+' % N)
    lrrp = sy2(w, PH, rre, linarith(w, PH, [r2], '1 < R', leaves={'R': rre}), 'rplogcl', '( log ` R ) e. RR+')
    lll = st([lnlr, sy2(w, PH, lnrp, lrrp, 'logleb', '( ( log ` %s ) <_ ( log ` R ) <-> %s <_ %s )' % (N, LL(N), LL('R')))], 'mpbid', '%s <_ %s' % (LL(N), LL('R')))
    # exponent bound
    AP = '( %s /\\ p e. %s )' % (PH, PR(N))
    sp = mkst(w, AP)
    pnn = sy(w, AP, sy(w, AP, sp([], 'simpr', 'p e. %s' % PR(N)), 'elinel2', 'p e. Prime'), 'prmnn', 'p e. NN')
    prfin = st([st([], 'fzfid', '( 1 ... %s ) e. Fin' % N), st([clo(w, 'inss1', '%s C_ ( 1 ... %s )' % (PR(N), N))], 'a1i', '%s C_ ( 1 ... %s )' % (PR(N), N))], 'ssfid', '%s e. Fin' % PR(N))
    spr = st([prfin, sp([pnn], 'nnrecred', '( 1 / p ) e. RR')], 'fsumrecl', '%s e. RR' % SP)
    lln = st([lnrp], 'relogcld', '%s e. RR' % LL(N)); llr = st([lrrp], 'relogcld', '%s e. RR' % LL('R'))
    E1 = '( %s + 2 )' % SP
    E2 = '( %s + %s )' % (LL('R'), KM)
    ele = linarith(w, PH, [ps, lll], '%s <_ %s' % (E1, E2), leaves={SP: spr, LL(N): lln, LL('R'): llr, LL('2'): ll2, '( ( 2 x. %s ) / ( log ` 2 ) )' % C4: tk})
    e1r = st([spr, st([clo(w, '2re', '2 e. RR')], 'a1i', '2 e. RR')], 'readdcld', '%s e. RR' % E1)
    e2r = st([llr, kr], 'readdcld', '%s e. RR' % E2)
    efl = st([ele, st([e1r, e2r, w.inst('efle')], 'syl2anc', '( %s <_ %s <-> ( exp ` %s ) <_ ( exp ` %s ) )' % (E1, E2, E1, E2))], 'mpbid',
             '( exp ` %s ) <_ ( exp ` %s )' % (E1, E2))
    ea = sy2(w, PH, st([llr], 'recnd', '%s e. CC' % LL('R')), st([kr], 'recnd', '%s e. CC' % KM), 'efadd',
             '( exp ` %s ) = ( ( exp ` %s ) x. ( exp ` %s ) )' % (E2, LL('R'), KM))
    rl = sy(w, PH, lrrp, 'reeflog', '( exp ` %s ) = ( log ` R )' % LL('R'))
    ea2 = st([ea, st([st([rl], 'oveq1d', '( ( exp ` %s ) x. ( exp ` %s ) ) = ( ( log ` R ) x. ( exp ` %s ) )' % (LL('R'), KM, KM)),
                      st([st([lrrp], 'rpcnd', '( log ` R ) e. CC'), st([st([kr], 'reefcld', '( exp ` %s ) e. RR' % KM)], 'recnd', '( exp ` %s ) e. CC' % KM)], 'mulcomd',
                         '( ( log ` R ) x. ( exp ` %s ) ) = ( ( exp ` %s ) x. ( log ` R ) )' % (KM, KM))], 'eqtrd',
                     '( ( exp ` %s ) x. ( exp ` %s ) ) = ( ( exp ` %s ) x. ( log ` R ) )' % (LL('R'), KM, KM))], 'eqtrd',
              '( exp ` %s ) = ( ( exp ` %s ) x. ( log ` R ) )' % (E2, KM))
    pu = sy(w, AP, sy(w, AP, sp([], 'simpr', 'p e. %s' % PR(N)), 'elinel2', 'p e. Prime'), 'prmuz2', 'p e. ( ZZ>= ` 2 )')
    _, _, _, _, _, p2 = uz2facts(w, AP, pu, 'p')
    prp = sp([pnn], 'nnrpd', 'p e. RR+')
    xh = sp([p2, sp([sp([clo(w, '2rp', '2 e. RR+')], 'a1i', '2 e. RR+'), prp], 'lerecd', '( 2 <_ p <-> ( 1 / p ) <_ ( 1 / 2 ) )')], 'mpbid', '( 1 / p ) <_ ( 1 / 2 )')
    xr = sp([prp], 'rprecred', '( 1 / p ) e. RR')
    mxr = sp([sp([], '1red', '1 e. RR'), xr], 'resubcld', '( 1 - ( 1 / p ) ) e. RR')
    mxrp = sp([mxr, linarith(w, AP, [xh], '0 < ( 1 - ( 1 / p ) )', leaves={'( 1 / p )': xr})], 'elrpd', '( 1 - ( 1 / p ) ) e. RR+')
    bre = sp([sp([mxrp], 'rpreccld', '( 1 / ( 1 - ( 1 / p ) ) ) e. RR+')], 'rpred', '( 1 / ( 1 - ( 1 / p ) ) ) e. RR')
    per = st([prfin, bre], 'fprodrecl', '%s e. RR' % PRODM(N))
    ee1 = st([e1r], 'reefcld', '( exp ` %s ) e. RR' % E1)
    ee2 = st([e2r], 'reefcld', '( exp ` %s ) e. RR' % E2)
    ch = st([per, ee1, ee2, l1, efl], 'letrd', '%s <_ ( exp ` %s )' % (PRODM(N), E2))
    w.qed([ch, ea2], 'breqtrd', '( %s -> %s <_ ( ( exp ` %s ) x. ( log ` R ) ) )' % (PH, PRODM(N), KM))
    return w


def zdmert2():
    w = W('zdmert2', 'zdmert with the primes up to R written as ( ( 0 [,] R ) i^i Prime ) (Z0 section 3.7).')
    PH = '( R e. RR /\\ 2 <_ R )'
    st = mkst(w, PH)
    N = '( |_ ` R )'
    rre = st([], 'simpl', 'R e. RR')
    two = w.s([w.s([], '2nn', '2 e. NN'), w.s([], 'nnuz', NNUZ)], 'eleqtri', '2 e. ( ZZ>= ` 1 )')
    seq = sy2(w, PH, rre, st([two], 'a1i', '2 e. ( ZZ>= ` 1 )'), 'ppisval2', '( ( 0 [,] R ) i^i Prime ) = %s' % PR(N))
    pe = st([seq], 'prodeq1d', 'prod_ p e. ( ( 0 [,] R ) i^i Prime ) ( 1 / ( 1 - ( 1 / p ) ) ) = %s' % PRODM(N))
    w.qed([pe, st([], 'zdmert', '%s <_ ( ( exp ` %s ) x. ( log ` R ) )' % (PRODM(N), KM))], 'eqbrtrd',
          '( %s -> prod_ p e. ( ( 0 [,] R ) i^i Prime ) ( 1 / ( 1 - ( 1 / p ) ) ) <_ ( ( exp ` %s ) x. ( log ` R ) ) )' % (PH, KM))
    return w


def zdmhyp():
    w = W('zdmhyp', 'MertensHyp of ZeroDensity.lean discharged: there is a nonnegative constant c with '
                    'the Mertens product up to r at most c log r for every real r >= 2.')
    EK = '( exp ` %s )' % KM
    PRR = PRODM('( |_ ` r )')
    INNER = lambda c: 'A. r e. RR ( 2 <_ r -> %s <_ ( %s x. ( log ` r ) ) )' % (PRR, c)
    BODY = lambda c: '( 0 <_ %s /\\ %s )' % (c, INNER(c))
    c4d, l2d, tk, ll2, kr = c4facts(w, 'T.')
    krt = w.s([w.s([], 'tru', 'T.'), kr], 'ax-mp', '%s e. RR' % KM)
    ekr = w.s([krt, w.inst('reefcl')], 'ax-mp', '%s e. RR' % EK)
    ekg = w.s([w.s([], '0re', '0 e. RR'), ekr, w.s([krt, w.inst('efgt0')], 'ax-mp', '0 < %s' % EK)], 'ltleii', '0 <_ %s' % EK)
    A = '( r e. RR /\\ 2 <_ r )'
    z = w.s([], 'zdmert', '( %s -> %s <_ ( %s x. ( log ` r ) ) )' % (A, PRR, EK))
    ze = w.s([z], 'ex', '( r e. RR -> ( 2 <_ r -> %s <_ ( %s x. ( log ` r ) ) ) )' % (PRR, EK))
    ral = w.s([ze], 'rgen', INNER(EK))
    both = w.s([ekg, ral], 'pm3.2i', BODY(EK))
    idc = w.s([], 'id', '( c = %s -> c = %s )' % (EK, EK))
    cg, _ = w.wcongr(BODY('c'), {'c': EK}, 'c = %s' % EK, {'c': idc})
    pair = w.s([ekr, both], 'pm3.2i', '( %s e. RR /\\ %s )' % (EK, BODY(EK)))
    inst = w.s([cg], 'rspcev', '( ( %s e. RR /\\ %s ) -> E. c e. RR %s )' % (EK, BODY(EK), BODY('c')))
    w.qed([pair, inst], 'ax-mp', 'E. c e. RR %s' % BODY('c'))
    return w


if __name__ == '__main__':
    for f in sys.argv[1:] or ['zdmertlem1', 'zdmert', 'zdmert2', 'zdmhyp']:
        globals()[f]().run()
