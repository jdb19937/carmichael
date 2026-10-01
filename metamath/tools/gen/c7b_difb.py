"""C7b section 1: dconvdifb (the modulus of the difference is
O ( N ^c -u ( Re Z - 1 ) ( log N + K ) ) under the log-average bound)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
lin.FASTPATH = True

N1 = '( 1 ... N )'
BZ = '( %s /\\ %s )' % (CFBB, ZP1)
ABZN = '( ( A : NN --> CC /\\ B : NN --> CC ) /\\ ( Z e. CC /\\ N e. NN ) )'


def dchctx7(w, A0):
    """A0 = ( DCH /\\ X ): the pieces of DCH"""
    lav = w.s([], 'simplll', '( %s -> %s )' % (A0, LAV()))
    cfb = w.s([], 'simpllr', '( %s -> %s )' % (A0, CFBB))
    zc2 = w.s([], 'simplr', '( %s -> ( %s /\\ seq 1 ( + , %s ) e. dom ~~> ) )' % (A0, ZP1, MAP('A')))
    zp = w.s([zc2, w.inst('simpl')], 'syl', '( %s -> %s )' % (A0, ZP1))
    cvg = w.s([zc2, w.inst('simpr')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (A0, MAP('A')))
    af = w.s([lav, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % A0)
    kr = w.s([lav, w.inst('simp2')], 'syl', '( %s -> K e. RR )' % A0)
    lal = w.s([lav, w.inst('simp3')], 'syl', '( %s -> A. y e. RR ( 1 <_ y -> sum_ d e. ( 1 ... ( |_ ` y ) ) ( ( abs ` ( A ` d ) ) / d ) <_ ( ( log ` y ) + K ) ) )' % A0)
    return dict(lav=lav, cfb=cfb, zp=zp, cvg=cvg, af=af, kr=kr, lal=lal)


def lavat(w, A0, lal, Y, yr, y1):
    """( A0 -> sum_ d e. ( 1 ... ( |_ ` Y ) ) ( ( abs ` ( A ` d ) ) / d ) <_ ( ( log ` Y ) + K ) )"""
    body = '( 1 <_ y -> sum_ d e. ( 1 ... ( |_ ` y ) ) ( ( abs ` ( A ` d ) ) / d ) <_ ( ( log ` y ) + K ) )'
    idy = w.s([], 'id', '( y = %s -> y = %s )' % (Y, Y))
    sb, new = w.wcongr(body, {'y': Y}, 'y = %s' % Y, {'y': idy})
    im = w.s([sb, lal, yr], 'rspcdva', '( %s -> %s )' % (A0, new))
    return w.s([y1, im], 'mpd', '( %s -> sum_ d e. ( 1 ... ( |_ ` %s ) ) ( ( abs ` ( A ` d ) ) / d ) <_ ( ( log ` %s ) + K ) )' % (A0, Y, Y))


if __name__ == '__main__' and (not only or 'dconvdifb' in only):
    w = W('dconvdifb', 'The difference of the convolution partial sum and the product of the partial sums is at most '
          '` ( 2 ^c ( Re Z - 1 ) C / ( Re Z - 1 ) ) N ^c -u ( Re Z - 1 ) ( log N + K ) ` under the log-average bound on ` A ` .')
    A0 = '( %s /\\ N e. NN )' % DCH
    c = dchctx7(w, A0)
    nn = w.s([], 'simpr', '( %s -> N e. NN )' % A0)
    z = zctx(w, A0, c['zp'])
    cb = cfbctx(w, A0, c['cfb'])
    c0 = w.s([c['cfb'], w.inst('cfb0')], 'syl', '( %s -> 0 <_ C )' % A0)
    PE = PS('B', '( |_ ` ( N / e ) )')
    Q = PS('B', 'N')
    TE = TRM('A', 'e')
    XE = '( %s x. ( %s - %s ) )' % (TE, PE, Q)
    abzn = w.s([w.s([c['af'], cb['bf']], 'jca', '( %s -> ( A : NN --> CC /\\ B : NN --> CC ) )' % A0), w.s([z['zc'], nn], 'jca', '( %s -> ( Z e. CC /\\ N e. NN ) )' % A0)],
               'jca', '( %s -> %s )' % (A0, ABZN))
    DIF = '( %s - ( %s x. %s ) )' % (CPS('N'), PS('A', 'N'), Q)
    dif = w.s([abzn, w.inst('dconvdif')], 'syl', '( %s -> %s = sum_ e e. %s %s )' % (A0, DIF, N1, XE))
    adif = w.s([dif], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` sum_ e e. %s %s ) )' % (A0, DIF, N1, XE))
    Ae = '( %s /\\ e e. %s )' % (A0, N1)
    em = w.s([], 'simpr', '( %s -> e e. %s )' % (Ae, N1))
    enn = w.s([em, w.inst('elfznn')], 'syl', '( %s -> e e. NN )' % Ae)
    zce = w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % Ae)
    afe = w.s([c['af']], 'adantr', '( %s -> A : NN --> CC )' % Ae)
    bfe = w.s([cb['bf']], 'adantr', '( %s -> B : NN --> CC )' % Ae)
    ae = w.s([afe, enn], 'ffvelcdmd', '( %s -> ( A ` e ) e. CC )' % Ae)
    pwe = cxpz(w, Ae, 'e', enn, zce)
    te = w.s([ae, pwe], 'mulcld', '( %s -> %s e. CC )' % (Ae, TE))

    def pscl(ante, M, bfa, zca):
        Ai = '( %s /\\ i e. ( 1 ... %s ) )' % (ante, M)
        inn = w.s([w.s([], 'simpr', '( %s -> i e. ( 1 ... %s ) )' % (Ai, M)), w.inst('elfznn')], 'syl', '( %s -> i e. NN )' % Ai)
        ti = trmcl(w, Ai, 'B', 'i', w.s([bfa], 'adantr', '( %s -> B : NN --> CC )' % Ai), inn, w.s([zca], 'adantr', '( %s -> Z e. CC )' % Ai))
        return w.s([fsumfin(w, ante, M), ti], 'fsumcl', '( %s -> %s e. CC )' % (ante, PS('B', M)))
    pe = pscl(Ae, '( |_ ` ( N / e ) )', bfe, zce)
    qe = pscl(Ae, 'N', bfe, zce)
    dpq = w.s([pe, qe], 'subcld', '( %s -> ( %s - %s ) e. CC )' % (Ae, PE, Q))
    xe = w.s([te, dpq], 'mulcld', '( %s -> %s e. CC )' % (Ae, XE))
    fin = fsumfin(w, A0, 'N')
    ab1 = w.s([fin, xe], 'fsumabs', '( %s -> ( abs ` sum_ e e. %s %s ) <_ sum_ e e. %s ( abs ` %s ) )' % (A0, N1, XE, N1, XE))
    # termwise
    a = '( abs ` ( A ` e ) )'
    p = '( e ^c -u %s )' % RZ
    s = '( abs ` ( %s - %s ) )' % (PE, Q)
    Nm = '( N ^c -u %s )' % E1
    ie = '( 1 / e )'
    ae_ = '( %s / e )' % a
    m1 = w.s([te, dpq], 'absmuld', '( %s -> ( abs ` %s ) = ( ( abs ` %s ) x. %s ) )' % (Ae, XE, TE, s))
    m2 = w.s([ae, pwe], 'absmuld', '( %s -> ( abs ` %s ) = ( %s x. ( abs ` ( e ^c -u Z ) ) ) )' % (Ae, TE, a))
    m3 = w.s([enn, zce, w.inst('cxpnnabs')], 'syl2anc', '( %s -> ( abs ` ( e ^c -u Z ) ) = %s )' % (Ae, p))
    m23 = w.s([m2, w.s([m3], 'oveq2d', '( %s -> ( %s x. ( abs ` ( e ^c -u Z ) ) ) = ( %s x. %s ) )' % (Ae, a, a, p))], 'eqtrd',
              '( %s -> ( abs ` %s ) = ( %s x. %s ) )' % (Ae, TE, a, p))
    mm = w.s([m1, w.s([m23], 'oveq1d', '( %s -> ( ( abs ` %s ) x. %s ) = ( ( %s x. %s ) x. %s ) )' % (Ae, TE, s, a, p, s))], 'eqtrd',
             '( %s -> ( abs ` %s ) = ( ( %s x. %s ) x. %s ) )' % (Ae, XE, a, p, s))
    bz = w.s([w.s([c['cfb'], c['zp']], 'jca', '( %s -> %s )' % (A0, BZ))], 'adantr', '( %s -> %s )' % (Ae, BZ))
    ndm = w.s([w.s([nn], 'adantr', '( %s -> N e. NN )' % Ae), em], 'jca', '( %s -> ( N e. NN /\\ e e. %s ) )' % (Ae, N1))
    tm = w.s([w.s([bz, ndm], 'jca', '( %s -> ( %s /\\ ( N e. NN /\\ e e. %s ) ) )' % (Ae, BZ, N1)), w.inst('dconvtm')], 'syl',
             '( %s -> ( %s x. %s ) <_ ( %s x. ( %s / e ) ) )' % (Ae, s, p, DK, Nm))
    erp = w.s([enn], 'nnrpd', '( %s -> e e. RR+ )' % Ae)
    ec = w.s([erp], 'rpcnd', '( %s -> e e. CC )' % Ae)
    en0 = w.s([erp], 'rpne0d', '( %s -> e =/= 0 )' % Ae)
    nrp = w.s([w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % A0)], 'adantr', '( %s -> N e. RR+ )' % Ae)
    e1r = w.s([z['e1re']], 'adantr', '( %s -> %s e. RR )' % (Ae, E1))
    nmr = w.s([nrp, w.s([e1r], 'renegcld', '( %s -> -u %s e. RR )' % (Ae, E1))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (Ae, Nm))
    r1 = w.s([w.s([nmr], 'rpcnd', '( %s -> %s e. CC )' % (Ae, Nm)), ec, en0], 'divrecd', '( %s -> ( %s / e ) = ( %s x. %s ) )' % (Ae, Nm, Nm, ie))
    tm2 = w.s([tm, w.s([r1], 'oveq2d', '( %s -> ( %s x. ( %s / e ) ) = ( %s x. ( %s x. %s ) ) )' % (Ae, DK, Nm, DK, Nm, ie))], 'breqtrd',
              '( %s -> ( %s x. %s ) <_ ( %s x. ( %s x. %s ) ) )' % (Ae, s, p, DK, Nm, ie))
    ar = w.s([ae], 'abscld', '( %s -> %s e. RR )' % (Ae, a))
    a0 = w.s([ae], 'absge0d', '( %s -> 0 <_ %s )' % (Ae, a))
    pr = w.s([erp, w.s([w.s([z['rz']], 'adantr', '( %s -> %s e. RR )' % (Ae, RZ))], 'renegcld', '( %s -> -u %s e. RR )' % (Ae, RZ))], 'rpcxpcld',
             '( %s -> %s e. RR+ )' % (Ae, p))
    sr = w.s([dpq], 'abscld', '( %s -> %s e. RR )' % (Ae, s))
    ier = w.s([erp], 'rpreccld', '( %s -> %s e. RR+ )' % (Ae, ie))
    e1rp = w.s([z['e1rp']], 'adantr', '( %s -> %s e. RR+ )' % (Ae, E1))
    t2 = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % Ae), e1r], 'rpcxpcld', '( %s -> ( 2 ^c %s ) e. RR+ )' % (Ae, E1))
    crr = w.s([cb['cr']], 'adantr', '( %s -> C e. RR )' % Ae)
    dkr = w.s([w.s([w.s([t2], 'rpred', '( %s -> ( 2 ^c %s ) e. RR )' % (Ae, E1)), crr], 'remulcld', '( %s -> ( ( 2 ^c %s ) x. C ) e. RR )' % (Ae, E1)), e1rp],
              'rerpdivcld', '( %s -> %s e. RR )' % (Ae, DK))
    clo = cl.Closure(w, Ae, {a: ar, p: pr, s: sr, Nm: nmr, ie: ier, DK: dkr})
    for k in (a, p, s, Nm, ie, DK):
        clo.atom(k)
    clo.have(a, 'ge0', a0)
    l1 = w.s([clo.mem('( %s x. %s )' % (s, p), 'RR'), clo.mem('( %s x. ( %s x. %s ) )' % (DK, Nm, ie), 'RR'), ar, a0, tm2], 'lemul2ad',
             '( %s -> ( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. ( %s x. %s ) ) ) )' % (Ae, a, s, p, a, DK, Nm, ie))
    G = lin.linarith(w, Ae, [l1], '( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. ( %s x. %s ) )' % (a, p, s, DK, Nm, a, ie), closure=clo, products=True)
    r2 = w.s([w.s([ar], 'recnd', '( %s -> %s e. CC )' % (Ae, a)), ec, en0], 'divrecd', '( %s -> %s = ( %s x. %s ) )' % (Ae, ae_, a, ie))
    G2 = w.s([G, w.s([r2], 'oveq2d', '( %s -> ( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. ( %s x. %s ) ) )' % (Ae, DK, Nm, ae_, DK, Nm, a, ie))], 'breqtrrd',
             '( %s -> ( ( %s x. %s ) x. %s ) <_ ( ( %s x. %s ) x. %s ) )' % (Ae, a, p, s, DK, Nm, ae_))
    tb = w.s([mm, G2], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ ( ( %s x. %s ) x. %s ) )' % (Ae, XE, DK, Nm, ae_))
    axr = w.s([xe], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Ae, XE))
    DN = '( %s x. %s )' % (DK, Nm)
    dnr = clo.mem(DN, 'RR')
    aer = w.s([ar, erp], 'rerpdivcld', '( %s -> %s e. RR )' % (Ae, ae_))
    tr = w.s([dnr, aer], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (Ae, DN, ae_))
    ab2 = w.s([fin, axr, tr, tb], 'fsumle', '( %s -> sum_ e e. %s ( abs ` %s ) <_ sum_ e e. %s ( %s x. %s ) )' % (A0, N1, XE, N1, DN, ae_))
    # the constant pulled out
    nrp0 = w.s([nn], 'nnrpd', '( %s -> N e. RR+ )' % A0)
    nmr0 = w.s([nrp0, w.s([z['e1re']], 'renegcld', '( %s -> -u %s e. RR )' % (A0, E1))], 'rpcxpcld', '( %s -> %s e. RR+ )' % (A0, Nm))
    t20 = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A0), z['e1re']], 'rpcxpcld', '( %s -> ( 2 ^c %s ) e. RR+ )' % (A0, E1))
    dkr0 = w.s([w.s([w.s([t20], 'rpred', '( %s -> ( 2 ^c %s ) e. RR )' % (A0, E1)), cb['cr']], 'remulcld', '( %s -> ( ( 2 ^c %s ) x. C ) e. RR )' % (A0, E1)), z['e1rp']],
               'rerpdivcld', '( %s -> %s e. RR )' % (A0, DK))
    dn0r = w.s([dkr0, w.s([nmr0], 'rpred', '( %s -> %s e. RR )' % (A0, Nm))], 'remulcld', '( %s -> %s e. RR )' % (A0, DN))
    pull = w.s([fin, w.s([dn0r], 'recnd', '( %s -> %s e. CC )' % (A0, DN)), w.s([aer], 'recnd', '( %s -> %s e. CC )' % (Ae, ae_))], 'fsummulc2',
               '( %s -> ( %s x. sum_ e e. %s %s ) = sum_ e e. %s ( %s x. %s ) )' % (A0, DN, N1, ae_, N1, DN, ae_))
    # the log-average at y = N
    nr0 = w.s([nrp0], 'rpred', '( %s -> N e. RR )' % A0)
    lv = lavat(w, A0, c['lal'], 'N', nr0, w.s([nn], 'nnge1d', '( %s -> 1 <_ N )' % A0))
    fl = w.s([w.s([nn], 'nnzd', '( %s -> N e. ZZ )' % A0), w.inst('flid')], 'syl', '( %s -> ( |_ ` N ) = N )' % A0)
    fr = w.s([fl], 'oveq2d', '( %s -> ( 1 ... ( |_ ` N ) ) = %s )' % (A0, N1))
    SD = 'sum_ d e. %s ( ( abs ` ( A ` d ) ) / d )' % N1
    s1 = w.s([fr], 'sumeq1d', '( %s -> sum_ d e. ( 1 ... ( |_ ` N ) ) ( ( abs ` ( A ` d ) ) / d ) = %s )' % (A0, SD))
    idd = w.s([], 'id', '( d = e -> d = e )')
    cgd, nb = w.congr('( ( abs ` ( A ` d ) ) / d )', {'d': 'e'}, 'd = e', {'d': idd})
    assert nb == ae_, nb
    s2 = w.s([w.s([cgd], 'cbvsumv', '%s = sum_ e e. %s %s' % (SD, N1, ae_))], 'a1i', '( %s -> %s = sum_ e e. %s %s )' % (A0, SD, N1, ae_))
    s12 = w.s([s1, s2], 'eqtrd', '( %s -> sum_ d e. ( 1 ... ( |_ ` N ) ) ( ( abs ` ( A ` d ) ) / d ) = sum_ e e. %s %s )' % (A0, N1, ae_))
    LG = '( ( log ` N ) + K )'
    lv2 = w.s([s12, lv], 'eqbrtrrd', '( %s -> sum_ e e. %s %s <_ %s )' % (A0, N1, ae_, LG))
    ser = w.s([fin, aer], 'fsumrecl', '( %s -> sum_ e e. %s %s e. RR )' % (A0, N1, ae_))
    lgr = w.s([w.s([nrp0], 'relogcld', '( %s -> ( log ` N ) e. RR )' % A0), c['kr']], 'readdcld', '( %s -> %s e. RR )' % (A0, LG))
    t2r0 = w.s([t20], 'rpred', '( %s -> ( 2 ^c %s ) e. RR )' % (A0, E1))
    t2c0 = w.s([t2r0, cb['cr']], 'remulcld', '( %s -> ( ( 2 ^c %s ) x. C ) e. RR )' % (A0, E1))
    t2c00 = w.s([t2r0, cb['cr'], w.s([t20], 'rpge0d', '( %s -> 0 <_ ( 2 ^c %s ) )' % (A0, E1)), c0], 'mulge0d', '( %s -> 0 <_ ( ( 2 ^c %s ) x. C ) )' % (A0, E1))
    dk0 = w.s([t2c0, z['e1rp'], t2c00], 'divge0d', '( %s -> 0 <_ %s )' % (A0, DK))
    dnge = w.s([dkr0, w.s([nmr0], 'rpred', '( %s -> %s e. RR )' % (A0, Nm)), dk0, w.s([nmr0], 'rpge0d', '( %s -> 0 <_ %s )' % (A0, Nm))], 'mulge0d',
               '( %s -> 0 <_ %s )' % (A0, DN))
    l3 = w.s([ser, lgr, dn0r, dnge, lv2], 'lemul2ad', '( %s -> ( %s x. sum_ e e. %s %s ) <_ ( %s x. %s ) )' % (A0, DN, N1, ae_, DN, LG))
    l4 = w.s([pull, l3], 'eqbrtrrd', '( %s -> sum_ e e. %s ( %s x. %s ) <_ ( %s x. %s ) )' % (A0, N1, DN, ae_, DN, LG))
    ma = w.s([w.s([dkr0], 'recnd', '( %s -> %s e. CC )' % (A0, DK)), w.s([nmr0], 'rpcnd', '( %s -> %s e. CC )' % (A0, Nm)), w.s([lgr], 'recnd', '( %s -> %s e. CC )' % (A0, LG))],
             'mulassd', '( %s -> ( %s x. %s ) = ( %s x. ( %s x. %s ) ) )' % (A0, DN, LG, DK, Nm, LG))
    RHS = '( %s x. ( %s x. %s ) )' % (DK, Nm, LG)
    l5 = w.s([l4, ma], 'breqtrd', '( %s -> sum_ e e. %s ( %s x. %s ) <_ %s )' % (A0, N1, DN, ae_, RHS))
    sx = w.s([fin, axr], 'fsumrecl', '( %s -> sum_ e e. %s ( abs ` %s ) e. RR )' % (A0, N1, XE))
    st = w.s([fin, tr], 'fsumrecl', '( %s -> sum_ e e. %s ( %s x. %s ) e. RR )' % (A0, N1, DN, ae_))
    rr = w.s([dkr0, w.s([w.s([nmr0], 'rpred', '( %s -> %s e. RR )' % (A0, Nm)), lgr], 'remulcld', '( %s -> ( %s x. %s ) e. RR )' % (A0, Nm, LG))], 'remulcld',
             '( %s -> %s e. RR )' % (A0, RHS))
    l6 = w.s([sx, st, rr, ab2, l5], 'letrd', '( %s -> sum_ e e. %s ( abs ` %s ) <_ %s )' % (A0, N1, XE, RHS))
    asum = w.s([w.s([fin, xe], 'fsumcl', '( %s -> sum_ e e. %s %s e. CC )' % (A0, N1, XE))], 'abscld', '( %s -> ( abs ` sum_ e e. %s %s ) e. RR )' % (A0, N1, XE))
    l7 = w.s([asum, sx, rr, ab1, l6], 'letrd', '( %s -> ( abs ` sum_ e e. %s %s ) <_ %s )' % (A0, N1, XE, RHS))
    w.qed([adif, l7], 'eqbrtrd', '( %s -> ( abs ` %s ) <_ %s )' % (A0, DIF, RHS))
    run7b(w)
