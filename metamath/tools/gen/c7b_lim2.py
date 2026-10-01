"""C7b section 1, the limit: dconvdif0, dconvlim1, dconvlim."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from c7blib import *
import lin, cl
import congr as _cg
lin.FASTPATH = True


def dchc(w, ph):
    """ph = DCH"""
    lav = w.s([], 'simpll', '( %s -> %s )' % (ph, LAV()))
    cfb = w.s([], 'simplr', '( %s -> %s )' % (ph, CFBB))
    zc2 = w.s([], 'simpr', '( %s -> ( %s /\\ seq 1 ( + , %s ) e. dom ~~> ) )' % (ph, ZP1, MAP('A')))
    zp = w.s([zc2, w.inst('simpl')], 'syl', '( %s -> %s )' % (ph, ZP1))
    cvg = w.s([zc2, w.inst('simpr')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, MAP('A')))
    af = w.s([lav, w.inst('simp1')], 'syl', '( %s -> A : NN --> CC )' % ph)
    kr = w.s([lav, w.inst('simp2')], 'syl', '( %s -> K e. RR )' % ph)
    return dict(lav=lav, cfb=cfb, zp=zp, cvg=cvg, af=af, kr=kr)


def val(w, ante, body, k, mem, exs, x='n'):
    return _cg.mptval(w, ante, x, 'NN', body, k, mem, exs=exs, gen=w.g)


def mex(w, ph, M):
    return w.s([w.s([w.s([], 'nnex', 'NN e. _V')], 'a1i', '( %s -> NN e. _V )' % ph)], 'mptexd', '( %s -> %s e. _V )' % (ph, M))


def DIF(n):
    return '( %s - ( %s x. %s ) )' % (CPS(n), PS('A', n), PS('B', n))


def ex_(w, ante, E, cc):
    return w.s([cc], 'elexd', '( %s -> %s e. _V )' % (ante, E))


if __name__ == '__main__' and (not only or 'dconvdif0' in only):
    w = W('dconvdif0', 'The difference of the convolution partial sums and the products of the partial sums tends to zero.')
    ph = DCH
    c = dchc(w, ph)
    z = zctx(w, ph, c['zp'])
    cb = cfbctx(w, ph, c['cfb'])
    c0 = w.s([c['cfb'], w.inst('cfb0')], 'syl', '( %s -> 0 <_ C )' % ph)
    F = '( n e. NN |-> %s )' % DIF('n')
    G = '( n e. NN |-> ( abs ` %s ) )' % DIF('n')
    MJX = MJ(DK, 'K', E1)
    t2 = w.s([w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % ph), z['e1re']], 'rpcxpcld', '( %s -> ( 2 ^c %s ) e. RR+ )' % (ph, E1))
    dkr = w.s([w.s([w.s([t2], 'rpred', '( %s -> ( 2 ^c %s ) e. RR )' % (ph, E1)), cb['cr']], 'remulcld', '( %s -> ( ( 2 ^c %s ) x. C ) e. RR )' % (ph, E1)), z['e1rp']],
              'rerpdivcld', '( %s -> %s e. RR )' % (ph, DK))
    mj = w.s([w.s([w.s([dkr, c['kr']], 'jca', '( %s -> ( %s e. RR /\\ K e. RR ) )' % (ph, DK)), z['e1rp']], 'jca',
                  '( %s -> ( ( %s e. RR /\\ K e. RR ) /\\ %s e. RR+ ) )' % (ph, DK, E1)), w.inst('dconvmaj')], 'syl', '( %s -> %s ~~> 0 )' % (ph, MJX))
    Al = '( %s /\\ l e. NN )' % ph
    ln = w.s([], 'simpr', '( %s -> l e. NN )' % Al)
    afl = w.s([c['af']], 'adantr', '( %s -> A : NN --> CC )' % Al)
    bfl = w.s([cb['bf']], 'adantr', '( %s -> B : NN --> CC )' % Al)
    zcl = w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % Al)
    dc = w.s([cpscl2(w, Al, 'l', afl, bfl, zcl, ln), w.s([pscl(w, Al, 'A', 'l', afl, zcl), pscl(w, Al, 'B', 'l', bfl, zcl)], 'mulcld',
                                                        '( %s -> ( %s x. %s ) e. CC )' % (Al, PS('A', 'l'), PS('B', 'l')))], 'subcld', '( %s -> %s e. CC )' % (Al, DIF('l')))
    adc = w.s([dc], 'abscld', '( %s -> ( abs ` %s ) e. RR )' % (Al, DIF('l')))
    vf, _ = val(w, Al, DIF('n'), 'l', ln, ex_(w, Al, DIF('l'), dc))
    vg, _ = val(w, Al, '( abs ` %s )' % DIF('n'), 'l', ln, ex_(w, Al, '( abs ` %s )' % DIF('l'), w.s([adc], 'recnd', '( %s -> ( abs ` %s ) e. CC )' % (Al, DIF('l')))))
    ML = '( %s x. ( ( l ^c -u %s ) x. ( ( log ` l ) + K ) ) )' % (DK, E1)
    lrp = w.s([ln], 'nnrpd', '( %s -> l e. RR+ )' % Al)
    e1l = w.s([z['e1re']], 'adantr', '( %s -> %s e. RR )' % (Al, E1))
    mlr = w.s([w.s([dkr], 'adantr', '( %s -> %s e. RR )' % (Al, DK)),
               w.s([w.s([w.s([lrp, w.s([e1l], 'renegcld', '( %s -> -u %s e. RR )' % (Al, E1))], 'rpcxpcld', '( %s -> ( l ^c -u %s ) e. RR+ )' % (Al, E1))], 'rpred',
                        '( %s -> ( l ^c -u %s ) e. RR )' % (Al, E1)),
                    w.s([w.s([lrp], 'relogcld', '( %s -> ( log ` l ) e. RR )' % Al), w.s([c['kr']], 'adantr', '( %s -> K e. RR )' % Al)], 'readdcld',
                        '( %s -> ( ( log ` l ) + K ) e. RR )' % Al)], 'remulcld', '( %s -> ( ( l ^c -u %s ) x. ( ( log ` l ) + K ) ) e. RR )' % (Al, E1))],
              'remulcld', '( %s -> %s e. RR )' % (Al, ML))
    vm, _ = val(w, Al, '( %s x. ( ( n ^c -u %s ) x. ( ( log ` n ) + K ) ) )' % (DK, E1), 'l', ln, ex_(w, Al, ML, w.s([mlr], 'recnd', '( %s -> %s e. CC )' % (Al, ML))))
    bnd = w.s([], 'dconvdifb', '( %s -> ( abs ` %s ) <_ %s )' % (Al, DIF('l'), ML))
    fmr = w.s([vm, mlr], 'eqeltrd', '( %s -> ( %s ` l ) e. RR )' % (Al, MJX))
    fgr = w.s([vg, adc], 'eqeltrd', '( %s -> ( %s ` l ) e. RR )' % (Al, G))
    le8 = w.s([w.s([vg, bnd], 'eqbrtrd', '( %s -> ( %s ` l ) <_ %s )' % (Al, G, ML)), vm], 'breqtrrd', '( %s -> ( %s ` l ) <_ ( %s ` l ) )' % (Al, G, MJX))
    le9 = w.s([w.s([dc], 'absge0d', '( %s -> 0 <_ ( abs ` %s ) )' % (Al, DIF('l'))), vg], 'breqtrrd', '( %s -> 0 <_ ( %s ` l ) )' % (Al, G))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ph)
    gc = w.s([nnuz, one, mj, mex(w, ph, G), fmr, fgr, le8, le9], 'climsqz2', '( %s -> %s ~~> 0 )' % (ph, G))
    fcl = w.s([vf, dc], 'eqeltrd', '( %s -> ( %s ` l ) e. CC )' % (Al, F))
    gv = w.s([vg, w.s([vf], 'fveq2d', '( %s -> ( abs ` ( %s ` l ) ) = ( abs ` %s ) )' % (Al, F, DIF('l')))], 'eqtr4d', '( %s -> ( %s ` l ) = ( abs ` ( %s ` l ) ) )' % (Al, G, F))
    bi = w.s([nnuz, one, mex(w, ph, F), mex(w, ph, G), fcl, gv], 'climabs0', '( %s -> ( %s ~~> 0 <-> %s ~~> 0 ) )' % (ph, F, G))
    w.qed([gc, bi], 'mpbird', '( %s -> %s ~~> 0 )' % (ph, F))
    run7b(w)


def serlim(w, ph, A, af, zc, cvg):
    """( ph -> seq 1 ( + , MAP(A) ) ~~> SER(A) ) by isumclim2 (index k)"""
    Ak = '( %s /\\ k e. NN )' % ph
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    tc = trmcl(w, Ak, A, 'k', w.s([af], 'adantr', '( %s -> %s : NN --> CC )' % (Ak, A)), kn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))
    v, _ = val(w, Ak, TRM(A, 'n'), 'k', kn, ex_(w, Ak, TRM(A, 'k'), tc))
    return w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ph), v, tc, cvg], 'isumclim2',
               '( %s -> seq 1 ( + , %s ) ~~> %s )' % (ph, MAP(A), SER(A)))


def psser(w, Al, A, af, zc, ln):
    """( Al -> ( seq 1 ( + , MAP(A) ) ` l ) = PS(A,l) ) by fsumser (index k) and cbvsumv"""
    Ak = '( %s /\\ k e. ( 1 ... l ) )' % Al
    kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... l ) )' % Ak), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ak)
    tc = trmcl(w, Ak, A, 'k', w.s([af], 'adantr', '( %s -> %s : NN --> CC )' % (Ak, A)), kn, w.s([zc], 'adantr', '( %s -> Z e. CC )' % Ak))
    v, _ = val(w, Ak, TRM(A, 'n'), 'k', kn, ex_(w, Ak, TRM(A, 'k'), tc))
    luz = w.s([ln, w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> l e. ( ZZ>= ` 1 ) )' % Al)
    fs = w.s([v, luz, tc], 'fsumser', '( %s -> sum_ k e. ( 1 ... l ) %s = ( seq 1 ( + , %s ) ` l ) )' % (Al, TRM(A, 'k'), MAP(A)))
    cb = w.s([trmsub(w, A, 'i', 'Z', 'k')], 'cbvsumv', 'sum_ k e. ( 1 ... l ) %s = %s' % (TRM(A, 'k'), PS(A, 'l')))
    return w.s([fs, w.s([cb], 'a1i', '( %s -> sum_ k e. ( 1 ... l ) %s = %s )' % (Al, TRM(A, 'k'), PS(A, 'l')))], 'eqtr3d',
               '( %s -> ( seq 1 ( + , %s ) ` l ) = %s )' % (Al, MAP(A), PS(A, 'l')))


if __name__ == '__main__' and (not only or 'dconvlim1' in only):
    w = W('dconvlim1', 'The Dirichlet series of the convolution converges to the product of the two Dirichlet series '
          '(Mathlib ` LSeries_convolution\' ` , under the log-average bound on ` A ` and bounded ` B ` ).')
    ph = DCH
    c = dchc(w, ph)
    z = zctx(w, ph, c['zp'])
    cb = cfbctx(w, ph, c['cfb'])
    sa = serlim(w, ph, 'A', c['af'], z['zc'], c['cvg'])
    cvb = w.s([w.s([c['cfb'], c['zp']], 'jca', '( %s -> ( %s /\\ %s ) )' % (ph, CFBB, ZP1)), w.inst('dsercvg')], 'syl', '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (ph, MAP('B')))
    sb = serlim(w, ph, 'B', cb['bf'], z['zc'], cvb)
    Al = '( %s /\\ l e. NN )' % ph
    ln = w.s([], 'simpr', '( %s -> l e. NN )' % Al)
    afl = w.s([c['af']], 'adantr', '( %s -> A : NN --> CC )' % Al)
    bfl = w.s([cb['bf']], 'adantr', '( %s -> B : NN --> CC )' % Al)
    zcl = w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % Al)
    fa = psser(w, Al, 'A', afl, zcl, ln)
    fb = psser(w, Al, 'B', bfl, zcl, ln)
    pa = pscl(w, Al, 'A', 'l', afl, zcl)
    pb = pscl(w, Al, 'B', 'l', bfl, zcl)
    PP = '( %s x. %s )' % (PS('A', 'l'), PS('B', 'l'))
    ppc = w.s([pa, pb], 'mulcld', '( %s -> %s e. CC )' % (Al, PP))
    P = '( n e. NN |-> ( %s x. %s ) )' % (PS('A', 'n'), PS('B', 'n'))
    vp, _ = val(w, Al, '( %s x. %s )' % (PS('A', 'n'), PS('B', 'n')), 'l', ln, ex_(w, Al, PP, ppc))
    SQA = 'seq 1 ( + , %s )' % MAP('A')
    SQB = 'seq 1 ( + , %s )' % MAP('B')
    ph_ = w.s([vp, w.s([fa, fb], 'oveq12d', '( %s -> ( ( %s ` l ) x. ( %s ` l ) ) = %s )' % (Al, SQA, SQB, PP))], 'eqtr4d',
              '( %s -> ( %s ` l ) = ( ( %s ` l ) x. ( %s ` l ) ) )' % (Al, P, SQA, SQB))
    fac = w.s([fa, pa], 'eqeltrd', '( %s -> ( %s ` l ) e. CC )' % (Al, SQA))
    fbc = w.s([fb, pb], 'eqeltrd', '( %s -> ( %s ` l ) e. CC )' % (Al, SQB))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    one = w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ph)
    SS = '( %s x. %s )' % (SER('A'), SER('B'))
    cp = w.s([nnuz, one, sa, mex(w, ph, P), sb, fac, fbc, ph_], 'climmul', '( %s -> %s ~~> %s )' % (ph, P, SS))
    D = '( n e. NN |-> %s )' % DIF('n')
    cd = w.s([], 'dconvdif0', '( %s -> %s ~~> 0 )' % (ph, D))
    # the convolution partial sums
    CS = 'seq 1 ( + , %s )' % CMAP()
    Ak = '( %s /\\ k e. ( 1 ... l ) )' % Al
    kn = w.s([w.s([], 'simpr', '( %s -> k e. ( 1 ... l ) )' % Ak), w.inst('elfznn')], 'syl', '( %s -> k e. NN )' % Ak)
    tk = ctrmcl2(w, Ak, 'k', w.s([afl], 'adantr', '( %s -> A : NN --> CC )' % Ak), w.s([bfl], 'adantr', '( %s -> B : NN --> CC )' % Ak),
                 w.s([zcl], 'adantr', '( %s -> Z e. CC )' % Ak), kn)
    vk, _ = val(w, Ak, CTRM('n'), 'k', kn, ex_(w, Ak, CTRM('k'), tk))
    luz = w.s([ln, w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleqtrdi', '( %s -> l e. ( ZZ>= ` 1 ) )' % Al)
    fs = w.s([vk, luz, tk], 'fsumser', '( %s -> sum_ k e. ( 1 ... l ) %s = ( %s ` l ) )' % (Al, CTRM('k'), CS))
    idk = w.s([], 'id', '( k = i -> k = i )')
    cgk, ci = w.congr(CTRM('k'), {'k': 'i'}, 'k = i', {'k': idk})
    assert ci == CTRM('i'), ci
    cbk = w.s([cgk], 'cbvsumv', 'sum_ k e. ( 1 ... l ) %s = %s' % (CTRM('k'), CPS('l')))
    csl = w.s([fs, w.s([cbk], 'a1i', '( %s -> sum_ k e. ( 1 ... l ) %s = %s )' % (Al, CTRM('k'), CPS('l')))], 'eqtr3d', '( %s -> ( %s ` l ) = %s )' % (Al, CS, CPS('l')))
    cpc = cpscl2(w, Al, 'l', afl, bfl, zcl, ln)
    dlc = w.s([cpc, ppc], 'subcld', '( %s -> %s e. CC )' % (Al, DIF('l')))
    vd, _ = val(w, Al, DIF('n'), 'l', ln, ex_(w, Al, DIF('l'), dlc))
    npc = w.s([cpc, ppc], 'npcand', '( %s -> ( %s + %s ) = %s )' % (Al, DIF('l'), PP, CPS('l')))
    sm = w.s([vd, vp], 'oveq12d', '( %s -> ( ( %s ` l ) + ( %s ` l ) ) = ( %s + %s ) )' % (Al, D, P, DIF('l'), PP))
    hh = w.s([csl, w.s([sm, npc], 'eqtrd', '( %s -> ( ( %s ` l ) + ( %s ` l ) ) = %s )' % (Al, D, P, CPS('l')))], 'eqtr4d',
             '( %s -> ( %s ` l ) = ( ( %s ` l ) + ( %s ` l ) ) )' % (Al, CS, D, P))
    dcl = w.s([vd, dlc], 'eqeltrd', '( %s -> ( %s ` l ) e. CC )' % (Al, D))
    pcl = w.s([vp, ppc], 'eqeltrd', '( %s -> ( %s ` l ) e. CC )' % (Al, P))
    csx = w.s([w.s([], 'seqex', '%s e. _V' % CS)], 'a1i', '( %s -> %s e. _V )' % (ph, CS))
    ca = w.s([nnuz, one, cd, csx, cp, dcl, pcl, hh], 'climadd', '( %s -> %s ~~> ( 0 + %s ) )' % (ph, CS, SS))
    sac = w.s([sa, w.inst('climcl')], 'syl', '( %s -> %s e. CC )' % (ph, SER('A')))
    sbc = w.s([sb, w.inst('climcl')], 'syl', '( %s -> %s e. CC )' % (ph, SER('B')))
    z0 = w.s([w.s([sac, sbc], 'mulcld', '( %s -> %s e. CC )' % (ph, SS))], 'addlidd', '( %s -> ( 0 + %s ) = %s )' % (ph, SS, SS))
    w.qed([ca, z0], 'breqtrd', '( %s -> %s ~~> %s )' % (ph, CS, SS))
    run7b(w)

if __name__ == '__main__' and (not only or 'dconvlim' in only):
    w = W('dconvlim', 'The Dirichlet series of the convolution converges and its sum is the product of the two sums '
          '(Mathlib ` LSeries_convolution\' ` , under the log-average bound on ` A ` and bounded ` B ` ).')
    ph = DCH
    c = dchc(w, ph)
    z = zctx(w, ph, c['zp'])
    cb = cfbctx(w, ph, c['cfb'])
    CS = 'seq 1 ( + , %s )' % CMAP()
    SS = '( %s x. %s )' % (SER('A'), SER('B'))
    lim = w.s([], 'dconvlim1', '( %s -> %s ~~> %s )' % (ph, CS, SS))
    csx = w.s([w.s([], 'seqex', '%s e. _V' % CS)], 'a1i', '( %s -> %s e. _V )' % (ph, CS))
    ssx = w.s([], 'ovexd', '( %s -> %s e. _V )' % (ph, SS))
    dm = w.s([csx, ssx, lim, w.inst('breldmg')], 'syl3anc', '( %s -> %s e. dom ~~> )' % (ph, CS))
    Ak = '( %s /\\ k e. NN )' % ph
    kn = w.s([], 'simpr', '( %s -> k e. NN )' % Ak)
    tk = ctrmcl2(w, Ak, 'k', w.s([c['af']], 'adantr', '( %s -> A : NN --> CC )' % Ak), w.s([cb['bf']], 'adantr', '( %s -> B : NN --> CC )' % Ak),
                 w.s([z['zc']], 'adantr', '( %s -> Z e. CC )' % Ak), kn)
    vk, _ = val(w, Ak, CTRM('n'), 'k', kn, ex_(w, Ak, CTRM('k'), tk))
    sm = w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), w.s([], '1zzd', '( %s -> 1 e. ZZ )' % ph), vk, tk, lim], 'isumclim', '( %s -> %s = %s )' % (ph, CSER(), SS))
    w.qed([dm, sm], 'jca', '( %s -> ( %s e. dom ~~> /\\ %s = %s ) )' % (ph, CS, CSER(), SS))
    run7b(w)
