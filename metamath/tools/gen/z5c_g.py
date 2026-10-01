"""Sortie Z5c, section G: the kernel Gker and psi_eq_sum_Gker (Detector.lean 654-688)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from z5clib import *
from cl import Closure, lift


def pdc(w, a, dn):
    """( a -> prod_ p e. PF(d) ( FMP(p) - 1 ) e. CC ) from dn: ( a -> d e. NN )"""
    fin = sy(w, a, dn, 'pffinq', '%s e. Fin' % PF('d'))
    b = '( %s /\\ p e. %s )' % (a, PF('d'))
    pn = sy(w, b, pp(w, b, w.s([], 'simpr', '( %s -> p e. %s )' % (b, PF('d')))), 'prmnn', 'p e. NN')
    fc = w.s([w.s([fmpre(w, b, pn), w.s([], '1red', '( %s -> 1 e. RR )' % b)], 'resubcld', '( %s -> ( %s - 1 ) e. RR )' % (b, FMP('p')))], 'recnd',
             '( %s -> ( %s - 1 ) e. CC )' % (b, FMP('p')))
    return w.s([fin, fc], 'fprodcl', '( %s -> prod_ p e. %s ( %s - 1 ) e. CC )' % (a, PF('d'), FMP('p')))


def z5psigk():
    w = W('z5psigk', "Lean psi_eq_sum_Gker: for squarefree T and M in NN, psi_T ( M ) = sum_ d | M G_T ( d ) with the finite kernel "
                     "G_T ( d ) = prod_ p | d ( f ( p ) - 1 ) for d | T, else 0 (the Euler-product engine z5sqfeul at the divisors of ( T , M )).")
    ante = '( %s /\\ M e. NN )' % SQF('T')
    st = mkst(w, ante)
    tn = st([], 'simpll', 'T e. NN'); t0 = st([], 'simplr', '( mmu ` T ) =/= 0'); mn = st([], 'simpr', 'M e. NN')
    g = '( T gcd M )'
    tz = st([tn], 'nnzd', 'T e. ZZ'); mz = st([mn], 'nnzd', 'M e. ZZ')
    gn = st([tn, mn, w.inst('gcdnncl')], 'syl2anc', '%s e. NN' % g)
    gz = st([gn], 'nnzd', '%s e. ZZ' % g)
    gd = st([tz, mz, w.inst('gcddvds')], 'syl2anc', '( %s || T /\\ %s || M )' % (g, g))
    gT = st([gd], 'simpld', '%s || T' % g); gM = st([gd], 'simprd', '%s || M' % g)
    gs = st([tn, t0, gn, gT, w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` %s ) =/= 0' % g)
    PD = 'prod_ p e. %s ( %s - 1 )' % (PF('d'), FMP('p'))
    GKd = GK('T', 'd')
    IFd = 'if ( ( mmu ` d ) =/= 0 , %s , 0 )' % PD
    # DV(g) C_ DV(M)
    a = '( %s /\\ x e. NN )' % ante
    sa = mkst(w, a)
    xz = sa([sa([], 'simpr', 'x e. NN')], 'nnzd', 'x e. ZZ')
    tr = sa([xz, lift(w, gz, a), lift(w, mz, a), w.inst('dvdstr')], 'syl3anc', '( ( x || %s /\\ %s || M ) -> x || M )' % (g, g))
    tr2 = sa([lift(w, gM, a), tr], 'mpan2d', '( x || %s -> x || M )' % g)
    ss = st([tr2], 'ss2rabdv', '%s C_ %s' % (DV(g), DV('M')))
    # summand in CC on DV(g)
    b = '( %s /\\ d e. %s )' % (ante, DV(g))
    sb = mkst(w, b)
    dnb, ddg = dvparts(w, b, sb([], 'simpr', 'd e. %s' % DV(g)), g)
    pdcb = pdc(w, b, dnb)
    gkc = sb([pdcb, sb([], '0cnd', '0 e. CC')], 'ifcld', '%s e. CC' % GKd)
    # zero on DV(M) \ DV(g)
    c = '( %s /\\ d e. ( %s \\ %s ) )' % (ante, DV('M'), DV(g))
    sc = mkst(w, c)
    inm = sc([sc([], 'simpr', 'd e. ( %s \\ %s )' % (DV('M'), DV(g)))], 'eldifad', 'd e. %s' % DV('M'))
    ning = sc([sc([], 'simpr', 'd e. ( %s \\ %s )' % (DV('M'), DV(g)))], 'eldifbd', '-. d e. %s' % DV(g))
    dnc, ddm = dvparts(w, c, inm, 'M')
    dzc = sc([dnc], 'nnzd', 'd e. ZZ')
    e_ = '( %s /\\ d || T )' % c
    se = mkst(w, e_)
    dg = se([se([se([], 'simpr', 'd || T'), lift(w, ddm, e_)], 'jca', '( d || T /\\ d || M )'),
             se([lift(w, dzc, e_), lift(w, tz, e_), lift(w, mz, e_), w.inst('dvdsgcd')], 'syl3anc', '( ( d || T /\\ d || M ) -> d || %s )' % g)], 'mpd', 'd || %s' % g)
    ing = se([lift(w, dnc, e_), dg, w.s([eldv(w, g)], 'a1i', '( %s -> ( d e. %s <-> ( d e. NN /\\ d || %s ) ) )' % (e_, DV(g), g))], 'mpbir2and', 'd e. %s' % DV(g))
    ndT = w.s([ing, lift(w, ning, e_)], 'pm2.65da', '( %s -> -. d || T )' % c)
    z0 = sc([ndT], 'iffalsed', '%s = 0' % GKd)
    dvf = sy(w, ante, mn, 'dvdsfi', '%s e. Fin' % DV('M'))
    fs = st([ss, gkc, z0, dvf], 'fsumss', 'sum_ d e. %s %s = sum_ d e. %s %s' % (DV(g), GKd, DV('M'), GKd))
    # on DV(g): GKd = IFd
    dzb = sb([dnb], 'nnzd', 'd e. ZZ')
    dT = sb([sb([ddg, lift(w, gT, b)], 'jca', '( d || %s /\\ %s || T )' % (g, g)),
             sb([dzb, lift(w, gz, b), lift(w, tz, b), w.inst('dvdstr')], 'syl3anc', '( ( d || %s /\\ %s || T ) -> d || T )' % (g, g))], 'mpd', 'd || T')
    v1 = sb([dT], 'iftrued', '%s = %s' % (GKd, PD))
    mud = sb([lift(w, gn, b), lift(w, gs, b), dnb, ddg, w.inst('z5sqfdvd')], 'syl22anc', '( mmu ` d ) =/= 0')
    v2 = sb([mud], 'iftrued', '%s = %s' % (IFd, PD))
    v = sb([v1, v2], 'eqtr4d', '%s = %s' % (GKd, IFd))
    se2 = st([v], 'sumeq2dv', 'sum_ d e. %s %s = sum_ d e. %s %s' % (DV(g), GKd, DV(g), IFd))
    # the engine
    bp = '( %s /\\ p e. Prime )' % ante
    pnp = sy(w, bp, w.s([], 'simpr', '( %s -> p e. Prime )' % bp), 'prmnn', 'p e. NN')
    fmc = w.s([fmpre(w, bp, pnp)], 'recnd', '( %s -> %s e. CC )' % (bp, FMP('p')))
    bc = w.s([fmc, w.s([], '1cnd', '( %s -> 1 e. CC )' % bp)], 'subcld', '( %s -> ( %s - 1 ) e. CC )' % (bp, FMP('p')))
    eng = w.s([gn, bc], 'z5sqfeul', '( %s -> sum_ d e. %s %s = prod_ p e. %s ( 1 + ( %s - 1 ) ) )' % (ante, DV(g), IFd, PF(g), FMP('p')))
    # ( 1 + ( f - 1 ) ) = f
    cq = '( %s /\\ p e. %s )' % (ante, PF(g))
    pnq = sy(w, cq, pp(w, cq, w.s([], 'simpr', '( %s -> p e. %s )' % (cq, PF(g)))), 'prmnn', 'p e. NN')
    fq = w.s([fmpre(w, cq, pnq)], 'recnd', '( %s -> %s e. CC )' % (cq, FMP('p')))
    pc = w.s([w.s([], '1cnd', '( %s -> 1 e. CC )' % cq), fq, w.inst('pncan3')], 'syl2anc', '( %s -> ( 1 + ( %s - 1 ) ) = %s )' % (cq, FMP('p'), FMP('p')))
    pe = st([pc], 'prodeq2dv', 'prod_ p e. %s ( 1 + ( %s - 1 ) ) = prod_ p e. %s %s' % (PF(g), FMP('p'), PF(g), FMP('p')))
    fp = st([gn, gs, w.inst('z5fmpprod')], 'syl2anc', '%s = prod_ p e. %s %s' % (FMP(g), PF(g), FMP('p')))
    # chain
    c1 = st([fp, pe], 'eqtr4d', '%s = prod_ p e. %s ( 1 + ( %s - 1 ) )' % (FMP(g), PF(g), FMP('p')))
    c2 = st([c1, eng], 'eqtr4d', '%s = sum_ d e. %s %s' % (FMP(g), DV(g), IFd))
    c3 = st([c2, se2], 'eqtr4d', '%s = sum_ d e. %s %s' % (FMP(g), DV(g), GKd))
    w.qed([c3, fs], 'eqtrd', STATEMENTS['z5psigk'])
    return w


if __name__ == '__main__':
    import z5clib
    for f in sys.argv[1:]:
        z5clib.run(globals()[f]())
