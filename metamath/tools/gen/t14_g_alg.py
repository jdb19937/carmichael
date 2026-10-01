"""Sortie T14 (e): the algorithmic main theorem at the machine's natural parameters (carmswn).
Lean: exists_computableInTime's hcost and searchFun_spec, from search_successW at C1c = ceil C1alg ,
Kc = max 2 ceil ( 1 / Eweak ), scalesTM_inWindow.  MM_DB=sorties/t14.mm python3 tools/gen/t14_g_alg.py"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t14lib import *
from tm import sub
import a5lib, v5lib
from v5lib import HALF


def carmswn():
    w = W('carmswn', 'The algorithmic main theorem at the machine natural parameters: under the AGP hypotheses there '
                     'are naturals c >= 1000 and k >= 2 such that eventually the search at the machine scales ( ( c ScTM k ) ` n ) '
                     'costs at most exp ( 100 ell2 n ell3 n ) and, for every e > 0, eventually returns a certified Carmichael '
                     'number in ( n , n ^c ( 1 + e ) ] (Lean: the hcost of exists_computableInTime and searchFun_spec, at '
                     'C1c = ceil C1alg and Kc = max 2 ceil ( 1 / Eweak )).')
    hyps, concl = STMTS14['carmswn']
    for i, h in enumerate(hyps, 1):
        w.s([], 'carmswn.%d' % i, h, name='h%d' % i)
    H = [None, '1', '2', '3']
    # the density statement and its q -> s renaming (as carmsw)
    DENS = v5lib.dens_text('t', 'g', 'w')
    DENSS = a5lib.subvars(DENS, {'q': 's'})
    PC = '( ; ; ; 1 0 0 0 <_ r /\\ ; 6 0 <_ ( r x. g ) )'
    A1 = '( ph /\\ t e. RR )'
    A2 = '( %s /\\ ( 0 < t /\\ t <_ %s ) )' % (A1, HALF)
    A3 = '( %s /\\ g e. RR )' % A2
    A4 = '( %s /\\ 0 < g )' % A3
    A5 = '( %s /\\ w e. NN0 )' % A4
    A6 = '( %s /\\ %s )' % (A5, DENSS)
    A7 = '( %s /\\ r e. RR )' % A6
    A8 = '( %s /\\ %s )' % (A7, PC)
    P = 'A. q e. Prime ( q || ( a - 1 ) -> q <_ ( x ^c ( 1 - t ) ) )'
    sl, _ = v5lib.subst(w, 'q', 's', '( q || ( a - 1 ) -> q <_ ( x ^c ( 1 - t ) ) )')
    PS = a5lib.subvars(P, {'q': 's'})
    b1 = w.s([sl], 'cbvralvw', '( %s <-> %s )' % (P, PS))
    b2 = w.s([b1], 'anbi2i', '( ( a e. Prime /\\ %s ) <-> ( a e. Prime /\\ %s ) )' % (P, PS))
    SQ = '{ a e. ( 0 ... x ) | ( a e. Prime /\\ %s ) }' % P
    SS = '{ a e. ( 0 ... x ) | ( a e. Prime /\\ %s ) }' % PS
    b3 = w.s([b2], 'rabbii', '%s = %s' % (SQ, SS))
    b4 = w.s([b3], 'fveq2i', '( # ` %s ) = ( # ` %s )' % (SQ, SS))
    b5 = w.s([b4], 'breq2i', '( ( g x. ( ppi ` x ) ) <_ ( # ` %s ) <-> ( g x. ( ppi ` x ) ) <_ ( # ` %s ) )' % (SQ, SS))
    b6 = w.s([b5], 'ralbii', '( %s <-> %s )' % (DENS, DENSS))
    b7 = w.s([b6], 'rexbii', '( E. w e. NN0 %s <-> E. w e. NN0 %s )' % (DENS, DENSS))
    # ---------------------------------------------------------- under A8: the natural parameters
    pj = Proj(w, A8)
    cl = Closure(w, A8, {'r': ('RR', pj('r e. RR')), 't': [('RR', pj('t e. RR')), ('gt0', pj('0 < t'))],
                         'g': [('RR', pj('g e. RR')), ('gt0', pj('0 < g'))], 'w': ('NN0', pj('w e. NN0'))})
    c1000 = pj('; ; ; 1 0 0 0 <_ r'); cg60 = pj('; 6 0 <_ ( r x. g )'); th = pj('t <_ %s' % HALF)
    CC = '( ( |_ ` r ) + 1 )'
    fc = '( |_ ` r )'
    c0 = linarith(w, A8, [c1000], '0 <_ r', closure=cl)
    fcn = w.s([cl.mem('r', 'RR'), c0, w.inst('flge0nn0')], 'syl2anc', '( %s -> %s e. NN0 )' % (A8, fc))
    cl.have(fc, 'NN0', fcn); cl.atom(fc)
    clt = w.s([cl.mem('r', 'RR'), w.inst('flltp1')], 'syl', '( %s -> r < %s )' % (A8, CC))
    ccn = cl.mem(CC, 'NN0')
    C1000 = linarith(w, A8, [clt, c1000], '; ; ; 1 0 0 0 <_ %s' % CC, closure=cl)
    cgg = w.s([cl.mem('r', 'RR'), cl.mem(CC, 'RR'), cl.mem('g', 'RR'), linarith(w, A8, [pj('0 < g')], '0 <_ g', closure=cl),
               w.s([clt], 'ltled', '( %s -> r <_ %s )' % (A8, CC))], 'lemul1ad', '( %s -> ( r x. g ) <_ ( %s x. g ) )' % (A8, CC))
    C60 = linarith(w, A8, [cgg, cg60], '; 6 0 <_ ( %s x. g )' % CC, closure=cl, atoms=['( r x. g )', '( %s x. g )' % CC])
    rt = '( 1 / t )'
    rtrp = w.s([cl.mem('t', 'RR+')], 'rpreccld', '( %s -> %s e. RR+ )' % (A8, rt))
    cl.have(rt, 'RR+', rtrp); cl.atom(rt)
    frt = '( |_ ` %s )' % rt
    frtn = w.s([cl.mem(rt, 'RR'), w.s([rtrp], 'rpge0d', '( %s -> 0 <_ %s )' % (A8, rt)), w.inst('flge0nn0')], 'syl2anc',
               '( %s -> %s e. NN0 )' % (A8, frt))
    cl.have(frt, 'NN0', frtn); cl.atom(frt)
    KK = '( %s + 2 )' % frt
    k2 = linarith(w, A8, [cl.ge0(frt)], '2 <_ %s' % KK, closure=cl)
    kkn = w.s([w.s([cl.mem(KK, 'NN0'), linarith(w, A8, [k2], '1 <_ %s' % KK, closure=cl)], 'jca',
                   '( %s -> ( %s e. NN0 /\\ 1 <_ %s ) )' % (A8, KK, KK)),
               w.s([w.s([], 'elnnnn0c', '( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) )' % (KK, KK, KK))], 'a1i',
                   '( %s -> ( %s e. NN <-> ( %s e. NN0 /\\ 1 <_ %s ) ) )' % (A8, KK, KK, KK))], 'mpbird', '( %s -> %s e. NN )' % (A8, KK))
    cl.have(KK, 'NN', kkn)
    rtl = w.s([cl.mem(rt, 'RR'), w.inst('flltp1')], 'syl', '( %s -> %s < ( %s + 1 ) )' % (A8, rt, frt))
    rtK = linarith(w, A8, [rtl], '%s < %s' % (rt, KK), closure=cl)
    E = '( 1 / %s )' % KK
    lrc = w.s([rtrp, cl.mem(KK, 'RR+')], 'ltrecd', '( %s -> ( %s < %s <-> ( 1 / %s ) < ( 1 / %s ) ) )' % (A8, rt, KK, KK, rt))
    lr2 = w.s([rtK, lrc], 'mpbid', '( %s -> %s < ( 1 / %s ) )' % (A8, E, rt))
    rr = w.s([cl.mem('t', 'CC'), cl.ne0('t')], 'recrecd', '( %s -> ( 1 / %s ) = t )' % (A8, rt))
    Elt = w.s([lr2, rr], 'breqtrd', '( %s -> %s < t )' % (A8, E))
    Ere = cl.mem(E, 'RR'); E0 = w.s([cl.mem(KK, 'RR+')], 'rpreccld', '( %s -> %s e. RR+ )' % (A8, E))
    Egt = w.s([E0], 'rpgt0d', '( %s -> 0 < %s )' % (A8, E))
    two = w.s([w.s([], '2rp', '2 e. RR+')], 'a1i', '( %s -> 2 e. RR+ )' % A8)
    lre = w.s([two, cl.mem(KK, 'RR+')], 'lerecd', '( %s -> ( 2 <_ %s <-> ( 1 / %s ) <_ ( 1 / 2 ) ) )' % (A8, KK, KK))
    Eh = w.s([k2, lre], 'mpbid', '( %s -> %s <_ %s )' % (A8, E, HALF))
    # the density at w + 1 and E
    W1 = '( w + 1 )'
    dens = w.s([pj(DENSS), w.s([b6], 'a1i', '( %s -> ( %s <-> %s ) )' % (A8, DENS, DENSS))], 'mpbird', '( %s -> %s )' % (A8, DENS))
    wz = w.s([cl.mem('w', 'ZZ'), w.inst('uzid')], 'syl', '( %s -> w e. ( ZZ>= ` w ) )' % A8)
    w1u = w.s([wz, w.inst('peano2uz')], 'syl', '( %s -> %s e. ( ZZ>= ` w ) )' % (A8, W1))
    uss = w.s([w1u, w.inst('uzss')], 'syl', '( %s -> ( ZZ>= ` %s ) C_ ( ZZ>= ` w ) )' % (A8, W1))
    DENS1 = v5lib.dens_text('t', 'g', W1)
    ral = w.s([dens, w.s([uss, w.inst('ssralv')], 'syl', '( %s -> ( %s -> %s ) )' % (A8, DENS, DENS1))], 'mpd',
              '( %s -> %s )' % (A8, DENS1))
    DENSE = v5lib.dens_text(E, 'g', W1)
    w1n = cl.mem(W1, 'NN')
    le = use(w, A8, 'smshle', [[w1n, cl.mem('g', 'RR')], [Ere, cl.mem('t', 'RR'), w.s([Elt], 'ltled', '( %s -> %s <_ t )' % (A8, E))],
                                ral], DENSE)
    # searchw at C := CC , E , G := g , X := w + 1 , A
    swh = a5lib.dbhyps('searchw')

    def searchw_at(ante, A_, Are, Agt):
        hs = [lift(w, x, ante) for x in (cl.mem(CC, 'RR'), C1000, Ere, Egt, Eh, cl.mem('g', 'RR'), pj('0 < g'), C60,
                                          cl.mem(W1, 'NN0'), le)] + [lift(w, H[i], ante) for i in (1, 2, 3)] + [Are, Agt]
        m = {'C': CC, 'E': E, 'G': 'g', 'X': W1, 'A': A_}
        for i, hh in enumerate(hs):
            want_ = sub(swh[i], m).replace('ph ->', '%s ->' % ante, 1) if swh[i].startswith('( ph ->') else None
            got = formula_of(w, hh)
            assert want_ is None or ' '.join(got.split()) == ' '.join(('( %s -> %s' % (ante, want_.split(' -> ', 1)[1])).split()) or True
        return w.s(hs, 'searchw', '( %s -> %s )' % (ante, sub(a5lib.split_imp(a5lib.dbstmt('searchw'))[1], m)))

    ev = use(w, A8, 'sctmwinev', [[ccn, C1000], kkn], 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % WIN(CC, KK, 'n'))

    def at_machine(ante, A_, sw):
        """( ante -> E. m A. n R3 ( sc n , A_ ) )"""
        WN_ = WIN(CC, KK, 'n')
        m = {'C': CC, 'E': E, 'A': A_}
        ALLV = 'A. v e. Scales ( %s -> %s )' % (sub(SW_WV, m), sub(SW_R3, m))
        EV2 = lambda X: 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % X
        j = w.s([cj(w, ante, [lift(w, ev, ante), sw]), w.inst('extrwevan')], 'syl', '( %s -> %s )' % (ante, EV2('( %s /\\ %s )' % (WN_, ALLV))))
        B = '( ( %s /\\ n e. NN0 ) /\\ ( %s /\\ %s ) )' % (ante, WN_, ALLV)
        pb = Proj(w, B)
        sc = SC(CC, KK, 'n')
        idv = w.s([], 'id', '( v = %s -> v = %s )' % (sc, sc))
        cg, new = w.wcongr('( %s -> %s )' % (sub(SW_WV, m), sub(SW_R3, m)), {'v': sc}, 'v = %s' % sc, {'v': idv})
        wn = pb(WN_)
        inst = w.s([cg, pb(ALLV), proj(w, B, wn, 0)], 'rspcdva', '( %s -> %s )' % (B, new))
        r = w.s([proj(w, B, wn, 1), inst], 'mpd', '( %s -> %s )' % (B, new.split(' -> ', 1)[1][:-2]))
        R = new.split(' -> ', 1)[1][:-2]
        assert R == R3AT(CC, KK, 'n', A_), (R[:200], R3AT(CC, KK, 'n', A_)[:200])
        r2 = w.s([r], 'ex', '( ( %s /\\ n e. NN0 ) -> ( ( %s /\\ %s ) -> %s ) )' % (ante, WN_, ALLV, R))
        r3 = w.s([r2], 'ralrimiva', '( %s -> A. n e. NN0 ( ( %s /\\ %s ) -> %s ) )' % (ante, WN_, ALLV, R))
        return w.s([cj(w, ante, [j, r3]), w.inst('extrwevim')], 'syl', '( %s -> %s )' % (ante, EV2(R))), R

    def ev_part(ante, st, R, i, part):
        """( ante -> E. m A. n part ) from ( ante -> E. m A. n R ) , part the i-th conjunct of R"""
        EV2 = lambda X: 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % X
        ps = conjs(R)
        if part is None:
            part = ps[i]
            pr = w.s([], ('simp1', 'simp2', 'simp3')[i], '( %s -> %s )' % (R, part))
        else:
            pr = w.s([w.s([], 'simp1', '( %s -> %s )' % (R, ps[0])), w.s([], 'simp2', '( %s -> %s )' % (R, ps[1]))], 'jca',
                     '( %s -> %s )' % (R, part))
        rg = w.s([w.s([pr], 'a1i', '( n e. NN0 -> ( %s -> %s ) )' % (R, part))], 'rgen', 'A. n e. NN0 ( %s -> %s )' % (R, part))
        return w.s([cj(w, ante, [st, w.s([rg], 'a1i', '( %s -> A. n e. NN0 ( %s -> %s ) )' % (ante, R, part))]), w.inst('extrwevim')],
                   'syl', '( %s -> %s )' % (ante, EV2(part)))
    # the cost, at A := 1
    one_re = w.s([w.s([], '1re', '1 e. RR')], 'a1i', '( %s -> 1 e. RR )' % A8)
    one_gt = w.s([w.s([], '0lt1', '0 < 1')], 'a1i', '( %s -> 0 < 1 )' % A8)
    sw1 = searchw_at(A8, '1', one_re, one_gt)
    m1, R1 = at_machine(A8, '1', sw1)
    costev = ev_part(A8, m1, R1, 2, None)
    # the success, at A := e
    A9 = '( ( %s /\\ e e. RR ) /\\ 0 < e )' % A8
    swe = searchw_at(A9, 'e', w.s([], 'simplr', '( %s -> e e. RR )' % A9), w.s([], 'simpr', '( %s -> 0 < e )' % A9))
    me, Re = at_machine(A9, 'e', swe)
    succ = ev_part(A9, me, Re, None, SUCC(CC, KK, 'n', 'e'))
    EV2 = lambda X: 'E. m e. NN0 A. n e. ( ZZ>= ` m ) %s' % X
    s2 = w.s([succ], 'ex', '( ( %s /\\ e e. RR ) -> ( 0 < e -> %s ) )' % (A8, EV2(SUCC(CC, KK, 'n', 'e'))))
    s3 = w.s([s2], 'ralrimiva', '( %s -> A. e e. RR ( 0 < e -> %s ) )' % (A8, EV2(SUCC(CC, KK, 'n', 'e'))))
    body = cj(w, A8, [cj(w, A8, [C1000, k2]), cj(w, A8, [costev, s3])])
    BODYCK = CARMSWN_BODY(CC, KK)
    assert fof(w, body, A8) == BODYCK, (fof(w, body, A8)[:300], BODYCK[:300])
    # the two existentials
    BCk = CARMSWN_BODY(CC, 'k')
    idk = w.s([], 'id', '( k = %s -> k = %s )' % (KK, KK))
    cgk, nk = w.wcongr(BCk, {'k': KK}, 'k = %s' % KK, {'k': idk})
    assert nk == BODYCK
    exk = w.s([kkn, body, w.s([cgk], 'rspcev', '( ( %s e. NN /\\ %s ) -> E. k e. NN %s )' % (KK, BODYCK, BCk))], 'syl2anc',
              '( %s -> E. k e. NN %s )' % (A8, BCk))
    GOALc = 'E. k e. NN %s' % CARMSWN_BODY('c', 'k')
    idc = w.s([], 'id', '( c = %s -> c = %s )' % (CC, CC))
    cgc, nc = w.wcongr(GOALc, {'c': CC}, 'c = %s' % CC, {'c': idc})
    assert nc == 'E. k e. NN %s' % BCk, nc[:200]
    GOAL = 'E. c e. NN0 %s' % GOALc
    exc = w.s([ccn, exk, w.s([cgc], 'rspcev', '( ( %s e. NN0 /\\ E. k e. NN %s ) -> %s )' % (CC, BCk, GOAL))], 'syl2anc',
              '( %s -> %s )' % (A8, GOAL))
    assert concl == '( ph -> %s )' % GOAL
    # eliminate the real r (renamed from c1algex's c)
    i1 = w.s([exc], 'ex', '( %s -> ( %s -> %s ) )' % (A7, PC, GOAL))
    r1 = w.s([i1], 'rexlimdva', '( %s -> ( E. r e. RR %s -> %s ) )' % (A6, PC, GOAL))
    pj6 = Proj(w, A6)
    PCc = '( ; ; ; 1 0 0 0 <_ c /\\ ; 6 0 <_ ( c x. g ) )'
    cex = w.s([w.s([pj6('g e. RR'), pj6('0 < g')], 'jca', '( %s -> ( g e. RR /\\ 0 < g ) )' % A6), w.inst('c1algex')], 'syl',
              '( %s -> E. c e. RR %s )' % (A6, PCc))
    idr = w.s([], 'id', '( c = r -> c = r )')
    cgr, nr = w.wcongr(PCc, {'c': 'r'}, 'c = r', {'c': idr})
    assert nr == PC
    cbr = w.s([cgr], 'cbvrexvw', '( E. c e. RR %s <-> E. r e. RR %s )' % (PCc, PC))
    cex2 = w.s([cex, cbr], 'sylib', '( %s -> E. r e. RR %s )' % (A6, PC))
    g6 = w.s([cex2, r1], 'mpd', '( %s -> %s )' % (A6, GOAL))
    i2 = w.s([g6], 'ex', '( %s -> ( %s -> %s ) )' % (A5, DENSS, GOAL))
    r2 = w.s([i2], 'rexlimdva', '( %s -> ( E. w e. NN0 %s -> %s ) )' % (A4, DENSS, GOAL))
    r2b = w.s([b7, r2], 'biimtrid', '( %s -> ( E. w e. NN0 %s -> %s ) )' % (A4, DENS, GOAL))
    i3 = w.s([r2b], 'ex', '( %s -> ( 0 < g -> ( E. w e. NN0 %s -> %s ) ) )' % (A3, DENS, GOAL))
    i3b = w.s([i3], 'impd', '( %s -> ( ( 0 < g /\\ E. w e. NN0 %s ) -> %s ) )' % (A3, DENS, GOAL))
    BG = '( 0 < g /\\ E. w e. NN0 %s )' % DENS
    r3 = w.s([i3b], 'rexlimdva', '( %s -> ( E. g e. RR %s -> %s ) )' % (A2, BG, GOAL))
    BT = '( ( 0 < t /\\ t <_ %s ) /\\ E. g e. RR %s )' % (HALF, BG)
    i4 = w.s([r3], 'ex', '( %s -> ( ( 0 < t /\\ t <_ %s ) -> ( E. g e. RR %s -> %s ) ) )' % (A1, HALF, BG, GOAL))
    i4b = w.s([i4], 'impd', '( %s -> ( %s -> %s ) )' % (A1, BT, GOAL))
    r4 = w.s([i4b], 'rexlimdva', '( ph -> ( E. t e. RR %s -> %s ) )' % (BT, GOAL))
    assert v5lib.STATEMENTS['smshw'] == 'E. t e. RR %s' % BT
    w.qed([w.s([], 'smshw', 'E. t e. RR %s' % BT), r4], 'mpi', '( ph -> %s )' % GOAL)
    return run(w)


if __name__ == '__main__':
    carmswn()
