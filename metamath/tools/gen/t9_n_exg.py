"""T9: Lean's ` extractGoF_runs ` at the machine on TMIexg.

  tmiexgh   the epilogue ` peekKet np ; ite flag ( popTop np ) skip ` after a hit: the marker is read and popped
  tmiexgn   the epilogue when the pool ran out: ` peekKet np ` reads ` bra ` , ` skip `
  tmiexg    extractGoF_runs: ` peekBra np ` , the loop (~ tmiexgl at the family), the epilogue by cases, the budget
            ` ( ( extractGo ).2 + 1 ) ( exC + 5 ) ` (~ exres )

    MM_DB=sorties/t9.mm python3 tools/gen/t9_n_exg.py LABEL...
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from t9lib import *
from lin import linarith, nlinarith, lineq
from t7lib import famval, fam_unpack, ifex_closed
from t9_m_loop import (Lg, Si, NW, DRP, REST, HIT, K3, KV, EGY, K0V, J0V, PBG, FLC, COND, NCL, NFM, PF, PV, EXC_, LMG, Z0, PH_S0,
                       ST_L, LCONCL, cnfl_at)
import t8alib as A8

SEL = sys.argv[1:]
PHG = cj(TREE_EXG)
PTR = '( %s ` %s )' % (PF, RG)
IFX = 'if ( ( 1st ` %s ) = ( inr ` (/) ) , (/) , 1o )' % EGG
FINCL = NFL(IFX)
IFR = 'if ( %s , ( inl ` <. %s , %s >. ) , ( inr ` (/) ) )' % (HIT(RG), ZM(Si(RG)), ZU(Si(RG)))
ST_EH = '( ( %s /\\ %s ) -> %s )' % (PHG, HIT(RG), TRI(CLN(LMG['Q3'], S, PTR), CLN('E', FINCL, DFIN_EXG), '3'))
ST_EN = '( ( %s /\\ -. %s ) -> %s )' % (PHG, HIT(RG), TRI(CLN(LMG['Q3'], S, PTR), CLN('E', FINCL, DFIN_EXG), '3'))
BCH = [('K', KV(RG)), ("I'", ACCW(ZA(Si(RG)))), ('K0', K0V(RG)), ('J0', J0V(RG))]


def zcomps(w, ph, B):
    """the components of the initial state"""
    s = w.s
    return tup_comps(w, ph, Z0, s([], 'eqidd', '( %s -> %s = %s )' % (ph, Z0, Z0)), 'F', 'U', 'A', '(/)',
                     {'m': s([B.fn], 'elexd', '( %s -> F e. _V )' % ph), 'u': s([B.uw], 'elexd', '( %s -> U e. _V )' % ph),
                      'a': s([B.an], 'elexd', '( %s -> A e. _V )' % ph), 'h': vex_(w, ph, '(/)')})


def egfacts(w, ph, B):
    """( ph -> ( 1st ` EGG ) = IFR ) , ( ph -> RG <_ ( 2nd ` EGG ) ) (~ exres at the initial state)"""
    s = w.s
    zc = zcomps(w, ph, B)
    ante = s([B.pS, zc['h']], 'jca', '( %s -> ( %s /\\ %s = (/) ) )' % (ph, PH_S0, ZH(Z0)))
    D0 = '( W substr <. 0 , %s >. )' % NW
    EG0 = EGO('L', 'G', D0, ZM(Si('0')), ZU(Si('0')), ZA(Si('0')))
    RS = '( ( 1st ` %s ) = %s /\\ %s <_ ( 2nd ` %s ) )' % (EG0, IFR, RG, EG0)
    rs = s([ante, w.inst('exres')], 'syl', '( %s -> %s )' % (ph, RS))
    d0 = s([B.ww, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = W )' % (ph, D0))
    s0 = s([B.pS, w.inst('exst0')], 'syl', '( %s -> %s = %s )' % (ph, Si('0'), Z0))
    r1, x1 = w.rewrite(EG0, {D0: ('W', d0), Si('0'): (Z0, s0)}, ph)
    r2, x2 = w.rewrite(x1, {ZM(Z0): ('F', zc['m']), ZU(Z0): ('U', zc['u']), ZA(Z0): ('A', zc['a'])}, ph)
    assert x2 == EGG, x2
    ee = s([r1, r2], 'eqtrd', '( %s -> %s = %s )' % (ph, EG0, EGG))
    e1 = s([s([s([ee], 'fveq2d', '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph, EG0, EGG))], 'eqcomd',
              '( %s -> ( 1st ` %s ) = ( 1st ` %s ) )' % (ph, EGG, EG0)), s([rs], 'simpld', '( %s -> ( 1st ` %s ) = %s )' % (ph, EG0, IFR))],
           'eqtrd', '( %s -> ( 1st ` %s ) = %s )' % (ph, EGG, IFR))
    e2 = s([s([rs], 'simprd', '( %s -> %s <_ ( 2nd ` %s ) )' % (ph, RG, EG0)), s([ee], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (ph, EG0, EGG))],
           'breqtrd', '( %s -> %s <_ ( 2nd ` %s ) )' % (ph, RG, EGG))
    return e1, e2


def at_rg(w, ph, B):
    """the Stacks at ( PF ` RG ) and pv : ( ph -> ( PF ` RG ) = PBG( RG ) )"""
    s = w.s
    fe = s([], 'eqidd', '( %s -> %s = %s )' % (ph, PF, PF))
    return fam_at(w, ph, B.mk, B.ne, fe, PF, 'j', 'NN0', PBG, RG, B.rn, B.pbst(RG, B.rz))


def fincl(w, ph, flv, val):
    """( ph -> NFL( val ) = FINCL ) from flv : ( ph -> IFX = val )"""
    s = w.s
    q = s([s([s([flv], 'eqcomd', '( %s -> %s = %s )' % (ph, val, IFX))], 'eqeq2d', '( %s -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ph, val, IFX))],
          'adantr', '( ( %s /\\ h e. TMSt ) -> ( ( TMfl ` h ) = %s <-> ( TMfl ` h ) = %s ) )' % (ph, val, IFX))
    return s([q], 'rabbidva', '( %s -> %s = %s )' % (ph, NFL(val), FINCL))


def epi(hit):
    lab = 'tmiexgh' if hit else 'tmiexgn'
    T = (TREE_EXG, HIT(RG) if hit else '-. %s' % HIT(RG))
    ph = cj(T)
    if hit:
        w = W(lab, 'The epilogue of Lean\'s ` extractGoF ` after a hit: ` peekKet np ` reads the marker, ` ite flag ` pops it, '
                   'the stacks hold the state at ` ExIt ` and the flag says ` ( extractGo ).1 ` is ` some ` (~ exres ).')
    else:
        w = W(lab, 'The epilogue of Lean\'s ` extractGoF ` when the pool ran out: ` ExIt = # W ` , ` peekKet np ` reads ` bra ` , '
                   '` ite flag ` skips, and the flag says ` ( extractGo ).1 ` is ` none ` (~ exres ).')
    s = w.s
    B = Lg(w, ph, T)
    c, mk = B.c, B.mk
    cnd = c[HIT(RG) if hit else '-. %s' % HIT(RG)]
    pv, SR = at_rg(w, ph, B)
    R = B.run(SR)
    ex = {CTY('TMfl'): B.ex[CTY('TMfl')]}
    rst = REST(RG)
    kif = s([cnd], 'iftrued' if hit else 'iffalsed', '( %s -> %s = %s )' % (ph, KV(RG), K3(RG) if hit else rst))
    if hit:
        HD, TL, V = '3', rst, '1o'
        kv = s([SR.vals['K'][1], kif], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, PTR, K3(RG)))
        hg = closed(w, ph, 'gamma3', "3 e. Gamma'")
        tg = B.gam[rst]
        ifeq = s([s([s([], 'eqid', '3 = 3')], 'iftruei', 'if ( 3 = 3 , 1o , (/) ) = 1o')], 'a1i', '( %s -> if ( 3 = 3 , 1o , (/) ) = 1o )' % ph)
    else:
        HD, TL, V = '2', 'X', '(/)'
        rgw = s([c[HIT(RG) if hit else '-. %s' % HIT(RG)], B.ror, w.inst('orel2')], 'sylc', '( %s -> %s = %s )' % (ph, RG, NW))
        r_, x_ = w.rewrite(DRP(RG), {RG: (NW, rgw)}, ph)
        assert x_ == '( W substr <. %s , %s >. )' % (NW, NW), x_
        e0 = s([r_, s([s([], 'swrd00', '( W substr <. %s , %s >. ) = (/)' % (NW, NW))], 'a1i', '( %s -> ( W substr <. %s , %s >. ) = (/) )' % (ph, NW, NW))],
               'eqtrd', '( %s -> %s = (/) )' % (ph, DRP(RG)))
        el = s([s([e0], 'fveq2d', '( %s -> ( encList ` %s ) = ( encList ` (/) ) )' % (ph, DRP(RG))),
                closed(w, ph, 'tm2lenc0', '( encList ` (/) ) = <" 2 ">')], 'eqtrd', '( %s -> ( encList ` %s ) = <" 2 "> )' % (ph, DRP(RG)))
        e2 = s([el], 'oveq1d', '( %s -> %s = ( <" 2 "> ++ X ) )' % (ph, rst))
        kv = s([s([SR.vals['K'][1], kif], 'eqtrd', '( %s -> ( %s ` K ) = %s )' % (ph, PTR, rst)), e2], 'eqtrd',
               '( %s -> ( %s ` K ) = ( <" 2 "> ++ X ) )' % (ph, PTR))
        hg = closed(w, ph, 'gamma2', "2 e. Gamma'")
        tg = B.xw
        n23 = s([s([s([], '2re', '2 e. RR'), s([], '2lt3', '2 < 3')], 'ltneii', '2 =/= 3')], 'neii', '-. 2 = 3')
        ifeq = s([s([n23], 'iffalsei', 'if ( 2 = 3 , 1o , (/) ) = (/)')], 'a1i', '( %s -> if ( 2 = 3 , 1o , (/) ) = (/) )' % ph)
    NV = NFL(V)
    pk = A8.peek_iface(w, ph, mk, RDK, HD, hg, ifeq, V)
    ssS = s([s([], 'ssid', '%s C_ %s' % (S, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, S, S))
    B.call(R, 'tm2lpk', {'A': LMG['Q3'], 'E': LMG['Q4'], 'K': 'K', 'F': RDK, 'Z': HD, 'X': TL, 'N': S, "N'": NV},
           {'( %s ` K ) = ( <" %s "> ++ %s )' % (PTR, HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg,
            'A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (S, RDK, HD, NV): pk, SSS(S): ssS, SSS(NV): B.ss(NV)}, [])
    pm = '( %s /\\ m e. %s )' % (ph, NV)
    mm, mf = A8.nfl_unpack(w, pm, V, 'm', s([], 'simpr', '( %s -> m e. %s )' % (pm, NV)))
    ssN = s([s([], 'ssid', '%s C_ %s' % (NV, NV))], 'a1i', '( %s -> %s C_ %s )' % (ph, NV, NV))
    if hit:
        ex[STMT(GT(LMG['Q6']))] = gotocl(w, ph, mk['tv'], LMG['Q6'], B.ex[LAB(LMG['Q6'])])
        ex['A. m e. %s ( TMfl ` m ) = 1o' % NV] = s([mf], 'ralrimiva', '( %s -> A. m e. %s ( TMfl ` m ) = 1o )' % (ph, NV))
        ex[SSS(NV)] = B.ss(NV)
        B.call(R, 'tm2lbrt', {'A': LMG['Q4'], 'C': 'TMfl', 'E': LMG['Q5'], 'Q': GT(LMG['Q6']), 'N': NV}, ex, [])
        pi = A8.pop_iface(w, ph, mk, NV, B.ss(NV), '3', hg, NV, ssN)
        B.call(R, 'tm2lpop', {'A': LMG['Q5'], 'E': 'E', 'K': 'K', 'F': PID, 'Z': '3', 'X': rst, 'N': NV, "N'": NV},
               {'( %s ` K ) = ( <" 3 "> ++ %s )' % (PTR, rst): kv, "3 e. Gamma'": hg,
                'A. r e. %s ( %s ` <. r , ( inl ` 3 ) >. ) e. %s' % (NV, PID, NV): pi, SSS(NV): B.ss(NV)},
               [('K', rst, B.gam[rst])])
    else:
        ex[STMT(GT(LMG['Q5']))] = gotocl(w, ph, mk['tv'], LMG['Q5'], B.ex[LAB(LMG['Q5'])])
        f0 = s([mf, s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o')], 'a1i', '( %s -> (/) =/= 1o )' % pm)], 'eqnetrd',
               '( %s -> ( TMfl ` m ) =/= 1o )' % pm)
        ex['A. m e. %s -. ( TMfl ` m ) = 1o' % NV] = s([s([f0], 'neneqd', '( %s -> -. ( TMfl ` m ) = 1o )' % pm)], 'ralrimiva',
                                                       '( %s -> A. m e. %s -. ( TMfl ` m ) = 1o )' % (ph, NV))
        ex[SSS(NV)] = B.ss(NV)
        B.call(R, 'tm2fbrg', {'A': LMG['Q4'], 'C': 'TMfl', 'E': LMG['Q6'], 'Q': GT(LMG['Q5']), 'N': NV}, ex, [])
        # skip
        f1_ = s([], 'f1oi', '( _I |` TMSt ) : TMSt -1-1-onto-> TMSt')
        ff = s([s([f1_, w.inst('f1of')], 'ax-mp', '( _I |` TMSt ) : TMSt --> TMSt')], 'a1i', '( %s -> ( _I |` TMSt ) : TMSt --> TMSt )' % ph)
        sv = s([s([], 'tmstfi', 'TMSt e. Fin')], 'elexi', 'TMSt e. _V')
        em = s([s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), s([sv], 'a1i', '( %s -> TMSt e. _V )' % ph), w.inst('elmapg')], 'syl2anc',
               '( %s -> ( ( _I |` TMSt ) e. ( TMSt ^m TMSt ) <-> ( _I |` TMSt ) : TMSt --> TMSt ) )' % ph)
        li = s([em, ff], 'mpbird', '( %s -> ( _I |` TMSt ) e. ( TMSt ^m TMSt ) )' % ph)
        sq = s([mk['seq']], 'eqcomd', '( %s -> TMSt = ( 2nd ` T ) )' % ph)
        mq = s([sq, sq], 'oveq12d', '( %s -> ( TMSt ^m TMSt ) = ( ( 2nd ` T ) ^m ( 2nd ` T ) ) )' % ph)
        lty = s([li, mq], 'eleqtrd', '( %s -> %s )' % (ph, LTY(LID)))
        pr = '( %s /\\ r e. %s )' % (ph, NV)
        rin = s([], 'simpr', '( %s -> r e. %s )' % (pr, NV))
        rt = s([rin, w.inst('elrabi')], 'syl', '( %s -> r e. TMSt )' % pr)
        fv = s([rt, w.inst('fvresi')], 'syl', '( %s -> ( ( _I |` TMSt ) ` r ) = r )' % pr)
        hl = s([s([fv, rin], 'eqeltrd', '( %s -> ( ( _I |` TMSt ) ` r ) e. %s )' % (pr, NV))], 'ralrimiva',
               '( %s -> A. r e. %s ( ( _I |` TMSt ) ` r ) e. %s )' % (ph, NV, NV))
        B.call(R, 'tm2flg', {'A': LMG['Q6'], 'E': 'E', 'F': LID, 'N': NV, "N'": NV},
               {LTY(LID): lty, SSS(NV): B.ss(NV), 'A. r e. %s ( %s ` r ) e. %s' % (NV, LID, NV): hl}, [])
    # the stacks
    e, nrm, out2 = renorm(w, ph, B, R, BCH, K8, PT=PTR, pv=pv)
    if hit:
        assert nrm == DFIN_EXG, (nrm, DFIN_EXG)
        dq = e
    else:
        r3, x3 = w.rewrite(nrm, {KV(RG): (rst, kif)}, ph)
        assert x3 == DFIN_EXG, x3
        dq = s([e, r3], 'eqtrd', '( %s -> %s = %s )' % (ph, triple_D(R.cur), DFIN_EXG))
    # the class
    e1, _ = egfacts(w, ph, B)
    if hit:
        ir = s([cnd], 'iftrued', '( %s -> %s = ( inl ` <. %s , %s >. ) )' % (ph, IFR, ZM(Si(RG)), ZU(Si(RG))))
        g1 = s([e1, ir], 'eqtrd', '( %s -> ( 1st ` %s ) = ( inl ` <. %s , %s >. ) )' % (ph, EGG, ZM(Si(RG)), ZU(Si(RG))))
        OP = '<. %s , %s >.' % (ZM(Si(RG)), ZU(Si(RG)))
        ne_ = s([s([s([], 'opex', '%s e. _V' % OP)], 'a1i', '( %s -> %s e. _V )' % (ph, OP)), vex_(w, ph, '(/)'), w.inst('inlneinr')], 'syl2anc',
                '( %s -> ( inl ` %s ) =/= ( inr ` (/) ) )' % (ph, OP))
        n1 = s([s([g1, ne_], 'eqnetrd', '( %s -> ( 1st ` %s ) =/= ( inr ` (/) ) )' % (ph, EGG))], 'neneqd',
               '( %s -> -. ( 1st ` %s ) = ( inr ` (/) ) )' % (ph, EGG))
        flv = s([n1], 'iffalsed', '( %s -> %s = 1o )' % (ph, IFX))
    else:
        ir = s([cnd], 'iffalsed', '( %s -> %s = ( inr ` (/) ) )' % (ph, IFR))
        g1 = s([e1, ir], 'eqtrd', '( %s -> ( 1st ` %s ) = ( inr ` (/) ) )' % (ph, EGG))
        flv = s([g1], 'iftrued', '( %s -> %s = (/) )' % (ph, IFX))
    fc = fincl(w, ph, flv, V)
    Dc = triple_D(R.cur)
    ceq = s([clnneq(w, ph, 'E', fc, NV, FINCL, Dc), clneq(w, ph, 'E', FINCL, dq, Dc, DFIN_EXG)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, CLN('E', NV, Dc), CLN('E', FINCL, DFIN_EXG)))
    t, C, D, n = hrrw(w, ph, R.tri, R.C0, R.cur, R.n, deq=ceq)
    neq = lineq(w, ph, n, '3', closure=Closure(w, ph, {}))
    hrrw(w, ph, t, C, D, n, neq=neq, qed=True)
    return w.run()


def tmiexgh():
    return epi(True)


def tmiexgn():
    return epi(False)


def tmiexg():
    lab = 'tmiexg'
    ph = PHG
    w = W(lab, 'Lean\'s ` extractGoF_runs ` at the machine: wherever ` extractGoF np nL snap acc s t nm nu ` is installed, with '
               'the pool ` W ` on ` np ` and the state ` ( m , used , t ) ` on ` nm ` , ` nu ` , ` acc ` , the machine runs the '
               'extraction loop to its stop index ` ExIt ` : the stacks hold the state there (the rest of the pool on ` np ` ), '
               'the flag says whether ` ( extractGo ).1 ` is ` some ` , within ` ( ( extractGo ).2 + 1 ) ( exC + 5 ) ` steps '
               '(` peekBra np ` , ~ tmiexgl at the families, ~ tmiexgh / ~ tmiexgn , ~ exres ).')
    s = w.s
    B = Lg(w, ph, TREE_EXG)
    c, mk = B.c, B.mk
    # the loop at the family
    eq = s([s([], 'eqid', '%s = %s' % (PF, PF))], 'a1i', '( %s -> %s = %s )' % (ph, PF, PF))
    tl, cc = inst(w, ph, 'tmiexgl', {PV: PF}, Bld(w, ph, c, {'%s = %s' % (PF, PF): eq}))
    Cl, Dl, nl = triple_parts(cc)
    # the prologue: peekBra np
    R = B.run()
    V_ = ENCL('W', 'X')
    vn0 = encl_ne0(w, ph, 'W', B.ww, 'X', B.xw)
    eqw, hg, tg = A8.word_split(w, ph, V_, B.gam[V_], vn0)
    HD, TL = A8.HD0(V_), A8.TL1(V_)
    kv = s([B.S0.vals['K'][1], eqw], 'eqtrd', '( %s -> ( D ` K ) = ( <" %s "> ++ %s ) )' % (ph, HD, TL))
    hb = s([B.ww, B.xw, w.inst('tmexhdb')], 'syl2anc', '( %s -> ( %s = 2 <-> W = (/) ) )' % (ph, HD))
    zc = zcomps(w, ph, B)
    s0 = s([B.pS, w.inst('exst0')], 'syl', '( %s -> %s = %s )' % (ph, Si('0'), Z0))
    rh, xh = w.rewrite(ZH(Si('0')), {Si('0'): (Z0, s0)}, ph)
    h0 = s([rh, zc['h']], 'eqtrd', '( %s -> %s = (/) )' % (ph, ZH(Si('0'))))
    nh0 = s([s([h0, s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o')], 'a1i', '( %s -> (/) =/= 1o )' % ph)], 'eqnetrd',
               '( %s -> %s =/= 1o )' % (ph, ZH(Si('0'))))], 'neneqd', '( %s -> -. %s )' % (ph, HIT('0')))
    he = s([s([B.ww], 'elexd', '( %s -> W e. _V )' % ph), w.inst('hasheq0')], 'syl', '( %s -> ( %s = 0 <-> W = (/) ) )' % (ph, NW))
    w0 = s([s([he], 'bicomd', '( %s -> ( W = (/) <-> %s = 0 ) )' % (ph, NW)),
            s([s([], 'eqcom', '( %s = 0 <-> 0 = %s )' % (NW, NW))], 'a1i', '( %s -> ( %s = 0 <-> 0 = %s ) )' % (ph, NW, NW))], 'bitrd',
           '( %s -> ( W = (/) <-> 0 = %s ) )' % (ph, NW))
    orb = s([s([nh0, w.inst('biorf')], 'syl', '( %s -> ( 0 = %s <-> ( %s \\/ 0 = %s ) ) )' % (ph, NW, HIT('0'), NW)),
             s([s([], 'orcom', '( ( %s \\/ 0 = %s ) <-> ( 0 = %s \\/ %s ) )' % (HIT('0'), NW, NW, HIT('0')))], 'a1i',
               '( %s -> ( ( %s \\/ 0 = %s ) <-> ( 0 = %s \\/ %s ) ) )' % (ph, HIT('0'), NW, NW, HIT('0')))], 'bitrd',
            '( %s -> ( 0 = %s <-> ( 0 = %s \\/ %s ) ) )' % (ph, NW, NW, HIT('0')))
    hb2 = s([s([hb, w0], 'bitrd', '( %s -> ( %s = 2 <-> 0 = %s ) )' % (ph, HD, NW)), orb], 'bitrd',
            '( %s -> ( %s = 2 <-> ( 0 = %s \\/ %s ) ) )' % (ph, HD, NW, HIT('0')))
    ifeq = s([hb2], 'ifbid', '( %s -> if ( %s = 2 , 1o , (/) ) = %s )' % (ph, HD, FLC('0')))
    pk = A8.peek_iface(w, ph, mk, RDBRA, HD, hg, ifeq, FLC('0'))
    N0 = NCL('0')
    ssS = s([s([], 'ssid', '%s C_ %s' % (S, S))], 'a1i', '( %s -> %s C_ %s )' % (ph, S, S))
    B.call(R, 'tm2lpk', {'A': LMG['Q1'], 'E': LMG['Q2'], 'K': 'K', 'F': RDBRA, 'Z': HD, 'X': TL, 'N': S, "N'": N0},
           {'( D ` K ) = ( <" %s "> ++ %s )' % (HD, TL): kv, "%s e. Gamma'" % HD: hg, WG(TL): tg,
            'A. r e. %s ( %s ` <. r , ( inl ` %s ) >. ) e. %s' % (S, RDBRA, HD, N0): pk, SSS(S): ssS, SSS(N0): B.ss(N0)}, [])
    tp, Cp, Dp, npr = R.tri, R.C0, R.cur, R.n
    assert Dp == CLN(LMG['Q2'], N0, 'D'), Dp
    # ( PF ` 0 ) = D
    z0n = closed(w, ph, '0nn0', '0 e. NN0')
    z0 = s([B.nw, w.inst('0elfz')], 'syl', '( %s -> 0 e. ( 0 ... %s ) )' % (ph, NW))
    fe = s([], 'eqidd', '( %s -> %s = %s )' % (ph, PF, PF))
    pv0, _ = fam_at(w, ph, mk, B.ne, fe, PF, 'j', 'NN0', PBG, '0', z0n, B.pbst('0', z0))
    r1, x1 = w.rewrite(PBG('0'), {Si('0'): (Z0, s0)}, ph)
    r2, x2 = w.rewrite(x1, {ZM(Z0): ('F', zc['m']), ZU(Z0): ('U', zc['u']), ZA(Z0): ('A', zc['a']), ZH(Z0): ('(/)', zc['h'])}, ph)
    IF0 = 'if ( (/) = 1o , %s , %s )' % (K3('0'), REST('0'))
    n01 = s([s([s([], '1n0', '1o =/= (/)')], 'necomi', '(/) =/= 1o')], 'neii', '-. (/) = 1o')
    r3, x3 = w.rewrite(x2, {IF0: (REST('0'), s([s([n01], 'iffalsei', '%s = %s' % (IF0, REST('0')))], 'a1i', '( %s -> %s = %s )' % (ph, IF0, REST('0'))))}, ph)
    d0 = s([B.ww, w.inst('tm2ldrop0')], 'syl', '( %s -> %s = W )' % (ph, DRP('0')))
    r4, x4 = w.rewrite(x3, {DRP('0'): ('W', d0)}, ph)
    back = {}
    for k, v in (('K', ENCL('W', 'X')), ("I'", ACCW('A')), ('K0', EWg('F', EGY)), ('J0', ENCL('U', 'R'))):
        back[v] = ('( D ` %s )' % k, s([c['( D ` %s ) = %s' % (k, v)]], 'eqcomd', '( %s -> %s = ( D ` %s ) )' % (ph, v, k)))
    r5, x5 = w.rewrite(x4, back, ph)
    chi = [('K', '( D ` K )'), ("I'", "( D ` I' )"), ('K0', '( D ` K0 )'), ('J0', '( D ` J0 )')]
    assert x5 == chain_text('D', chi), x5
    nst, out = stk_normalize(w, ph, mk, 'D', B.dd, B.ne, chi, B.gam, K8)
    assert out == [], out
    acc = pv0
    for st_, rhs in ((r1, x1), (r2, x2), (r3, x3), (r4, x4), (r5, x5), (nst, 'D')):
        acc = s([acc, st_], 'eqtrd', '( %s -> ( %s ` 0 ) = %s )' % (ph, PF, rhs))
    dq = s([acc], 'eqcomd', '( %s -> D = ( %s ` 0 ) )' % (ph, PF))
    NF0 = '( %s ` 0 )' % NFM
    nq = s([famval(w, ph, COND, '0', z0n)], 'eqcomd', '( %s -> %s = %s )' % (ph, N0, NF0))
    P0 = '( %s ` 0 )' % PF
    ceq = s([clnneq(w, ph, LMG['Q2'], nq, N0, NF0, 'D'), clneq(w, ph, LMG['Q2'], NF0, dq, 'D', P0)], 'eqtrd',
            '( %s -> %s = %s )' % (ph, Dp, CLN(LMG['Q2'], NF0, P0)))
    tp, Cp, Dp, npr = hrrw(w, ph, tp, Cp, Dp, npr, deq=ceq)
    assert Dp == Cl, (Dp, Cl)
    t1 = hrseq(w, ph, mk['phm'], tp, tl, Cp, Dp, Dl, npr, nl)
    # the epilogue by cases
    TRI3 = TRI(CLN(LMG['Q3'], S, PTR), CLN('E', FINCL, DFIN_EXG), '3')
    eh = s([s([], 'tmiexgh', ST_EH)], 'ex', '( %s -> ( %s -> %s ) )' % (ph, HIT(RG), TRI3))
    en = s([s([], 'tmiexgn', ST_EN)], 'ex', '( %s -> ( -. %s -> %s ) )' % (ph, HIT(RG), TRI3))
    te = s([eh, en], 'pm2.61d', '( %s -> %s )' % (ph, TRI3))
    NR_ = '( %s ` %s )' % (NFM, RG)
    assert Dl == CLN(LMG['Q3'], NR_, PTR), Dl
    te = hrssc(w, ph, mk['phm'], te, CLN(LMG['Q3'], S, PTR), CLN('E', FINCL, DFIN_EXG), '3', Dl,
               clnss(w, ph, LMG['Q3'], NR_, S, PTR, B.famss(RG, B.rn)))
    N1 = '( %s + %s )' % (npr, nl)
    t2 = hrseq(w, ph, mk['phm'], t1, te, Cp, Dl, CLN('E', FINCL, DFIN_EXG), N1, '3')
    NT = '( %s + 3 )' % N1
    # the budget
    e1, e2 = egfacts(w, ph, B)
    EG2 = '( 2nd ` %s )' % EGG
    a1 = s([B.ln, B.gn], 'jca', '( %s -> ( L e. NN /\\ G e. NN0 ) )' % ph)
    A2 = '( ( L e. NN /\\ G e. NN0 ) /\\ W e. Word NN0 )'
    a2 = s([a1, B.ww], 'jca', '( %s -> %s )' % (ph, A2))
    A3 = '( %s /\\ F e. NN0 )' % A2
    a3 = s([a2, B.fn], 'jca', '( %s -> %s )' % (ph, A3))
    A4 = '( %s /\\ U e. Word NN0 )' % A3
    a4 = s([a3, B.uw], 'jca', '( %s -> %s )' % (ph, A4))
    A5 = '( %s /\\ A e. Tbl )' % A4
    a5 = s([a4, B.an], 'jca', '( %s -> %s )' % (ph, A5))
    ec = s([a5, w.inst('extractgocl')], 'syl', '( %s -> %s e. ( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 ) )' % (ph, EGG))
    eg2 = s([ec, w.inst('xp2nd')], 'syl', '( %s -> %s e. NN0 )' % (ph, EG2))
    cl = Closure(w, ph, {v: ('NN0', c['%s e. NN0' % v]) for v in ('H', 'Q')})
    cl.leaf('L', 'NN0', B.l0)
    tq = s([s([c['Q e. NN0'], w.inst('tmbcl')], 'syl', '( %s -> ( TMB ` Q ) e. NN )' % ph)], 'nnnn0d', '( %s -> ( TMB ` Q ) e. NN0 )' % ph)
    cl.leaf('( TMB ` Q )', 'NN0', tq)
    exn = cl.mem(EXC_, 'NN0')
    cl2 = Closure(w, ph, {EXC_: ('NN0', exn), EG2: ('NN0', eg2), RG: ('NN0', B.rn)})
    mul = s([cl2.mem(RG, 'RR'), cl2.mem(EG2, 'RR'), cl2.mem(EXC_, 'RR'), cl2.ge0(EXC_), e2], 'lemul1ad',
            '( %s -> ( %s x. %s ) <_ ( %s x. %s ) )' % (ph, RG, EXC_, EG2, EXC_))
    le = linarith(w, ph, [mul, e2, cl2.ge0(EG2), cl2.ge0(EXC_)], '%s <_ %s' % (NT, EXGB), closure=cl2, products=True, atoms=[EXC_, EG2, RG])
    hrle(w, ph, mk['phm'], t2, Cp, CLN('E', FINCL, DFIN_EXG), NT, EXGB, cl2.mem(EXGB, 'NN0'), le, qed=True)
    return w.run()


STMTS = {'tmiexgh': ST_EH, 'tmiexgn': ST_EN}

if __name__ == '__main__':
    for l in SEL:
        globals()[l]()
