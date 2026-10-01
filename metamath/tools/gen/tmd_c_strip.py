"""T-MD: the strip loop of ` canonNum ` (TM/Canon.lean, blueprint D2): a peek
tests the top of the stack, a zero letter is popped and the loop continues,
anything else stops it unconsumed.  Shape: T3's guarded dropping scan
(tools/gen/t3_i_zb.py): ~ tm2fsp1 (continue), ~ tm2fspw (the run, by
~ tm2hwrd ), ~ tm2fsp0 (exit), ~ tm2fsp (the fragment)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from tmdlib import *
from t2_c_mov import constfty

SEL = sys.argv[1:]
def want(l): return not SEL or l in SEL

OPTK = '( %s |_| 1o )' % GK
POPST = POP('K', "F'", GA)
BRST = BRANCH('C', POPST, GE)
TL = lambda x: '( %s substr <. 1 , ( # ` %s ) >. )' % (x, x)


def typings(w, ph, c, tv):
    """the statement typings of STM_SP's parts"""
    al, el = c[LAB('A')], c[LAB('E')]
    ga = gotocl(w, ph, tv, 'A', al); ge = gotocl(w, ph, tv, 'E', el)
    po = popcl(w, ph, tv, 'K', "F'", GA, c['K e. %s' % DG], c[RTY("F'", 'K')], ga)
    br = brcl(w, ph, tv, 'C', POPST, GE, c[CTY('C')], po, ge)
    fa = constfty(w, ph, 'A', LL, al); fe = constfty(w, ph, 'E', LL, el)
    return dict(ga=ga, ge=ge, po=po, br=br, fa=fa, fe=fe)


def facts_common(w, av, A_, c, ty, tv):
    return {'T e. V': A_(tv, 'T e. V'), 'K e. %s' % DG: A_(c['K e. %s' % DG], 'K e. %s' % DG),
            RTY('F', 'K'): A_(c[RTY('F', 'K')], RTY('F', 'K')), RTY("F'", 'K'): A_(c[RTY("F'", 'K')], RTY("F'", 'K')),
            CTY('C'): A_(c[CTY('C')], CTY('C')),
            STMT(GA): A_(ty['ga'], STMT(GA)), STMT(GE): A_(ty['ge'], STMT(GE)),
            STMT(POPST): A_(ty['po'], STMT(POPST)), STMT(BRST): A_(ty['br'], STMT(BRST)),
            '%s e. ( %s ^m %s )' % (CONST('A'), LL, SS): A_(ty['fa'], '%s e. ( %s ^m %s )' % (CONST('A'), LL, SS)),
            '%s e. ( %s ^m %s )' % (CONST('E'), LL, SS): A_(ty['fe'], '%s e. ( %s ^m %s )' % (CONST('E'), LL, SS))}


def tm2fsp1():
    lab = 'tm2fsp1'
    tree, ph = TREE_SP1, cj(TREE_SP1)
    D1 = UP('D', 'K', XR); TXR = CC(TL('x'), 'R'); D2 = UP('D', 'K', TXR)
    X0 = '( x ` 0 )'
    NV1 = NV('F', 'v', X0); NV2 = NV("F'", NV1, X0)
    w = W(lab, 'One iteration of the strip loop of ` canonNum ` (TM/Canon.lean): the peek at '
               'stack ` K ` reads a zero letter, the test passes, the letter is popped and '
               'discarded (the pop handler ` F\' ` is Lean\'s ` fun v _ => v ` ) and the machine '
               'loops, the state staying in ` N ` .  Lean: ` stripLoop_loop ` , case 2.  Shape: '
               '~ tm2fzb1 ; the untaken exit branch is ` goto E ` .')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, dd, rw, nss, hc = c['K e. %s' % DG], c[STKD('D')], c[WRD('R', GK)], c[SSS('N')], c[HSPC('N')]
    b0k, xw, xn = c['B0 C_ %s' % GK], c[WRD('x', 'B0')], c['x =/= (/)']
    ty = typings(w, ph, c, tv)
    xwg = sswordd(w, ph, xw, 'x', 'B0', GK, b0k)
    x0 = w.s([xw, xn, w.inst('wrdfv0')], 'syl2anc', '( %s -> %s e. B0 )' % (ph, X0))
    x0k = w.s([b0k, x0], 'sseldd', '( %s -> %s e. %s )' % (ph, X0, GK))
    tlw = w.s([xw, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B0 )' % (ph, TL('x')))
    tlwg = sswordd(w, ph, tlw, TL('x'), 'B0', GK, b0k)
    xrw = ccatw(w, ph, xwg, rw, 'x', 'R', GK)
    txrw = ccatw(w, ph, tlwg, rw, TL('x'), 'R', GK)
    xrn = w.s([xwg, xn, rw, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, XR))
    d1cl = updcl(w, ph, 'D', 'K', XR, tv, dd, kk, xrw)
    d2cl = updcl(w, ph, 'D', 'K', TXR, tv, dd, kk, txrw)

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, STKD('D')); kka = A_(kk, 'K e. %s' % DG)
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        nssa = A_(nss, SSS('N'))
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, SS))
        x0b = A_(x0, '%s e. B0' % X0); x0ka = A_(x0k, '%s e. %s' % (X0, GK))
        hca = A_(hc, HSPC('N'))
        BODY = '( ( C ` %s ) = 1o /\\ %s e. N )' % (NV('F', 'r', 'z'), NV("F'", NV('F', 'r', 'z'), 'z'))
        h, _ = ral2at(w, av, BODY, hca, vn, vn, X0, x0b)
        ct = w.s([h], 'simpld', '( %s -> ( C ` %s ) = 1o )' % (av, NV1))
        n2 = w.s([h], 'simprd', '( %s -> %s e. N )' % (av, NV2))
        nv1s = hdapply(w, av, 'F', A_(c[RTY('F', 'K')], RTY('F', 'K')), 'v', vv, X0, x0ka)
        nv2s = w.s([nssa, n2], 'sseldd', '( %s -> %s e. %s )' % (av, NV2, SS))
        xrv = w.s([A_(xrw, WRD(XR, GK))], 'elexd', '( %s -> %s e. _V )' % (av, XR))
        d1k = updkv(w, av, 'D', 'K', XR, tva, dda, kka, xrv)
        xnn = w.s([A_(xrn, '%s =/= (/)' % XR)], 'neneqd', '( %s -> -. %s = (/) )' % (av, XR))
        xwga = A_(xwg, WRD('x', GK)); rwa = A_(rw, WRD('R', GK)); xna = A_(xn, 'x =/= (/)')
        nnx = w.s([xwga, xna, w.inst('lennncl')], 'syl2anc', '( %s -> ( # ` x ) e. NN )' % av)
        xpos = w.s([nnx, w.inst('nngt0')], 'syl', '( %s -> 0 < ( # ` x ) )' % av)
        rfv = w.s([xwga, rwa, xpos, w.inst('ccatfv0')], 'syl3anc', '( %s -> ( %s ` 0 ) = %s )' % (av, XR, X0))
        rtl = w.s([xwga, xna, rwa, w.inst('wrdtlcc')], 'syl3anc', '( %s -> %s = %s )' % (av, TL(XR), TXR))
        tdk = w.s([tva, dda], 'jca', '( %s -> ( T e. V /\\ D e. %s ) )' % (av, STK_T))
        k2b = w.s([A_(xrw, WRD(XR, GK)), A_(txrw, WRD(TXR, GK))], 'jca', '( %s -> ( %s e. Word %s /\\ %s e. Word %s ) )' % (av, XR, GK, TXR, GK))
        up2s = w.s([tdk, kka, k2b, w.inst('tm2stkup2')], 'syl3anc', '( %s -> %s = %s )' % (av, UP(D1, 'K', TXR), D2))
        avv = w.s([A_(c[LAB('A')], LAB('A'))], 'elexd', '( %s -> A e. _V )' % av)
        rga = w.s([avv, nv2s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = A )' % (av, CONST('A'), NV2))
        facts = facts_common(w, av, A_, c, ty, tv)
        facts.update({'v e. %s' % SS: vv, '%s e. %s' % (NV1, SS): nv1s, '%s e. %s' % (NV2, SS): nv2s,
                      STKD(D1): A_(d1cl, STKD(D1)), STKD(D2): A_(d2cl, STKD(D2))})
        rules = {'( %s ` K )' % D1: (XR, d1k), '( %s ` 0 )' % XR: (X0, rfv), TL(XR): (TXR, rtl),
                 UP(D1, 'K', TXR): (D2, up2s), '( %s ` %s )' % (CONST('A'), NV2): ('A', rga)}
        ifr = {'%s = (/)' % XR: (False, xnn), '( C ` %s ) = 1o' % NV1: (True, ct)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM_SP, '<. v , %s >.' % D1)
        wr = '<. ( inl ` A ) , <. %s , %s >. >.' % (NV2, D2)
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(c[MEQ('A', STM_SP)], MEQ('A', STM_SP))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = ( %s %s <. v , %s >. ) )' % (av, SA('T'), D1, STM_SP, SA('T'), D1))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , %s >. ) = %s )' % (av, SA('T'), D1, res))
        return fin, NV2, n2
    hstepc2(w, ph, 'T', 'M', 'A', 'A', 'N', 'N', D1, D2, (c[MEQ('A', STM_SP)], phm),
            c[LAB('A')], c[LAB('A')], nss, nss, d1cl, d2cl, body, qed=True)
    return w.run()


def tm2fsp0():
    lab = 'tm2fsp0'
    tree, ph = TREE_SP0, cj(TREE_SP0)
    NV1 = NV('F', 'v', 'Y')
    w = W(lab, 'The exit of the strip loop: the peek reads the stop letter ` Y ` (a one bit or '
               'the marker), the test fails and the machine leaves for ` E ` with the stack '
               'untouched, the state staying in ` N ` .  Lean: ` stripLoop_loop ` , cases 1 and 3.')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, dd, dke, nss, he = c['K e. %s' % DG], c[STKD('D')], c['( D ` K ) = %s' % YX], c[SSS('N')], c[HSPE('N', 'Y')]
    yy, xx = c['Y e. %s' % GK], c[WRD('X', GK)]
    ty = typings(w, ph, c, tv)
    s1y = s1w(w, ph, yy, 'Y', GK)
    s1n = w.s([], 's1nz', '<" Y "> =/= (/)'); s1na = w.s([s1n], 'a1i', '( %s -> <" Y "> =/= (/) )' % ph)
    yxn = w.s([s1y, s1na, xx, w.inst('ccatn0')], 'syl3anc', '( %s -> %s =/= (/) )' % (ph, YX))

    def body(av):
        def A_(st, f): return w.s([st], 'adantr', '( %s -> %s )' % (av, f))
        tva = A_(tv, 'T e. V'); dda = A_(dd, STKD('D'))
        vn = w.s([], 'simpr', '( %s -> v e. N )' % av)
        nssa = A_(nss, SSS('N'))
        vv = w.s([nssa, vn], 'sseldd', '( %s -> v e. %s )' % (av, SS))
        hea = A_(he, HSPE('N', 'Y'))
        BODY = '( -. ( C ` %s ) = 1o /\\ %s e. N )' % (NV('F', 'm', 'Y'), NV('F', 'm', 'Y'))
        h, _ = ralat(w, av, BODY, hea, vn)
        cf = w.s([h], 'simpld', '( %s -> -. ( C ` %s ) = 1o )' % (av, NV1))
        n1 = w.s([h], 'simprd', '( %s -> %s e. N )' % (av, NV1))
        nv1s = w.s([nssa, n1], 'sseldd', '( %s -> %s e. %s )' % (av, NV1, SS))
        yxnn = w.s([A_(yxn, '%s =/= (/)' % YX)], 'neneqd', '( %s -> -. %s = (/) )' % (av, YX))
        yj = w.s([A_(yy, 'Y e. %s' % GK), A_(xx, WRD('X', GK))], 'jca', '( %s -> ( Y e. %s /\\ X e. Word %s ) )' % (av, GK, GK))
        yfv = w.s([yj, w.inst('ccats1fv0')], 'syl', '( %s -> ( %s ` 0 ) = Y )' % (av, YX))
        evv = w.s([A_(c[LAB('E')], LAB('E'))], 'elexd', '( %s -> E e. _V )' % av)
        rge = w.s([evv, nv1s, w.inst('fvconst2g')], 'syl2anc', '( %s -> ( %s ` %s ) = E )' % (av, CONST('E'), NV1))
        facts = facts_common(w, av, A_, c, ty, tv)
        facts.update({'v e. %s' % SS: vv, '%s e. %s' % (NV1, SS): nv1s, STKD('D'): dda})
        rules = {'( D ` K )': (YX, A_(dke, '( D ` K ) = %s' % YX)), '( %s ` 0 )' % YX: ('Y', yfv),
                 '( %s ` %s )' % (CONST('E'), NV1): ('E', rge)}
        ifr = {'%s = (/)' % YX: (False, yxnn), '( C ` %s ) = 1o' % NV1: (False, cf)}
        ex = Exec(w, av, 'T', facts, rules=rules, ifrules=ifr)
        st, res = ex.run(STM_SP, '<. v , D >.')
        wr = '<. ( inl ` E ) , <. %s , D >. >.' % NV1
        assert res == wr, 'GOT %s\nWANT %s' % (res, wr)
        meqa = A_(c[MEQ('A', STM_SP)], MEQ('A', STM_SP))
        o1 = w.s([meqa], 'oveq1d', '( %s -> ( ( M ` A ) %s <. v , D >. ) = ( %s %s <. v , D >. ) )' % (av, SA('T'), STM_SP, SA('T')))
        fin = w.s([o1, st], 'eqtrd', '( %s -> ( ( M ` A ) %s <. v , D >. ) = %s )' % (av, SA('T'), res))
        return fin, NV1, n1
    hstepc2(w, ph, 'T', 'M', 'A', 'E', 'N', 'N', 'D', 'D', (c[MEQ('A', STM_SP)], phm),
            c[LAB('A')], c[LAB('E')], nss, nss, dd, dd, body, qed=True)
    return w.run()


CLSP = lambda X: CLN('A', 'N', UP('D', 'K', CC(X, 'R')))
JSP = '( p e. _V |-> %s )' % CLSP('p')


def jsp(w, ante, U, ucl, nex):
    """( ante -> ( JSP ` U ) = CLSP( U ) )"""
    aq = '( %s /\\ p = %s )' % (ante, U)
    lp = w.s([], 'simpr', '( %s -> p = %s )' % (aq, U))
    st, mid = W.congr(w, CLSP('p'), {'p': U}, aq, {'p': lp})
    tgt = CLSP(U)
    assert mid == tgt, mid
    eqi = w.s([], 'eqid', '%s = %s' % (JSP, JSP))
    uv = w.s([ucl], 'elexd', '( %s -> %s e. _V )' % (ante, U))
    sn1 = w.s([], 'snex', '{ ( inl ` A ) } e. _V'); sn1a = w.s([sn1], 'a1i', '( %s -> { ( inl ` A ) } e. _V )' % ante)
    UPS = UP('D', 'K', CC(U, 'R'))
    sn2 = w.s([], 'snex', '{ %s } e. _V' % UPS); sn2a = w.s([sn2], 'a1i', '( %s -> { %s } e. _V )' % (ante, UPS))
    xp1 = w.s([nex, sn2a, w.inst('xpexg')], 'syl2anc', '( %s -> ( N X. { %s } ) e. _V )' % (ante, UPS))
    cex = w.s([sn1a, xp1, w.inst('xpexg')], 'syl2anc', '( %s -> %s e. _V )' % (ante, tgt))
    return w.s([st, eqi, uv, cex], 'fvmptd2', '( %s -> ( %s ` %s ) = %s )' % (ante, JSP, U, tgt))


def tm2fspw():
    lab = 'tm2fspw'
    tree, ph = TREE_SPW, cj(TREE_SPW)
    PH1 = cj(PH_SP1)
    phx = '( %s /\\ x e. Word B0 )' % PH1
    ante2 = '( %s /\\ x =/= (/) )' % phx
    HRx = TRI('( %s ` x )' % JSP, '( %s ` %s )' % (JSP, TL('x')), '1')
    HYPJ = 'A. x e. Word B0 ( x =/= (/) -> %s )' % HRx
    ZCJ = '( %s ` (/) ) C_ %s' % (JSP, CFG_T)
    w = W(lab, 'The strip loop pops a run ` W ` of zero letters: ~ tm2hwrd over ~ tm2fsp1 , the '
               'invariant indexed by the part of the run still on the stack.  Lean: the '
               'induction of ` stripLoop_loop ` .')
    one = w.s([], 'tm2fsp1', '( %s -> %s )' % (ante2, TRI(CLSP('x'), CLSP(TL('x')), '1')))
    c2 = Ctx(w, ante2, TREE_SP1)
    xw1 = c2[WRD('x', 'B0')]
    tlw1 = w.s([xw1, w.inst('swrdcl')], 'syl', '( %s -> %s e. Word B0 )' % (ante2, TL('x')))
    sev = w.s([], 'fvex', '%s e. _V' % SS)
    sev2a = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ante2, SS))
    nex2 = w.s([c2[SSS('N')], sev2a, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ante2)
    jx = jsp(w, ante2, 'x', xw1, nex2)
    jt = jsp(w, ante2, TL('x'), tlw1, nex2)
    r1 = w.s([jt], 'opeq1d', '( %s -> <. ( %s ` %s ) , 1 >. = <. %s , 1 >. )' % (ante2, JSP, TL('x'), CLSP(TL('x'))))
    r2 = w.s([r1], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ante2, TRI(CLSP('x'), '( %s ` %s )' % (JSP, TL('x')), '1'), TRI(CLSP('x'), CLSP(TL('x')), '1')))
    o1 = w.s([r2, one], 'mpbird', '( %s -> %s )' % (ante2, TRI(CLSP('x'), '( %s ` %s )' % (JSP, TL('x')), '1')))
    r3 = w.s([jx], 'breq1d', '( %s -> ( %s <-> %s ) )' % (ante2, HRx, TRI(CLSP('x'), '( %s ` %s )' % (JSP, TL('x')), '1')))
    o2 = w.s([r3, o1], 'mpbird', '( %s -> %s )' % (ante2, HRx))
    ex1 = w.s([o2], 'ex', '( %s -> ( x =/= (/) -> %s ) )' % (phx, HRx))
    hyp = w.s([ex1], 'ralrimiva', '( %s -> %s )' % (PH1, HYPJ))
    hypa = w.s([hyp], 'adantr', '( %s -> %s )' % (ph, HYPJ))
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, dd, rw, nss, ww = c['K e. %s' % DG], c[STKD('D')], c[WRD('R', GK)], c[SSS('N')], c[WRD('W', 'B0')]
    sevpa = w.s([sev], 'a1i', '( %s -> %s e. _V )' % (ph, SS))
    nexp = w.s([nss, sevpa, w.inst('ssexg')], 'syl2anc', '( %s -> N e. _V )' % ph)
    w0 = w.s([], 'wrd0', '(/) e. Word %s' % GK); w0a = w.s([w0], 'a1i', '( %s -> (/) e. Word %s )' % (ph, GK))
    w0b = w.s([], 'wrd0', '(/) e. Word B0'); w0ba = w.s([w0b], 'a1i', '( %s -> (/) e. Word B0 )' % ph)
    jz = jsp(w, ph, '(/)', w0ba, nexp)
    zrw = ccatw(w, ph, w0a, rw, '(/)', 'R', GK)
    dzcl = updcl(w, ph, 'D', 'K', CC('(/)', 'R'), tv, dd, kk, zrw)
    cls = cfgcl(w, ph, 'A', 'N', UP('D', 'K', CC('(/)', 'R')), tv, c[LAB('A')], nss, dzcl)
    zc = w.s([jz, cls], 'eqsstrd', '( %s -> %s )' % (ph, ZCJ))
    n1 = w.s([], '1nn0', '1 e. NN0'); n1a = w.s([n1], 'a1i', '( %s -> 1 e. NN0 )' % ph)
    pj = w.s([n1a, zc], 'jca', '( %s -> ( 1 e. NN0 /\\ %s ) )' % (ph, ZCJ))
    ant = w.s([phm, pj, hypa], '3jca', '( %s -> ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) )' % (ph, PHM, ZCJ, HYPJ))
    ant2 = w.s([ant, ww], 'jca', '( %s -> ( ( %s /\\ ( 1 e. NN0 /\\ %s ) /\\ %s ) /\\ W e. Word B0 ) )' % (ph, PHM, ZCJ, HYPJ))
    RUN0 = TRI('( %s ` W )' % JSP, '( %s ` (/) )' % JSP, '( ( # ` W ) x. 1 )')
    run = w.s([ant2, w.inst('tm2hwrd')], 'syl', '( %s -> %s )' % (ph, RUN0))
    hn = w.s([ww, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % ph)
    hc_ = w.s([hn], 'nn0cnd', '( %s -> ( # ` W ) e. CC )' % ph)
    m1 = w.s([hc_, w.inst('mulrid')], 'syl', '( %s -> ( ( # ` W ) x. 1 ) = ( # ` W ) )' % ph)
    q1 = w.s([jz, m1], 'opeq12d', '( %s -> <. ( %s ` (/) ) , ( ( # ` W ) x. 1 ) >. = <. %s , ( # ` W ) >. )' % (ph, JSP, CLSP('(/)')))
    q2 = w.s([q1], 'breq2d', '( %s -> ( %s <-> %s ) )' % (ph, RUN0, TRI('( %s ` W )' % JSP, CLSP('(/)'), '( # ` W )')))
    r4 = w.s([q2, run], 'mpbid', '( %s -> %s )' % (ph, TRI('( %s ` W )' % JSP, CLSP('(/)'), '( # ` W )')))
    jw = jsp(w, ph, 'W', ww, nexp)
    q3 = w.s([jw], 'breq1d', '( %s -> ( %s <-> %s ) )' % (ph, TRI('( %s ` W )' % JSP, CLSP('(/)'), '( # ` W )'), TRI(CLSP('W'), CLSP('(/)'), '( # ` W )')))
    w.qed([q3, r4], 'mpbid', '( %s -> %s )' % (ph, TRI(CLSP('W'), CLSP('(/)'), '( # ` W )')))
    return w.run()


def tm2fsp():
    lab = 'tm2fsp'
    tree, ph = TREE_SP, cj(TREE_SP)
    DM = UP('D', 'K', YX)
    w = W(lab, 'The strip loop of ` canonNum ` , assembled: the run ` W ` of zero letters on top of '
               'stack ` K ` is popped and the stop letter ` Y ` below it is peeked and left in place, '
               'in ` ( # ` W ) + 1 ` steps, the state staying in ` N ` .  Lean: ` stripLoop_runs ` '
               '(the run is ` dropZeros ` \'s complement, blueprint D2).')
    c = Ctx(w, ph, tree)
    phm = c[PHM]
    tv = w.s([phm, w.inst('simpl')], 'syl', '( %s -> T e. V )' % ph)
    kk, dd, xx, yy, nss = c['K e. %s' % DG], c[STKD('D')], c[WRD('X', GK)], c['Y e. %s' % GK], c[SSS('N')]
    hc, he, ww = c[HSPC('N')], c[HSPE('N', 'Y')], c[WRD('W', 'B0')]
    yxw = ccatw(w, ph, s1w(w, ph, yy, 'Y', GK), xx, S1('Y'), 'X', GK)
    # the loop at R := YX
    loop = applylem(w, ph, 'tm2fspw',
                    ((((phm, c[MEQ('A', STM_SP)]), ((c[LAB('A')], c[LAB('E')], kk), ((c[RTY('F', 'K')], c[RTY("F'", 'K')], c[CTY('C')]), c['B0 C_ %s' % GK])),
                       ((dd, yxw), (nss, hc))), ww)),
                    TRI(CLN('A', 'N', UP('D', 'K', CC('W', YX))), CLN('A', 'N', UP('D', 'K', CC('(/)', YX))), '( # ` W )'))
    lidy = w.s([yxw, w.inst('ccatlid')], 'syl', '( %s -> ( (/) ++ %s ) = %s )' % (ph, YX, YX))
    MID = CLN('A', 'N', DM)
    loop2, _, _, _ = hrrw(w, ph, loop, CLN('A', 'N', UP('D', 'K', CC('W', YX))), CLN('A', 'N', UP('D', 'K', CC('(/)', YX))), '( # ` W )',
                          deq=clneq(w, ph, 'A', 'N', upeq(w, ph, 'D', 'K', lidy, CC('(/)', YX), YX), UP('D', 'K', CC('(/)', YX)), DM))
    # the exit at D := DM
    dmcl = updcl(w, ph, 'D', 'K', YX, tv, dd, kk, yxw)
    dmk = updkv(w, ph, 'D', 'K', YX, tv, dd, kk, elv(w, ph, yxw, YX))
    exit_ = applylem(w, ph, 'tm2fsp0',
                     ((phm, c[MEQ('A', STM_SP)]), ((c[LAB('A')], c[LAB('E')], kk), ((c[RTY('F', 'K')], c[RTY("F'", 'K')], c[CTY('C')]), c['B0 C_ %s' % GK])),
                      ((dmcl, dmk, (yy, xx)), (nss, he))),
                     TRI(MID, CLN('E', 'N', DM), '1'))
    w.qed([phm, loop2, exit_], 'syl3anc', '( %s -> %s )' % (ph, CONCL_SP))
    return w.run()


if __name__ == '__main__':
    if want('tm2fsp1'): tm2fsp1()
    if want('tm2fsp0'): tm2fsp0()
    if want('tm2fspw'): tm2fspw()
    if want('tm2fsp'): tm2fsp()
