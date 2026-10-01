"""Sortie EF56: the zeta contour for chosen heights, abscissa and cuts (ef6core; Lean contour_zeta body)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts

Z1 = {'N': '1'}


def gen_core():
    w = W('ef6core', 'Lean ` contour_zeta ` for chosen heights ` - U ` , ` V ` , abscissa ` S ` and cuts ` G ` : ` abs ( PS + 2 pi i SC - 2 pi i Y ) <_ 2 pi 1000000000 ( P1 + P2 ) ` at the character mod 1 ( ~ ef6id , ~ ef6bk , ~ ef6zs , ~ ef4hed , ~ ef6rx , ~ ef3left , ~ ef6pw , ~ ef6nm ).')
    A0, G = ante_of(S['ef6core'])
    c = Ctx(w, A0)
    g = c.g
    yr = g('Y e. RR'); y100 = g('; ; 1 0 0 <_ Y'); tr = g('T e. RR'); t2 = g('2 <_ T')
    ur = g('U e. RR'); vr = g('V e. RR'); tu = g('T <_ U'); u1 = g('U <_ ( T + 1 )'); tv = g('T <_ V'); v1 = g('V <_ ( T + 1 )')
    sr = g('S e. RR'); s916 = g('( 9 / ; 1 6 ) <_ S'); s58 = g('S <_ ( 5 / 8 )')
    hg = {ETA: g(HGDX(ETA)), GF: g(HGDX(GF))}
    ns = {ETA: g('-. S e. ( Re " %s )' % BZE4), GF: g('-. S e. ( Re " %s )' % BZG4)}
    BZ4F = {ETA: BZE4, GF: BZG4}
    mn0 = g('M e. NN0'); vm = g('V <_ ( -u U + ( M / 2 ) )'); mt = g('( -u U + ( M / 2 ) ) <_ ( T + 2 )')
    kn = g('K e. NN')
    av = {F: g('A. j e. ( 1 ..^ K ) -. ( G ` j ) e. ( Im " %s )' % BZ4F[F]) for F in (ETA, GF)}
    rng = g('A. j e. ( 0 ... K ) ( -u U <_ ( G ` j ) /\\ ( G ` j ) <_ V )')
    f = c1_facts(w, c, yr, y100)
    lv = {'T': tr, 'U': ur, 'V': vr, 'S': sr, C1: f['c1r']}
    nur = c([ur], 'renegcld', '-u U e. RR'); ntr = c([tr], 'renegcld', '-u T e. RR')
    # 1. the contour meets no zero of ETA, GF
    cbr, rb0 = cbvral(w, '( 0 ... K )', 'j', 'e', '( -u U <_ ( G ` j ) /\\ ( G ` j ) <_ V )')
    RNG = 'A. j e. ( 0 ... K ) ( -u U <_ ( G ` j ) /\\ ( G ` j ) <_ V )'
    rnge = c([rng, c.a1(cbr, '( %s <-> A. e e. ( 0 ... K ) %s )' % (RNG, rb0))], 'mpbid', 'A. e e. ( 0 ... K ) %s' % rb0)
    t2r = c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')
    NZ, LINES, LEFT2 = {}, {}, {}
    for F in (ETA, GF):
        GA, GB = GOOD(PTL('v', '-u U'), F, L4), GOOD(PTL('v', 'V'), F, L4)
        NA, NB = '( %s ` %s ) =/= 0' % (F, PTL('v', '-u U')), '( %s ` %s ) =/= 0' % (F, PTL('v', 'V'))
        NZF = 'A. v e. ( ( 1 / 2 ) [,] 3 ) ( %s /\\ %s )' % (NA, NB)
        imp = w.s([w.s([], 'simpl', '( %s -> %s )' % (GA, NA)), w.s([], 'simpl', '( %s -> %s )' % (GB, NB))], 'anim12i', '( ( %s /\\ %s ) -> ( %s /\\ %s ) )' % (GA, GB, NA, NB))
        nz = c([hg[F], c.a1(w.s([imp], 'ralimi', '( %s -> %s )' % (HGDX(F), NZF)), '( %s -> %s )' % (HGDX(F), NZF))], 'mpd', NZF)
        body = '-. ( G ` j ) e. ( Im " %s )' % BZ4F[F]
        cb1, bb1 = cbvral(w, '( 1 ..^ K )', 'j', 'e', body)
        ave = c([av[F], c.a1(cb1, '( A. j e. ( 1 ..^ K ) %s <-> A. e e. ( 1 ..^ K ) %s )' % (body, bb1))], 'mpbid', 'A. e e. ( 1 ..^ K ) %s' % bb1)
        LN = tsub(S['ef6ln'], {'F': F})
        lna, lnc = ante_of(LN)
        ln = c([rebuild(w, c, lna, {NZF: nz, 'A. e e. ( 1 ..^ K ) %s' % bb1: ave, 'A. e e. ( 0 ... K ) %s' % rb0: rnge, '-. S e. ( Re " %s )' % BZ4F[F]: ns[F]}), w.inst('ef6ln')], 'syl', lnc)
        NZ[F] = nz
        LINES[F], LEFT2[F] = conj_split(w, A0, ln)
    def left_on(F, hi, hle):
        TL = '( %s ` %s ) =/= 0' % (F, PTL('S', 't'))
        ss = c([c([nur, t2r], 'jca', '( -u U e. RR /\\ ( T + 2 ) e. RR )'), c([c([nur], 'leidd', '-u U <_ -u U'), hle], 'jca', '( -u U <_ -u U /\\ %s <_ ( T + 2 ) )' % hi), w.inst('iccss')], 'syl2anc',
               '( -u U [,] %s ) C_ ( -u U [,] ( T + 2 ) )' % hi)
        return c([LEFT2[F], c([ss, w.inst('ssralv')], 'syl', '( A. t e. ( -u U [,] ( T + 2 ) ) %s -> A. t e. ( -u U [,] %s ) %s )' % (TL, hi, TL))], 'mpd', 'A. t e. ( -u U [,] %s ) %s' % (hi, TL))
    vle = lin8(w, A0, [v1], 'V <_ ( T + 2 )', lv)
    PM = '( -u U + ( M / 2 ) )'
    # 2. the contour identity
    sc1 = lin8(w, A0, [s58, f['c1g']], 'S < %s' % C1, lv)
    IDs = tsub(S['ef6id'], {})
    ida, idc = ante_of(IDs)
    spec = {'S < %s' % C1: sc1}
    for F in (ETA, GF):
        spec[top_and(ZFX(F))[0]] = LINES[F]
        spec[top_and(ZFX(F))[1]] = left_on(F, 'V', vle)
    idst = c([rebuild(w, c, ida, spec), w.inst('ef6id')], 'syl', idc)
    ident, clos = conj_split(w, A0, idst)
    # 3. residue bookkeeping and the zero sums
    BKs = tsub(S['ef6bk'], {'C': C1})
    bka, bkc = ante_of(BKs)
    bk = c([rebuild(w, c, bka, {'Y e. RR+': f['yp'], '( 1 / 2 ) <_ S': lin8(w, A0, [s916], '( 1 / 2 ) <_ S', lv), 'S < 1': lin8(w, A0, [s58], 'S < 1', lv),
                               '%s e. RR' % C1: f['c1r'], '1 < %s' % C1: f['c1g'], '%s <_ ( 3 / 2 )' % C1: lin8(w, A0, [f['c54']], '%s <_ ( 3 / 2 )' % C1, lv),
                               '0 < U': lin8(w, A0, [tu, t2], '0 < U', lv), '0 < V': lin8(w, A0, [tv, t2], '0 < V', lv)}), w.inst('ef6bk')], 'syl', bkc)
    bkeq, bkcl = conj_split(w, A0, bk)
    srec, srgc, srzc = [c([bkcl, w.inst(k)], 'syl', top_and(top_and(bkc)[1])[i]) for i, k in enumerate(('simp1', 'simp2', 'simp3'))]
    ZSs = S['ef6zs']
    zsa, zsc = ante_of(ZSs)
    zs = c([rebuild(w, c, zsa, {NZ2E: NZ[ETA]}), w.inst('ef6zs')], 'syl', zsc)
    zsb, zscl = conj_split(w, A0, zs)
    sczc, srzc2 = conj_split(w, A0, zscl)
    # 4. horizontal edges
    Ax = '( %s /\\ x e. ( S [,] %s ) )' % (A0, C1)
    cx = Ctx(w, Ax)
    xin = cx([], 'simpr', 'x e. ( S [,] %s )' % C1)
    xr, sx, xc = icc_out(cx, 'x', 'S', C1, xin, lift(w, sr, Ax), lift(w, f['c1r'], Ax))
    lvx = {'x': xr, 'S': lift(w, sr, Ax), C1: lift(w, f['c1r'], Ax)}
    vin = icc_in(cx, 'x', '( 1 / 2 )', '3', xr, numst(w, Ax, '( 1 / 2 )', 'RR'), numst(w, Ax, '3', 'RR'), lin8(w, Ax, [sx, lift(w, s916, Ax)], '( 1 / 2 ) <_ x', lvx), lin8(w, Ax, [xc, lift(w, f['c54'], Ax)], 'x <_ 3', lvx))
    K2 = '( %s x. ( %s ^ 2 ) )' % (KGH, L4)
    n4p = c([c.a1(w.s([], '1rp', '1 e. RR+'), '1 e. RR+'), c([c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [t2], '0 < ( T + 4 )', lv)], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( 1 x. ( T + 4 ) ) e. RR+')
    k2r = c([numst(w, A0, KGH, 'RR'), c([c([n4p], 'relogcld', '%s e. RR' % L4)], 'resqcld', '( %s ^ 2 ) e. RR' % L4)], 'remulcld', '%s e. RR' % K2)
    au = c([c([c([ur], 'recnd', 'U e. CC'), w.inst('absneg')], 'syl', '( abs ` -u U ) = ( abs ` U )'), c([ur, lin8(w, A0, [tu, t2], '0 <_ U', lv)], 'absidd', '( abs ` U ) = U')], 'eqtrd', '( abs ` -u U ) = U')
    thu = c([tu, c([au], 'eqcomd', 'U = ( abs ` -u U )')], 'breqtrd', 'T <_ ( abs ` -u U )')
    thv = c([tv, c([c([vr, lin8(w, A0, [tv, t2], '0 <_ V', lv)], 'absidd', '( abs ` V ) = V')], 'eqcomd', 'V = ( abs ` V )')], 'breqtrd', 'T <_ ( abs ` V )')
    hol = {ETA: hol_eta(w, A0), GF: hol_gf(w, A0)}
    def hedge(F, H, sel, hr, th):
        GA, GB = GOOD(PTL('v', '-u U'), F, L4), GOOD(PTL('v', 'V'), F, L4)
        gx, _ = ral_at(w, Ax, lift(w, hg[F], Ax), 'v', 'x', '( %s /\\ %s )' % (GA, GB), vin)
        gd = cx([gx, w.inst(sel)], 'syl', GOOD(PTL('x', H), F, L4))
        al = c([gd], 'ralrimiva', 'A. x e. ( S [,] %s ) %s' % (C1, GOOD(PTL('x', H), F, L4)))
        HE_ = tsub(stmt('ef4hed'), {'F': F, 'C': C1, 'H': H, 'K': K2})
        hea, hec = ante_of(HE_)
        sp = {HOLF(F, HP0): hol[F], '1 < Y': f['y1'], '0 < S': lin8(w, A0, [s916], '0 < S', lv), 'S <_ %s' % C1: lin8(w, A0, [s58, f['c1g']], 'S <_ %s' % C1, lv), '0 < T': lin8(w, A0, [t2], '0 < T', lv),
              '%s e. RR' % H: hr, 'T <_ ( abs ` %s )' % H: th, '%s e. RR' % K2: k2r, '%s e. RR' % C1: f['c1r'], top_and(hea)[2]: al}
        return c([rebuild(w, c, hea, sp), w.inst('ef4hed')], 'syl', hec)
    hbE = hedge(ETA, '-u U', 'simpl', nur, thu); htE = hedge(ETA, 'V', 'simpr', vr, thv)
    hbG = hedge(GF, '-u U', 'simpl', nur, thu); htG = hedge(GF, 'V', 'simpr', vr, thv)
    # 5. right extras
    def redge(Ua, Va, uar, var_, ule, vul, farf):
        RX = tsub(S['ef6rx'], {'U': Ua, 'V': Va})
        rxa, rxc = ante_of(RX)
        At = '( %s /\\ t e. ( %s [,] %s ) )' % (A0, Ua, Va)
        ct = Ctx(w, At)
        tin = ct([], 'simpr', 't e. ( %s [,] %s )' % (Ua, Va))
        trr, tlo, thi = icc_out(ct, 't', Ua, Va, tin, lift(w, uar, At), lift(w, var_, At))
        far = c([farf(At, ct, trr, tlo, thi)], 'ralrimiva', 'A. t e. ( %s [,] %s ) T <_ ( abs ` t )' % (Ua, Va))
        sp = {'%s e. RR' % Ua: uar, '%s e. RR' % Va: var_, '0 < T': lin8(w, A0, [t2], '0 < T', lv), '%s <_ %s' % (Ua, Va): ule, '( %s - %s ) <_ 1' % (Va, Ua): vul, top_and(rxa)[2]: far}
        return c([rebuild(w, c, rxa, sp), w.inst('ef6rx')], 'syl', rxc)
    def far_neg(At, ct, trr, tlo, thi):
        lvt = {'t': trr, 'T': lift(w, tr, At), 'U': lift(w, ur, At)}
        an = ct([trr, lin8(w, At, [thi, lift(w, t2, At)], 't <_ 0', lvt)], 'absnidd', '( abs ` t ) = -u t')
        return ct([lin8(w, At, [thi], 'T <_ -u t', lvt), ct([an], 'eqcomd', '-u t = ( abs ` t )')], 'breqtrd', 'T <_ ( abs ` t )')
    def far_pos(At, ct, trr, tlo, thi):
        lvt = {'t': trr, 'T': lift(w, tr, At)}
        return ct([tlo, ct([ct([trr, lin8(w, At, [tlo, lift(w, t2, At)], '0 <_ t', lvt)], 'absidd', '( abs ` t ) = t')], 'eqcomd', 't = ( abs ` t )')], 'breqtrd', 'T <_ ( abs ` t )')
    eb = redge('-u U', '-u T', nur, ntr, lin8(w, A0, [tu], '-u U <_ -u T', lv), lin8(w, A0, [u1], '( -u T - -u U ) <_ 1', lv), far_neg)
    et = redge('T', 'V', tr, vr, tv, lin8(w, A0, [v1], '( V - T ) <_ 1', lv), far_pos)
    # 6. left edges
    SGHs = {'-u ( T + 1 ) <_ -u U': lin8(w, A0, [u1], '-u ( T + 1 ) <_ -u U', lv), '-u U <_ 0': lin8(w, A0, [tu, t2], '-u U <_ 0', lv),
            '0 <_ %s' % PM: lin8(w, A0, [vm, tv, t2], '0 <_ %s' % PM, dict(lv, M=c([mn0], 'nn0red', 'M e. RR'))), '-u U e. RR': nur}
    PW = tsub(S['ef6pw'], {'P': '-u U'})
    pwa, pwc = ante_of(PW)
    pw = c([rebuild(w, c, pwa, dict(SGHs)), w.inst('ef6pw')], 'syl', pwc)
    wcG, phG = conj_split(w, A0, pw)
    def ledge(F, ddlab, extra):
        LE = tsub(stmt('ef3left'), {'F': F, 'A': '1', 'P': '-u U', 'Q': 'V'})
        lea, lec = ante_of(LE)
        TL = '( %s ` %s ) =/= 0' % (F, PTL('S', 't'))
        sp = dict(SGHs)
        sp.update({DD(F, '1'): c.a1(w.s([], ddlab, DD(F, '1')), DD(F, '1')), '1 < Y': f['y1'], 'A. t e. ( -u U [,] %s ) %s' % (PM, TL): left_on(F, PM, mt),
                   '-u U < V': lin8(w, A0, [tu, tv, t2], '-u U < V', lv), 'V <_ %s' % PM: vm})
        sp.update(extra)
        return c([rebuild(w, c, lea, sp), w.inst('ef3left')], 'syl', lec)
    leE = ledge(ETA, 'ef2dde', {})
    WCG = top_and(pwc)[0]
    leG = ledge(GF, 'ef2ddg', {WCG: wcG, top_and(pwc)[1]: phG})
    # 7. the triangle inequality on the identity
    IC = top_and(IDC)
    cB, cT = conj_split(w, A0, c([clos, w.inst('simp1')], 'syl', IC[0]))
    cL, cX = conj_split(w, A0, c([clos, w.inst('simp2')], 'syl', IC[1]))
    psc = c([clos, w.inst('simp3')], 'syl', IC[2])
    cc = {}
    for pair in (cB, cT, cL, cX):
        a_, b_ = conj_split(w, A0, pair)
        for st in (a_, b_):
            fm = [l for l in w.lines if l.startswith(st + ':')][0].split(' |- ', 1)[1]
            cc[ante_of(fm)[1][:-len(' e. CC')]] = st
    AB = lambda X: '( abs ` %s )' % X
    ineqs = []
    def split_top(e):
        toks = e.split()
        assert toks[0] == '(' and toks[-1] == ')'
        d = 0
        for i, t in enumerate(toks[1:-1], 1):
            if t == '(':
                d += 1
            elif t == ')':
                d -= 1
            elif d == 0 and t in ('+', '-'):
                return ' '.join(toks[1:i]), t, ' '.join(toks[i + 1:-1])
        raise ValueError(e)
    def tri(e):
        if e in cc:
            return cc[e]
        x, op, y = split_top(e)
        xs, ys = tri(x), tri(y)
        st = c([xs, ys], 'subcld' if op == '-' else 'addcld', '%s e. CC' % e)
        cc[e] = st
        if op == '-':
            ineqs.append(c([xs, ys, w.inst('abs2dif2')], 'syl2anc', '%s <_ ( %s + %s )' % (AB(e), AB(x), AB(y))))
        else:
            ineqs.append(c([xs, ys], 'abstrid', '%s <_ ( %s + %s )' % (AB(e), AB(x), AB(y))))
        return st
    idrc = tri(IDR)
    tp = c([tr, lin8(w, A0, [t2], '0 < T', lv)], 'elrpd', 'T e. RR+')
    clr = Closure(w, A0, {'Y': ('RR+', f['yp']), 'T': ('RR+', tp), 'S': ('RR', sr), '( log ` Y )': ('RR+', f['lp'])})
    HBz, RBz, LBz = tsub(HB, Z1), tsub(RB, Z1), tsub(LB, Z1)
    lva = {AB(k): c([v], 'abscld', '%s e. RR' % AB(k)) for k, v in cc.items()}
    lva.update({HBz: clr.mem(HBz, 'RR'), RBz: clr.mem(RBz, 'RR'), LBz: clr.mem(LBz, 'RR')})
    EDz = tsub(EDGE6, Z1)
    ea = lin8(w, A0, ineqs + [hbE, htE, hbG, htG, eb, et, leE, leG], '%s <_ %s' % (AB(IDR), EDz), lva)
    # 8. the full sum
    D = '( %s - %s )' % (SCz, SRz)
    dc = c([sczc, srzc2], 'subcld', '%s e. CC' % D)
    tpc = c.a1(w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI), '%s e. CC' % TPI)
    e1 = c([tpc, srec, srgc], 'subdid', '( %s x. ( %s - %s ) ) = ( ( %s x. %s ) - ( %s x. %s ) )' % (TPI, SRE, SRG, TPI, SRE, TPI, SRG))
    e2 = c([c([e1], 'eqcomd', '( ( %s x. %s ) - ( %s x. %s ) ) = ( %s x. ( %s - %s ) )' % (TPI, SRE, TPI, SRG, TPI, SRE, SRG)), c([bkeq], 'oveq2d', '( %s x. ( %s - %s ) ) = ( %s x. ( %s - Y ) )' % (TPI, SRE, SRG, TPI, SRz))],
           'eqtrd', '( ( %s x. %s ) - ( %s x. %s ) ) = ( %s x. ( %s - Y ) )' % (TPI, SRE, TPI, SRG, TPI, SRz))
    L0 = '( %s + ( %s x. ( %s - Y ) ) )' % (PSZ1, TPI, SRz)
    e3 = c([c([c([e2], 'oveq2d', '%s = %s' % (IDL, L0))], 'eqcomd', '%s = %s' % (L0, IDL)), c([ident], 'idi', '%s = %s' % (IDL, IDR))], 'eqtrd', '%s = %s' % (L0, IDR))
    LHS = '( ( %s + ( %s x. %s ) ) - ( %s x. Y ) )' % (PSZ1, TPI, SCz, TPI)
    clz = Closure(w, A0, {PSZ1: ('CC', psc), SCz: ('CC', sczc), SRz: ('CC', srzc2), TPI: ('CC', tpc), 'Y': ('CC', c([yr], 'recnd', 'Y e. CC'))})
    for k in (PSZ1, SCz, SRz, TPI, 'Y'):
        clz.atom(k)
    L2 = '( %s + ( %s x. %s ) )' % (L0, TPI, D)
    rq = ringeq(w, A0, LHS, L2, clz)
    L3 = '( %s + ( %s x. %s ) )' % (IDR, TPI, D)
    e4 = c([rq, c([e3], 'oveq1d', '%s = %s' % (L2, L3))], 'eqtrd', '%s = %s' % (LHS, L3))
    tri2 = c([idrc, c([tpc, dc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, D))], 'abstrid', '%s <_ ( %s + %s )' % (AB(L3), AB(IDR), AB('( %s x. %s )' % (TPI, D))))
    PI2 = '( 2 x. _pi )'
    atp = c([c.a1(w.s([], '2cn', '2 e. CC'), '2 e. CC'), c.a1(w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'), '( _i x. _pi ) e. CC')], 'absmuld',
            '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI)
    a2 = c.a1(w.s([w.s([], '0le2', '0 <_ 2'), w.s([w.s([], '2re', '2 e. RR')], 'absidi', '( 0 <_ 2 -> ( abs ` 2 ) = 2 )')], 'ax-mp', '( abs ` 2 ) = 2'), '( abs ` 2 ) = 2')
    aip = c([c([c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )'),
             c([c.a1(w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1'), c.a1(w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], 'pire', '_pi e. RR'), w.s([], 'pipos', '0 < _pi')], 'ltleii', '0 <_ _pi'), w.s([w.s([], 'pire', '_pi e. RR')], 'absidi', '( 0 <_ _pi -> ( abs ` _pi ) = _pi )')], 'ax-mp', '( abs ` _pi ) = _pi'), '( abs ` _pi ) = _pi')],
                'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')
    aip2 = c([aip, c([c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mullidd', '( 1 x. _pi ) = _pi')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = _pi')
    atp2 = c([atp, c([a2, aip2], 'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = %s' % PI2)], 'eqtrd', '( abs ` %s ) = %s' % (TPI, PI2))
    amx = c([c([tpc, dc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TPI, D, TPI, D)), c([atp2], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, D, PI2, D))], 'eqtrd',
            '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, D, PI2, D))
    tri3 = c([c([c([e4], 'fveq2d', '%s = %s' % (AB(LHS), AB(L3))), tri2], 'eqbrtrd', '%s <_ ( %s + %s )' % (AB(LHS), AB(IDR), AB('( %s x. %s )' % (TPI, D)))),
              c([amx], 'oveq2d', '( %s + %s ) = ( %s + ( %s x. %s ) )' % (AB(IDR), AB('( %s x. %s )' % (TPI, D)), AB(IDR), PI2, AB(D)))], 'breqtrd', '%s <_ ( %s + ( %s x. %s ) )' % (AB(LHS), AB(IDR), PI2, AB(D)))
    NM = tsub(S['ef6nm'], dict(Z1, A=AB(IDR), B=AB(D)))
    nma, nmc = ante_of(NM)
    nm = c([rebuild(w, c, nma, {'1 e. NN': c.a1(w.s([], '1nn', '1 e. NN'), '1 e. NN'), '%s e. RR' % AB(IDR): c([idrc], 'abscld', '%s e. RR' % AB(IDR)), '%s e. RR' % AB(D): c([dc], 'abscld', '%s e. RR' % AB(D)),
                               '%s <_ %s' % (AB(IDR), EDz): ea, '%s <_ %s' % (AB(D), tsub(ZB, Z1)): zsb}), w.inst('ef6nm')], 'syl', nmc)
    fin = le_tr(w, A0, tri3, AB(LHS), '( %s + ( %s x. %s ) )' % (AB(IDR), PI2, AB(D)), nm, nmc.split(' <_ ', 1)[1])
    w.qed([fin], 'idi', S['ef6core'])
    return run8(w)


GENS = {'ef6core': gen_core}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
