"""Sortie ZR, REP: cell arithmetic zrc2, zrc1 (Lean delta_lt_im_sub_of_idx_add_two_le, abs_im_sub_lt_of_idx_eq), zrpar."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zrlib import *
import lin
lin.FASTPATH = True
from cl import lift, strip_ante, formula_of
from zr_i import scale_facts


def idx_of(w, A, pre, Z, zc, zi):
    """zridx at Z: returns (nn0, le Qpar, lower, upper) steps"""
    c = Ctx(w, A)
    IA = ante_of(tsub(S['zridx'], {'Z': Z}))
    st = c([c([pre, c([zc, zi], 'jca', top_and(IA[0])[1])], 'jca', IA[0]), w.inst('zridx')], 'syl', IA[1])
    P = top_and(IA[1])
    a, b = top_and(P[0]), top_and(P[1])
    return c([c([st], 'simpld', P[0])], 'simpld', a[0]), c([c([st], 'simpld', P[0])], 'simprd', a[1]), c([c([st], 'simprd', P[1])], 'simpld', b[0]), c([c([st], 'simprd', P[1])], 'simprd', b[1])


def gen_c2(label='zrc2'):
    w = W(label, {'zrc2': 'Lean ` delta_lt_im_sub_of_idx_add_two_le ` : points of the box in cells ` m ` , ` m ' + "'" + ' >_ m + 2 ` have ordinates at least ` 1 / L ` apart.',
                  'zrc1': 'Lean ` abs_im_sub_lt_of_idx_eq ` : two points of the box in the same cell have ordinates less than ` 1 / L ` apart.'}[label])
    A0 = ante_of(S[label])[0]
    c = Ctx(w, A0)
    nn_, tr, t0 = c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T')
    pre = c([nn_, c([tr, t0], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    ac, ai, bc, bi = c.g('A e. CC'), c.g('( abs ` ( Im ` A ) ) <_ T'), c.g('B e. CC'), c.g('( abs ` ( Im ` B ) ) <_ T')
    na, _, la, ua = idx_of(w, A0, pre, 'A', ac, ai)
    nb, _, lb, ub = idx_of(w, A0, pre, 'B', bc, bi)
    IA, IB = IDX('A'), IDX('B')
    iar, ibr = c([na], 'nn0red', '%s e. RR' % IA), c([nb], 'nn0red', '%s e. RR' % IB)
    ima, imb = c([ac], 'imcld', '( Im ` A ) e. RR'), c([bc], 'imcld', '( Im ` B ) e. RR')
    lv = {IA: iar, IB: ibr, '( Im ` A )': ima, '( Im ` B )': imb, 'T': tr, LD: lr}
    lrp = c([lr, lp], 'elrpd', '%s e. RR+' % LD)
    if label == 'zrc2':
        h = c.g('( %s + 2 ) <_ %s' % (IA, IB))
        D = '( ( Im ` B ) - ( Im ` A ) )'
        dr_ = c([imb, ima], 'resubcld', '%s e. RR' % D)
        m = lin8(w, A0, [h, ua, lb], '1 <_ ( %s x. %s )' % (D, LD), lv, products=True)
        fin = c([m, c([c([], '1red', '1 e. RR'), dr_, lrp], 'ledivmul2d', '( ( 1 / %s ) <_ %s <-> 1 <_ ( %s x. %s ) )' % (LD, D, D, LD))], 'mpbird', ante_of(S[label])[1])
    else:
        h = c.g('%s = %s' % (IA, IB))
        D = '( ( Im ` A ) - ( Im ` B ) )'
        dr_ = c([ima, imb], 'resubcld', '%s e. RR' % D)
        m1 = lin8(w, A0, [h, ua, lb], '( %s x. %s ) < 1' % (D, LD), lv, products=True)
        m2 = lin8(w, A0, [h, la, ub], '( -u %s x. %s ) < 1' % (D, LD), lv, products=True)
        u1 = c([m1, c([dr_, c([], '1red', '1 e. RR'), lrp], 'ltmuldivd', '( ( %s x. %s ) < 1 <-> %s < ( 1 / %s ) )' % (D, LD, D, LD))], 'mpbid', '%s < ( 1 / %s )' % (D, LD))
        u2 = c([m2, c([c([dr_], 'renegcld', '-u %s e. RR' % D), c([], '1red', '1 e. RR'), lrp], 'ltmuldivd', '( ( -u %s x. %s ) < 1 <-> -u %s < ( 1 / %s ) )' % (D, LD, D, LD))], 'mpbid',
                '-u %s < ( 1 / %s )' % (D, LD))
        ilr = c([c([], '1red', '1 e. RR'), lr, c([lp], 'gt0ne0d', '%s =/= 0' % LD)], 'redivcld', '( 1 / %s ) e. RR' % LD)
        fin = c([c([lin8(w, A0, [u2], '-u ( 1 / %s ) < %s' % (LD, D), {D: dr_, '( 1 / %s )' % LD: ilr}), u1], 'jca', '( -u ( 1 / %s ) < %s /\\ %s < ( 1 / %s ) )' % (LD, D, D, LD)),
                 c([dr_, ilr], 'absltd', '( ( abs ` %s ) < ( 1 / %s ) <-> ( -u ( 1 / %s ) < %s /\\ %s < ( 1 / %s ) ) )' % (D, LD, LD, D, D, LD))], 'mpbird', ante_of(S[label])[1])
    w.qed([fin], 'idi', S[label])
    return run8(w)


GENS = {'zrc2': gen_c2, 'zrc1': lambda: gen_c2('zrc1')}


def gen_par():
    w = W('zrpar', 'An even integer ` E ` with ` M - 1 < E < M + 2 ` is ` M + ( M mod 2 ) ` (the integer step of Lean ` rep_band_card_le ` ).')
    A0 = ante_of(S['zrpar'])[0]
    c = Ctx(w, A0)
    mn, ez, e0, h1, h2 = c.g('M e. NN0'), c.g('E e. ZZ'), c.g('( E mod 2 ) = 0'), c.g('( M - 1 ) < E'), c.g('E < ( M + 2 )')
    mr = c([mn], 'nn0red', 'M e. RR'); er = c([ez], 'zred', 'E e. RR')
    two = c.a1(w.s([], '2rp', '2 e. RR+'), '2 e. RR+')
    R = '( M mod 2 )'
    rz = c([c([mn], 'nn0zd', 'M e. ZZ'), c.a1(w.s([], '2nn', '2 e. NN'), '2 e. NN'), w.inst('zmodcl')], 'syl2anc', '%s e. NN0' % R)
    rr = c([rz], 'nn0red', '%s e. RR' % R)
    r0 = c([mr, two, w.inst('modge0')], 'syl2anc', '0 <_ %s' % R)
    r2 = c([mr, two, w.inst('modlt')], 'syl2anc', '%s < 2' % R)
    F = '( |_ ` ( M / 2 ) )'; K = '( |_ ` ( E / 2 ) )'
    fz = c([c([mr, numst8(w, A0, '2', 'RR'), c.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0')], 'redivcld', '( M / 2 ) e. RR')], 'flcld', '%s e. ZZ' % F)
    kz = c([c([er, numst8(w, A0, '2', 'RR'), c.a1(w.s([], '2ne0', '2 =/= 0'), '2 =/= 0')], 'redivcld', '( E / 2 ) e. RR')], 'flcld', '%s e. ZZ' % K)
    fm = c([mr, two, w.inst('flpmodeq')], 'syl2anc', '( ( %s x. 2 ) + %s ) = M' % (F, R))
    fe = c([er, two, w.inst('flpmodeq')], 'syl2anc', '( ( %s x. 2 ) + ( E mod 2 ) ) = E' % K)
    J = '( ( %s - %s ) - %s )' % (K, F, R)
    jz = c([c([kz, fz], 'zsubcld', '( %s - %s ) e. ZZ' % (K, F)), c([rz], 'nn0zd', '%s e. ZZ' % R)], 'zsubcld', '%s e. ZZ' % J)
    jr = c([jz], 'zred', '%s e. RR' % J)
    lv = {'M': mr, 'E': er, R: rr, F: c([fz], 'zred', '%s e. RR' % F), K: c([kz], 'zred', '%s e. RR' % K)}
    # r <_ 1 (integer below 2)
    r1a = c([r2, c([c([rz], 'nn0zd', '%s e. ZZ' % R), c.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s < 2 <-> ( %s + 1 ) <_ 2 )' % (R, R))], 'mpbid', '( %s + 1 ) <_ 2' % R)
    jl = lin8(w, A0, [fm, fe, e0, h1, r1a], '-u 1 < %s' % J, lv)
    jh = lin8(w, A0, [fm, fe, e0, h2, r0], '%s < 1' % J, lv)
    ja = c([jl, c([c([c.a1(w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')], 'znegcld', '-u 1 e. ZZ'), jz, w.inst('zltp1le')], 'syl2anc', '( -u 1 < %s <-> ( -u 1 + 1 ) <_ %s )' % (J, J))], 'mpbid', '( -u 1 + 1 ) <_ %s' % J)
    jb = c([jh, c([jz, c.a1(w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), w.inst('zltp1le')], 'syl2anc', '( %s < 1 <-> ( %s + 1 ) <_ 1 )' % (J, J))], 'mpbid', '( %s + 1 ) <_ 1' % J)
    le1 = lin8(w, A0, [fm, fe, e0, jb], 'E <_ ( M + %s )' % R, lv)
    le2 = lin8(w, A0, [fm, fe, e0, ja], '( M + %s ) <_ E' % R, lv)
    mrr = c([mr, rr], 'readdcld', '( M + %s ) e. RR' % R)
    eq = c([c([le1, le2], 'jca', '( E <_ ( M + %s ) /\\ ( M + %s ) <_ E )' % (R, R)), c([er, mrr], 'letri3d', '( E = ( M + %s ) <-> ( E <_ ( M + %s ) /\\ ( M + %s ) <_ E ) )' % (R, R, R))], 'mpbird', 'E = ( M + %s )' % R)
    w.qed([eq], 'idi', S['zrpar'])
    return run8(w)


GENS['zrpar'] = gen_par


XPY = '( Y X. ( 0 ... %s ) )' % QP
RIB = lambda P, p='p': '( %s =/= (/) /\\ ( ( 2nd ` %s ) mod 2 ) = %s )' % (CELL('( 1st ` %s )' % p, '( 2nd ` %s )' % p), p, P)


def ri_facts(w, A, qst, Q, P='P'):
    """from ( A -> Q e. RI(P) ): Q e. XPY, cell nonempty, parity, 2nd Q e. ZZ, 1st Q e. Y"""
    from ef4_g import elrab_unpack
    c = Ctx(w, A)
    qxp, qb, new = elrab_unpack(w, A, 'p', XPY, RIB(P), Q, qst)
    cne = c([qb], 'simpld', top_and(new)[0])
    par = c([qb], 'simprd', top_and(new)[1])
    q2 = c([qxp, w.inst('xp2nd')], 'syl', '( 2nd ` %s ) e. ( 0 ... %s )' % (Q, QP))
    q2z = c([q2, w.inst('elfzelz')], 'syl', '( 2nd ` %s ) e. ZZ' % Q)
    q1 = c([qxp, w.inst('xp1st')], 'syl', '( 1st ` %s ) e. Y' % Q)
    return qxp, cne, par, q2z, q1, q2


def cell_facts(w, A, ast, Z, x, m, sr, tr):
    """from ( A -> Z e. CELL(x, m) ): Z e. CC, abs Im Z <_ T, IDX(Z) = m, Z e. G, Z e. ZFX(x), Re bounds"""
    from ef4_g import elrab_unpack
    from zr_j import box_facts
    c = Ctx(w, A)
    zz, zb, _ = elrab_unpack(w, A, 'v', ZFX(x), '( v e. G /\\ %s = %s )' % (IDX('v'), m), Z, ast)
    zg = c([zb], 'simpld', '%s e. G' % Z); zi = c([zb], 'simprd', '%s = %s' % (IDX(Z), m))
    zbx, zp, _ = elrab_unpack(w, A, 'r', BOXR, '( r =/= 1 /\\ ( %s ` r ) = 0 )' % EX(x), Z, zz)
    vc, rvr, ivr, f1, f2, f3, f4 = box_facts(w, A, sr, tr, zbx, Z)
    IM = '( Im ` %s )' % Z
    ab = c([c([f3, f4], 'jca', '( -u T <_ %s /\\ %s <_ T )' % (IM, IM)), c([ivr, tr], 'absled', '( ( abs ` %s ) <_ T <-> ( -u T <_ %s /\\ %s <_ T ) )' % (IM, IM, IM))], 'mpbird', '( abs ` %s ) <_ T' % IM)
    return dict(cc=vc, im=ab, idx=zi, g=zg, zf=zz, box=zbx, zp=zp, re1=f1, re2=f2, rer=rvr, imr=ivr)


def gen_sp():
    w = W('zrsp', 'Lean ` rep_spacing ` (blueprint 7.2(b)): zeros ` A ` , ` B ` from the cells of two distinct indices of one parity system with the same character have ordinates at least ` 1 / L ` apart ( ~ zrc2 ).')
    A0 = ante_of(S['zrsp'])[0]
    c = Ctx(w, A0)
    nn_, tr, t0 = c.g('N e. NN'), c.g('T e. RR'), c.g('0 <_ T')
    sr = c.g('S e. RR')
    qin, rin = c.g('Q e. %s' % RI('P')), c.g('R e. %s' % RI('P'))
    e1, qr = c.g('( 1st ` Q ) = ( 1st ` R )'), c.g('Q =/= R')
    ain, bin_ = c.g('A e. %s' % CELL('( 1st ` Q )', '( 2nd ` Q )')), c.g('B e. %s' % CELL('( 1st ` R )', '( 2nd ` R )'))
    qxp, _, qpar, q2z, _, _ = ri_facts(w, A0, qin, 'Q')
    rxp, _, rpar, r2z, _, _ = ri_facts(w, A0, rin, 'R')
    fa = cell_facts(w, A0, ain, 'A', '( 1st ` Q )', '( 2nd ` Q )', sr, tr)
    fb = cell_facts(w, A0, bin_, 'B', '( 1st ` R )', '( 2nd ` R )', sr, tr)
    MQ, MR = '( 2nd ` Q )', '( 2nd ` R )'
    # 2nd Q =/= 2nd R
    xo = c([qxp, rxp, w.inst('xpopth')], 'syl2anc', '( ( ( 1st ` Q ) = ( 1st ` R ) /\\ %s = %s ) <-> Q = R )' % (MQ, MR))
    A1 = '( %s /\\ %s = %s )' % (A0, MQ, MR)
    qe = w.s([w.s([lift(w, e1, A1), w.s([], 'simpr', '( %s -> %s = %s )' % (A1, MQ, MR))], 'jca', '( %s -> ( ( 1st ` Q ) = ( 1st ` R ) /\\ %s = %s ) )' % (A1, MQ, MR)), lift(w, xo, A1)],
             'mpbid', '( %s -> Q = R )' % A1)
    mne = c([qr, c([w.s([qe], 'ex', '( %s -> ( %s = %s -> Q = R ) )' % (A0, MQ, MR))], 'necon3d', '( Q =/= R -> %s =/= %s )' % (MQ, MR))], 'mpd', '%s =/= %s' % (MQ, MR))
    q2r, r2r = c([q2z], 'zred', '%s e. RR' % MQ), c([r2z], 'zred', '%s e. RR' % MR)
    tri = c([mne, c([q2r, r2r, w.inst('lttri2')], 'syl2anc', '( %s =/= %s <-> ( %s < %s \\/ %s < %s ) )' % (MQ, MR, MQ, MR, MR, MQ))], 'mpbid', '( %s < %s \\/ %s < %s )' % (MQ, MR, MR, MQ))
    pe = c([qpar, c([rpar], 'eqcomd', 'P = ( %s mod 2 )' % MR)], 'eqtrd', '( %s mod 2 ) = ( %s mod 2 )' % (MQ, MR))
    pre = c([nn_, c([tr, t0], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    GOAL = ante_of(S['zrsp'])[1]
    D = '( abs ` ( ( Im ` A ) - ( Im ` B ) ) )'
    def side(lo, hi, flo, fhi, loz, hiz, lopar_eq_hipar, lox, hix):
        # lo < hi  ->  1 / LD <_ Im hi - Im lo
        Al = '( %s /\\ ( 2nd ` %s ) < ( 2nd ` %s ) )' % (A0, lo, hi)
        cl = Ctx(w, Al)
        Lx = lambda st: lift(w, st, Al)
        lt = cl([], 'simpr', '( 2nd ` %s ) < ( 2nd ` %s )' % (lo, hi))
        nn2 = cl([lt, cl([Lx(loz), Lx(hiz), w.inst('znnsub')], 'syl2anc', '( ( 2nd ` %s ) < ( 2nd ` %s ) <-> ( ( 2nd ` %s ) - ( 2nd ` %s ) ) e. NN )' % (lo, hi, hi, lo))],
                 'mpbid', '( ( 2nd ` %s ) - ( 2nd ` %s ) ) e. NN' % (hi, lo))
        dv = cl([Lx(lopar_eq_hipar), cl([cl.a1(w.s([], '2nn', '2 e. NN'), '2 e. NN'), Lx(hiz), Lx(loz), w.inst('moddvds')], 'syl3anc',
                                          '( ( ( 2nd ` %s ) mod 2 ) = ( ( 2nd ` %s ) mod 2 ) <-> 2 || ( ( 2nd ` %s ) - ( 2nd ` %s ) ) )' % (hi, lo, hi, lo))], 'mpbid', '2 || ( ( 2nd ` %s ) - ( 2nd ` %s ) )' % (hi, lo))
        le2 = cl([dv, cl([cl.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ'), nn2, w.inst('dvdsle')], 'syl2anc', '( 2 || ( ( 2nd ` %s ) - ( 2nd ` %s ) ) -> 2 <_ ( ( 2nd ` %s ) - ( 2nd ` %s ) ) )' % (hi, lo, hi, lo))],
                 'mpd', '2 <_ ( ( 2nd ` %s ) - ( 2nd ` %s ) )' % (hi, lo))
        il, ih = IDX(lox), IDX(hix)
        lvi = {il: cl([cl([Lx(flo['idx']), Lx(loz)], 'eqeltrd', '%s e. ZZ' % il)], 'zred', '%s e. RR' % il), ih: cl([cl([Lx(fhi['idx']), Lx(hiz)], 'eqeltrd', '%s e. ZZ' % ih)], 'zred', '%s e. RR' % ih),
               '( 2nd ` %s )' % lo: Lx(c([loz], 'zred', '( 2nd ` %s ) e. RR' % lo)), '( 2nd ` %s )' % hi: Lx(c([hiz], 'zred', '( 2nd ` %s ) e. RR' % hi))}
        i2 = lin8(w, Al, [le2, Lx(flo['idx']), Lx(fhi['idx'])], '( %s + 2 ) <_ %s' % (il, ih), lvi)
        CA = ante_of(tsub(S['zrc2'], {'A': lox, 'B': hix}))
        z2 = cl([cl([cl([Lx(pre), cl([Lx(flo['cc']), Lx(flo['im'])], 'jca', PTB(lox)), cl([Lx(fhi['cc']), Lx(fhi['im'])], 'jca', PTB(hix))], '3jca', top_and(CA[0])[0]), i2], 'jca', CA[0]),
                 w.inst('zrc2')], 'syl', CA[1])
        return Al, cl, z2
    # Q below R: 1 / LD <_ Im B - Im A
    Al1, cl1, z1 = side('Q', 'R', fa, fb, q2z, r2z, c([pe], 'eqcomd', '( %s mod 2 ) = ( %s mod 2 )' % (MR, MQ)), 'A', 'B')
    DBA = '( ( Im ` B ) - ( Im ` A ) )'
    ima, imb = fa['imr'], fb['imr']
    ab1 = cl1([cl1([lift(w, c([imb, ima], 'resubcld', '%s e. RR' % DBA), Al1)], 'leabsd', '%s <_ ( abs ` %s )' % (DBA, DBA)),
               cl1([lift(w, c([imb], 'recnd', '( Im ` B ) e. CC'), Al1), lift(w, c([ima], 'recnd', '( Im ` A ) e. CC'), Al1)], 'abssubd', '( abs ` %s ) = %s' % (DBA, D))], 'breqtrd', '%s <_ %s' % (DBA, D))
    from zr_i import scale_facts as _sf
    def lvg(Al):
        d2_, lr_, lp_, dr_ = _sf(w, Al, lift(w, nn_, Al), lift(w, tr, Al), lift(w, t0, Al))
        ilr = w.s([w.s([], '1red', '( %s -> 1 e. RR )' % Al), lr_, w.s([lp_], 'gt0ne0d', '( %s -> %s =/= 0 )' % (Al, LD))], 'redivcld', '( %s -> ( 1 / %s ) e. RR )' % (Al, LD))
        return {'( 1 / %s )' % LD: ilr, DBA: lift(w, c([imb, ima], 'resubcld', '%s e. RR' % DBA), Al), DAB: lift(w, c([ima, imb], 'resubcld', '%s e. RR' % DAB), Al),
                D: lift(w, c([c([c([ima], 'recnd', '( Im ` A ) e. CC'), c([imb], 'recnd', '( Im ` B ) e. CC')], 'subcld', '%s e. CC' % DAB)], 'abscld', '%s e. RR' % D), Al)}
    DAB = '( ( Im ` A ) - ( Im ` B ) )'
    g1 = lin8(w, Al1, [z1, ab1], GOAL, lvg(Al1))
    Al2, cl2, z2 = side('R', 'Q', fb, fa, r2z, q2z, pe, 'B', 'A')
    ab2 = cl2([lift(w, c([ima, imb], 'resubcld', '%s e. RR' % DAB), Al2)], 'leabsd', '%s <_ %s' % (DAB, D))
    g2 = lin8(w, Al2, [z2, ab2], GOAL, lvg(Al2))
    fin = c([tri, c([w.s([g1], 'ex', '( %s -> ( %s < %s -> %s ) )' % (A0, MQ, MR, GOAL)), w.s([g2], 'ex', '( %s -> ( %s < %s -> %s ) )' % (A0, MR, MQ, GOAL))], 'jaod',
                    '( ( %s < %s \\/ %s < %s ) -> %s )' % (MQ, MR, MR, MQ, GOAL))], 'mpd', GOAL)
    w.qed([fin], 'idi', S['zrsp'])
    return run8(w)


GENS['zrsp'] = gen_sp


def gen_band():
    w = W('zrband', 'Lean ` rep_band_card_le ` (blueprint 7.2(b), the hypothesis of Lemma 6.4): for a selector ` H ` of the cells of a parity system, an index ` Q ` and ` M e. NN0 ` , '
             'at most two indices ` q ` with the character of ` Q ` have ` M / L <_ abs ( Im H ( q ) - Im H ( Q ) ) < ( M + 1 ) / L ` ( ~ zrpar ).')
    A0 = ante_of(S['zrband'])[0]
    c = Ctx(w, A0)
    nn_, sr, tr, t0 = c.g('N e. NN'), c.g('S e. RR'), c.g('T e. RR'), c.g('0 <_ T')
    qin = c.g('Q e. %s' % RI('P'))
    ALH = 'A. q e. %s ( H ` q ) e. %s' % (RI('P'), CELL('( 1st ` q )', '( 2nd ` q )'))
    alh = c.g(ALH); mn = c.g('M e. NN0')
    d2, lr, lp, dr = scale_facts(w, A0, nn_, tr, t0)
    IL = '( 1 / %s )' % LD
    l0 = c([lp], 'gt0ne0d', '%s =/= 0' % LD)
    ilr = c([c([], '1red', '1 e. RR'), lr, l0], 'redivcld', '%s e. RR' % IL)
    ill = c([c([], '1cnd', '1 e. CC'), c([lr], 'recnd', '%s e. CC' % LD), l0], 'divcan1d', '( %s x. %s ) = 1' % (IL, LD))
    mr = c([mn], 'nn0red', 'M e. RR')
    mill = c([c([ill], 'oveq2d', '( M x. ( %s x. %s ) ) = ( M x. 1 )' % (IL, LD)), c([c([mr], 'recnd', 'M e. CC')], 'mulridd', '( M x. 1 ) = M')], 'eqtrd', '( M x. ( %s x. %s ) ) = M' % (IL, LD))
    m1ill = c([c([ill], 'oveq2d', '( ( M + 1 ) x. ( %s x. %s ) ) = ( ( M + 1 ) x. 1 )' % (IL, LD)), c([c([c([mr, c([], '1red', '1 e. RR')], 'readdcld', '( M + 1 ) e. RR')], 'recnd', '( M + 1 ) e. CC')], 'mulridd', '( ( M + 1 ) x. 1 ) = ( M + 1 )')],
              'eqtrd', '( ( M + 1 ) x. ( %s x. %s ) ) = ( M + 1 )' % (IL, LD))
    qxp, _, qpar, q2z, q1, _ = ri_facts(w, A0, qin, 'Q')
    hqc, _ = ral_at(w, A0, alh, 'q', 'Q', '( H ` q ) e. %s' % CELL('( 1st ` q )', '( 2nd ` q )'), qin)
    fQ = cell_facts(w, A0, hqc, '( H ` Q )', '( 1st ` Q )', '( 2nd ` Q )', sr, tr)
    pre = c([nn_, c([tr, t0], 'jca', TT)], 'jca', '( N e. NN /\\ %s )' % TT)
    _, _, lQ, uQ = idx_of(w, A0, pre, '( H ` Q )', fQ['cc'], fQ['im'])
    C_ = '( M + ( M mod 2 ) )'
    PL = '<. ( 1st ` Q ) , ( ( 2nd ` Q ) + %s ) >.' % C_
    MI = '<. ( 1st ` Q ) , ( ( 2nd ` Q ) - %s ) >.' % C_
    BAND = BANDQ('M')
    BODYq = BAND[len('{ q e. %s | ' % RI('P')):-2]
    BODY = tsub(BODYq, {'q': 'j'})
    BANDJ = tsub(BAND, {'q': 'j'})
    Aq = '( %s /\\ j e. %s )' % (A0, BANDJ)
    cq = Ctx(w, Aq)
    Lq = lambda st: lift(w, st, Aq)
    qb = cq([cq([], 'simpr', 'j e. %s' % BANDJ), w.s([], 'rabid', '( j e. %s <-> ( j e. %s /\\ %s ) )' % (BANDJ, RI('P'), BODY))], 'sylib', '( j e. %s /\\ %s )' % (RI('P'), BODY))
    qri = cq([qb], 'simpld', 'j e. %s' % RI('P'))
    bb = cq([qb], 'simprd', BODY)
    B3 = top_and(BODY)
    e1 = cq([bb], 'simpld', B3[0])
    B4 = top_and(B3[1])
    blo = cq([cq([bb], 'simprd', B3[1])], 'simpld', B4[0]); bhi = cq([cq([bb], 'simprd', B3[1])], 'simprd', B4[1])
    qxq, _, qparq, q2zq, _, _ = ri_facts(w, Aq, qri, 'j')
    hqq, _ = ral_at(w, Aq, Lq(alh), 'q', 'j', '( H ` q ) e. %s' % CELL('( 1st ` q )', '( 2nd ` q )'), qri)
    fq = cell_facts(w, Aq, hqq, '( H ` j )', '( 1st ` j )', '( 2nd ` j )', Lq(sr), Lq(tr))
    _, _, lq, uq = idx_of(w, Aq, Lq(pre), '( H ` j )', fq['cc'], fq['im'])
    DL_ = '( ( Im ` ( H ` j ) ) - ( Im ` ( H ` Q ) ) )'
    dlr = cq([fq['imr'], Lq(fQ['imr'])], 'resubcld', '%s e. RR' % DL_)
    AD = '( abs ` %s )' % DL_
    adr = cq([cq([dlr], 'recnd', '%s e. CC' % DL_)], 'abscld', '%s e. RR' % AD)
    E_ = '( ( 2nd ` j ) - ( 2nd ` Q ) )'; EN = '( ( 2nd ` Q ) - ( 2nd ` j ) )'
    ez = cq([q2zq, Lq(q2z)], 'zsubcld', '%s e. ZZ' % E_); enz = cq([Lq(q2z), q2zq], 'zsubcld', '%s e. ZZ' % EN)
    # parities
    pe = cq([qparq, cq([Lq(qpar)], 'eqcomd', 'P = ( ( 2nd ` Q ) mod 2 )')], 'eqtrd', '( ( 2nd ` j ) mod 2 ) = ( ( 2nd ` Q ) mod 2 )')
    def even(a, b, dz, D_):
        pp = pe if a == 'j' else cq([pe], 'eqcomd', '( ( 2nd ` %s ) mod 2 ) = ( ( 2nd ` %s ) mod 2 )' % (a, b))
        dv = cq([pp, cq([cq.a1(w.s([], '2nn', '2 e. NN'), '2 e. NN'), q2zq if a == 'j' else Lq(q2z), Lq(q2z) if a == 'j' else q2zq, w.inst('moddvds')], 'syl3anc',
                         '( ( ( 2nd ` %s ) mod 2 ) = ( ( 2nd ` %s ) mod 2 ) <-> 2 || %s )' % (a, b, D_))], 'mpbid', '2 || %s' % D_)
        return cq([dv, cq([cq.a1(w.s([], '2nn', '2 e. NN'), '2 e. NN'), dz, w.inst('dvdsval3')], 'syl2anc', '( 2 || %s <-> ( %s mod 2 ) = 0 )' % (D_, D_))], 'mpbid', '( %s mod 2 ) = 0' % D_)
    ev1 = even('j', 'Q', ez, E_)
    ev2 = even('Q', 'j', enz, EN)
    IQq, IQQ = IDX('( H ` j )'), IDX('( H ` Q )')
    lv = {AD: adr, '( Im ` ( H ` j ) )': fq['imr'], '( Im ` ( H ` Q ) )': Lq(fQ['imr']), 'T': Lq(tr), LD: Lq(lr), IL: Lq(ilr), 'M': Lq(mr),
          '( 2nd ` j )': cq([q2zq], 'zred', '( 2nd ` j ) e. RR'), '( 2nd ` Q )': Lq(c([q2z], 'zred', '( 2nd ` Q ) e. RR')),
          IQq: cq([cq([fq['idx'], q2zq], 'eqeltrd', '%s e. ZZ' % IQq)], 'zred', '%s e. RR' % IQq), IQQ: Lq(c([c([fQ['idx'], q2z], 'eqeltrd', '%s e. ZZ' % IQQ)], 'zred', '%s e. RR' % IQQ))}
    h1 = cq([Lq(lr), cq([adr, cq([Lq(mr), Lq(ilr)], 'remulcld', '( M x. %s ) e. RR' % IL)], 'resubcld', '( %s - ( M x. %s ) ) e. RR' % (AD, IL)), Lq(c([lp], 'ltled', '0 <_ %s' % LD)),
             lin8(w, Aq, [blo], '0 <_ ( %s - ( M x. %s ) )' % (AD, IL), lv, products=True)], 'mulge0d', '0 <_ ( %s x. ( %s - ( M x. %s ) ) )' % (LD, AD, IL))
    h2 = cq([Lq(lp), lin8(w, Aq, [bhi], '0 < ( ( ( M + 1 ) x. %s ) - %s )' % (IL, AD), lv, products=True)], 'mulgt0d', '0 < ( %s x. ( ( ( M + 1 ) x. %s ) - %s ) )' % (LD, IL, AD))
    facts = [h1, h2, Lq(mill), Lq(m1ill), lq, uq, Lq(lQ), Lq(uQ), fq['idx'], Lq(fQ['idx'])]
    GOALq = 'j e. { %s , %s }' % (PL, MI)
    res = []
    for sign in ('+', '-'):
        if sign == '+':
            Ac = '( %s /\\ 0 <_ %s )' % (Aq, DL_)
            ccx = Ctx(w, Ac)
            ab_ = ccx([lift(w, dlr, Ac), ccx([], 'simpr', '0 <_ %s' % DL_)], 'absidd', '%s = %s' % (AD, DL_))
            Ez, evx = lift(w, ez, Ac), lift(w, ev1, Ac)
            EE = E_
        else:
            Ac = '( %s /\\ -. 0 <_ %s )' % (Aq, DL_)
            ccx = Ctx(w, Ac)
            ng = ccx([ccx([], 'simpr', '-. 0 <_ %s' % DL_), ccx([lift(w, dlr, Ac), ccx([], '0red', '0 e. RR')], 'ltnled', '( %s < 0 <-> -. 0 <_ %s )' % (DL_, DL_))], 'mpbird', '%s < 0' % DL_)
            ab_ = ccx([lift(w, dlr, Ac), ccx([ng], 'ltled', '%s <_ 0' % DL_)], 'absnidd', '%s = -u %s' % (AD, DL_))
            Ez, evx = lift(w, enz, Ac), lift(w, ev2, Ac)
            EE = EN
        La = lambda st: lift(w, st, Ac)
        lva = {k_: La(v_) for k_, v_ in lv.items()}
        SD = DL_ if sign == '+' else '-u %s' % DL_
        sdr = La(dlr) if sign == '+' else ccx([La(dlr)], 'renegcld', '%s e. RR' % SD)
        lva2 = dict(lva); lva2[SD] = sdr
        bl = lin8(w, Ac, [La(blo), ab_], '( M x. %s ) <_ %s' % (IL, SD), lva2, products=True)
        bh = lin8(w, Ac, [La(bhi), ab_], '%s < ( ( M + 1 ) x. %s )' % (SD, IL), lva2, products=True)
        h1c = ccx([La(lr), ccx([sdr, ccx([La(mr), La(ilr)], 'remulcld', '( M x. %s ) e. RR' % IL)], 'resubcld', '( %s - ( M x. %s ) ) e. RR' % (SD, IL)), La(c([lp], 'ltled', '0 <_ %s' % LD)),
                   lin8(w, Ac, [bl], '0 <_ ( %s - ( M x. %s ) )' % (SD, IL), lva2, products=True)], 'mulge0d', '0 <_ ( %s x. ( %s - ( M x. %s ) ) )' % (LD, SD, IL))
        h2c = ccx([La(lp), lin8(w, Ac, [bh], '0 < ( ( ( M + 1 ) x. %s ) - %s )' % (IL, SD), lva2, products=True)], 'mulgt0d', '0 < ( %s x. ( ( ( M + 1 ) x. %s ) - %s ) )' % (LD, IL, SD))
        f_ = [La(x) for x in facts[2:]] + [h1c, h2c]
        lo = lin8(w, Ac, f_, '( M - 1 ) < %s' % EE, lva, products=True)
        hi = lin8(w, Ac, f_, '%s < ( M + 2 )' % EE, lva, products=True)
        PA = ante_of(tsub(S['zrpar'], {'E': EE}))
        pr = ccx([ccx([ccx([La(mn), Ez], 'jca', top_and(PA[0])[0]), ccx([evx, ccx([lo, hi], 'jca', top_and(top_and(PA[0])[1])[1])], 'jca', top_and(PA[0])[1])], 'jca', PA[0]), w.inst('zrpar')], 'syl', PA[1])
        q2c = ccx([La(q2zq)], 'zcnd', '( 2nd ` j ) e. CC'); Q2c = La(c([q2z], 'zcnd', '( 2nd ` Q ) e. CC'))
        cc_ = ccx([La(c([mn], 'nn0cnd', 'M e. CC')), ccx([ccx([La(c([mn], 'nn0zd', 'M e. ZZ')), ccx.a1(w.s([], '2nn', '2 e. NN'), '2 e. NN'), w.inst('zmodcl')], 'syl2anc', '( M mod 2 ) e. NN0')], 'nn0cnd', '( M mod 2 ) e. CC')],
                  'addcld', '%s e. CC' % C_)
        if sign == '+':
            s2 = ccx([pr, ccx([q2c, Q2c, cc_, w.inst('subadd')], 'syl3anc', '( %s = %s <-> ( ( 2nd ` Q ) + %s ) = ( 2nd ` j ) )' % (E_, C_, C_))], 'mpbid', '( ( 2nd ` Q ) + %s ) = ( 2nd ` j )' % C_)
            tgt = PL
            sec = '( ( 2nd ` Q ) + %s )' % C_
        else:
            s2 = ccx([pr, ccx([Q2c, q2c, cc_, w.inst('subadd')], 'syl3anc', '( %s = %s <-> ( ( 2nd ` j ) + %s ) = ( 2nd ` Q ) )' % (EN, C_, C_))], 'mpbid', '( ( 2nd ` j ) + %s ) = ( 2nd ` Q )' % C_)
            s2 = ccx([s2, ccx([Q2c, cc_, q2c, w.inst('subadd2')], 'syl3anc', '( ( ( 2nd ` Q ) - %s ) = ( 2nd ` j ) <-> ( ( 2nd ` j ) + %s ) = ( 2nd ` Q ) )' % (C_, C_))], 'mpbird', '( ( 2nd ` Q ) - %s ) = ( 2nd ` j )' % C_)
            tgt = MI
            sec = '( ( 2nd ` Q ) - %s )' % C_
        o1 = ccx([La(qxq), w.inst('1st2nd2')], 'syl', 'j = <. ( 1st ` j ) , ( 2nd ` j ) >.')
        o2 = ccx([La(e1), ccx([s2], 'eqcomd', '( 2nd ` j ) = %s' % sec)], 'opeq12d', '<. ( 1st ` j ) , ( 2nd ` j ) >. = %s' % tgt)
        qe = ccx([o1, o2], 'eqtrd', 'j = %s' % tgt)
        el = ccx([(ccx([qe], 'orcd', '( j = %s \\/ j = %s )' % (PL, MI)) if sign == '+' else ccx([qe], 'olcd', '( j = %s \\/ j = %s )' % (PL, MI))),
                  ccx([La(qri), w.inst('elprg')], 'syl', '( j e. { %s , %s } <-> ( j = %s \\/ j = %s ) )' % (PL, MI, PL, MI))], 'mpbird', GOALq)
        res.append(el)
    gq = cq([res[0], res[1]], 'pm2.61dan', GOALq)
    Ar = '( ( %s /\\ j e. %s ) /\\ %s )' % (A0, RI('P'), BODY)
    cr_ = Ctx(w, Ar)
    qband = cr_([cr_([cr_.g('j e. %s' % RI('P')), cr_.g(BODY)], 'jca', '( j e. %s /\\ %s )' % (RI('P'), BODY)), w.s([], 'rabid', '( j e. %s <-> ( j e. %s /\\ %s ) )' % (BANDJ, RI('P'), BODY))], 'sylibr', 'j e. %s' % BANDJ)
    toq = cr_([cr_.g(A0), qband], 'jca', Aq)
    gr = cr_([toq, gq], 'syl', GOALq)
    al = c([w.s([gr], 'ex', '( ( %s /\\ j e. %s ) -> ( %s -> %s ) )' % (A0, RI('P'), BODY, GOALq))], 'ralrimiva', 'A. j e. %s ( %s -> %s )' % (RI('P'), BODY, GOALq))
    ssj = c([al, w.s([], 'rabss', '( %s C_ { %s , %s } <-> A. j e. %s ( %s -> %s ) )' % (BANDJ, PL, MI, RI('P'), BODY, GOALq))], 'sylibr', '%s C_ { %s , %s }' % (BANDJ, PL, MI))
    eqb, newb = w.wcongr(BODYq, {'q': 'j'}, 'q = j', {'q': w.s([], 'id', '( q = j -> q = j )')})
    assert newb == BODY, (newb, BODY)
    cbv = c.a1(w.s([eqb], 'cbvrabv', '%s = %s' % (BAND, BANDJ)), '%s = %s' % (BAND, BANDJ))
    ss = c([cbv, ssj], 'eqsstrd', '%s C_ { %s , %s }' % (BAND, PL, MI))
    hs = c([c.a1(w.s([], 'prfi', '{ %s , %s } e. Fin' % (PL, MI)), '{ %s , %s } e. Fin' % (PL, MI)), ss, w.inst('hashss')], 'syl2anc', '( # ` %s ) <_ ( # ` { %s , %s } )' % (BAND, PL, MI))
    h2_ = c.a1(w.s([w.s([], 'hashprlei', '( { %s , %s } e. Fin /\\ ( # ` { %s , %s } ) <_ 2 )' % (PL, MI, PL, MI))], 'simpri', '( # ` { %s , %s } ) <_ 2' % (PL, MI)), '( # ` { %s , %s } ) <_ 2' % (PL, MI))
    fin = lin8(w, A0, [hs, h2_], ante_of(S['zrband'])[1], {'( # ` %s )' % BAND: c([c([c.a1(w.s([], 'prfi', '{ %s , %s } e. Fin' % (PL, MI)), '{ %s , %s } e. Fin' % (PL, MI)), ss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % BAND), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % BAND) and c([c([c([c.a1(w.s([], 'prfi', '{ %s , %s } e. Fin' % (PL, MI)), '{ %s , %s } e. Fin' % (PL, MI)), ss, w.inst('ssfi')], 'syl2anc', '%s e. Fin' % BAND), w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % BAND)], 'nn0red', '( # ` %s ) e. RR' % BAND),
         '( # ` { %s , %s } )' % (PL, MI): c([c.a1(w.s([], 'prfi', '{ %s , %s } e. Fin' % (PL, MI)), '{ %s , %s } e. Fin' % (PL, MI)), w.inst('hashcl')], 'syl', '( # ` { %s , %s } ) e. NN0' % (PL, MI)) and c([c([c.a1(w.s([], 'prfi', '{ %s , %s } e. Fin' % (PL, MI)), '{ %s , %s } e. Fin' % (PL, MI)), w.inst('hashcl')], 'syl', '( # ` { %s , %s } ) e. NN0' % (PL, MI))], 'nn0red', '( # ` { %s , %s } ) e. RR' % (PL, MI))})
    w.qed([fin], 'idi', S['zrband'])
    return run8(w)


GENS['zrband'] = gen_band
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
