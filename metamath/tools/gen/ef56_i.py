"""Sortie EF56: the residue identity on the zeta rectangle for a generic F (ef6rid, after EF4's ef4id)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts, pt_parts


def gen_id(idc=False):
    from ef4_b import LD0F, ld0_mem, hp0_mem
    w = W('ef6rid', 'The residue identity on the rectangle ` [ S , c ] x [ - U , V ] ` for ` F ` with disk data, cut at the heights ` G ` ( Lean ` rectInt_chain ` with ` rectInt_edges ` in ` contour_zeta ` ): ` 2 pi i SR = ( ( BOT + RIGHT ) - TOP ) - LEFT ` , and the four edges are complex numbers ( ~ ef3chain , ~ rectintco , ~ lintrev ).')
    A00, G = ante_of(S['ef6rid'])
    LX = 'A. x e. ( S [,] %s ) ( %s ` %s ) =/= 0' % (C1, 'F', PTL('x', CHN('j')))
    LO_ = 'A. o e. ( S [,] %s ) ( %s ` %s ) =/= 0' % (C1, 'F', PTL('o', CHN('j')))
    LT = 'A. t e. ( -u U [,] V ) ( %s ` %s ) =/= 0' % ('F', PTL('S', 't'))
    LY = 'A. y e. ( -u U [,] V ) ( %s ` %s ) =/= 0' % ('F', PTL('S', 'y'))
    A0 = A00.replace(LX, LO_).replace(LT, LY).replace(DD(), DDR())
    c = Ctx(w, A0)
    yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    ur = c.g('U e. RR'); vr = c.g('V e. RR'); tu = c.g('T <_ U'); tv = c.g('T <_ V')
    sr = c.g('S e. RR'); s916 = c.g('( 9 / ; 1 6 ) <_ S'); sc1 = c.g('S < %s' % C1)
    kn = c.g('K e. NN'); gf = c.g('G : ( 0 ... K ) --> RR')
    STEP = 'A. j e. ( 0 ..^ K ) ( %s < %s /\\ ( %s - %s ) <_ 1 )' % (CHN('j'), GJ1, GJ1, CHN('j'))
    stp = c.g(STEP)
    g0 = c.g('( G ` 0 ) = -u U'); gk = c.g('( G ` K ) = V')
    lines = c.g('A. j e. ( 0 ... K ) %s' % LO_)
    left = c.g(LY)
    f = c1_facts(w, c, yr, y100)
    ddeq = dd_ren(w)
    dd = c([c.g(DDR()), c.a1(ddeq, '( %s <-> %s )' % (DD(), DDR()))], 'mpbird', DD())
    hol, _, _, _, nz = dd_parts(w, A0, dd, 'F', 'A')
    D0 = LD0F('F')
    ldc = c([hol, f['yp'], w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (LDF_, D0))
    ntr, nur = c([tr], 'renegcld', '-u T e. RR'), c([ur], 'renegcld', '-u U e. RR')
    lvn = {'T': tr, 'U': ur, 'V': vr, 'S': sr}
    s0 = lin8(w, A0, [s916], '0 < S', lvn)
    # the chain
    CH = tsub(stmt('ef3chain'), {'C': C1, 'M': 'K'})
    cha, chc = ante_of(CH)
    cbx, _ = cbvral(w, '( S [,] %s )' % C1, 'o', 'x', '( %s ` %s ) =/= 0' % ('F', PTL('o', CHN('j'))))
    rbx = w.s([cbx], 'ralbii', '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LO_, LX))
    linx = c([lines, c.a1(rbx, '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LO_, LX))], 'mpbid', 'A. j e. ( 0 ... K ) %s' % LX)
    cby, _ = cbvral(w, '( -u U [,] V )', 'y', 't', '( %s ` %s ) =/= 0' % ('F', PTL('S', 'y')))
    lt_ = c([left, c.a1(cby, '( %s <-> %s )' % (LY, LT))], 'mpbid', LT)
    LTG = 'A. t e. ( ( G ` 0 ) [,] ( G ` K ) ) ( %s ` %s ) =/= 0' % ('F', PTL('S', 't'))
    ieq = c([c([g0], 'eqcomd', '-u U = ( G ` 0 )'), c([gk], 'eqcomd', 'V = ( G ` K )')], 'oveq12d', '( -u U [,] V ) = ( ( G ` 0 ) [,] ( G ` K ) )')
    ltg = c([lt_, c([ieq], 'raleqdv', '( %s <-> %s )' % (LT, LTG))], 'mpbid', LTG)
    ch = c([conj(w, A0, cha, {DD(): dd, 'Y e. RR': yr, '1 < Y': f['y1'], 'S e. RR': sr, '%s e. RR' % C1: f['c1r'], '( 9 / ; 1 6 ) <_ S': s916, 'S < %s' % C1: sc1,
                                  '1 < %s' % C1: f['c1g'], '%s <_ ( 5 / 4 )' % C1: f['c54'], 'K e. NN': kn, 'G : ( 0 ... K ) --> RR': gf, STEP: stp, 'A. j e. ( 0 ... K ) %s' % LX: linx, LTG: ltg}),
             w.inst('ef3chain')], 'syl', chc)
    rw, chc2 = w.wcongr(chc, {}, A0, {}, rules={'( G ` 0 )': ('-u U', g0), '( G ` K )': ('V', gk)})
    ch2 = c([ch, rw], 'mpbid', chc2)
    RI = chc2.split(' = ')[0]
    # rectangle decomposition
    RC = tsub(stmt('rectintco'), {'F': LDF_, 'P': 'S', 'Q': C1, 'S': '-u U', 'R': 'V'})
    rca, rcc = ante_of(RC)
    rco = c([c([ldc], 'elexd', '%s e. _V' % LDF_), c([sr, f['c1r']], 'jca', '( S e. RR /\\ %s e. RR )' % C1), c([nur, vr], 'jca', '( -u U e. RR /\\ V e. RR )'), w.inst('rectintco')], 'syl3anc', rcc)
    LI = lambda a, b: '( %s lint <. %s , %s >. )' % (LDF_, a, b)
    P_ = lambda x, y: PTL(x, y)
    # membership of the lines in LD0
    def hline(y_, eqst, j_):
        """( A0 -> A. x e. ( S [,] C1 ) ( x + i y_ ) e. D0 ) from the line at j_ with ( G ` j_ ) = y_ (eqst)"""
        Ax = '( %s /\\ x e. ( S [,] %s ) )' % (A0, C1)
        cx = Ctx(w, Ax)
        xin = cx([], 'simpr', 'x e. ( S [,] %s )' % C1)
        jin = lift(w, c([kn], 'nnnn0d', 'K e. NN0') and c([c([kn], 'nnnn0d', 'K e. NN0'), w.inst('0elfz' if j_ == '0' else 'nn0fz0')], 'syl' if j_ == '0' else 'sylib', '%s e. ( 0 ... K )' % j_), Ax)
        lj, _ = ral_at(w, Ax, lift(w, lines, Ax), 'j', j_, LO_, jin)
        lx, _ = ral_at(w, Ax, lj, 'o', 'x', '( %s ` %s ) =/= 0' % ('F', PTL('o', CHN(j_))), xin)
        lx2 = cx([lx, cx([cx([cx([lift(w, eqst, Ax)], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (CHN(j_), y_))], 'oveq2d', '%s = %s' % (PTL('x', CHN(j_)), PTL('x', y_)))], 'fveq2d',
                                  '( %s ` %s ) = ( %s ` %s )' % ('F', PTL('x', CHN(j_)), 'F', PTL('x', y_))) and
                     cx([cx([cx([cx([lift(w, eqst, Ax)], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (CHN(j_), y_))], 'oveq2d', '%s = %s' % (PTL('x', CHN(j_)), PTL('x', y_)))], 'fveq2d',
                             '( %s ` %s ) = ( %s ` %s )' % ('F', PTL('x', CHN(j_)), 'F', PTL('x', y_)))], 'neeq1d', '( ( %s ` %s ) =/= 0 <-> ( %s ` %s ) =/= 0 )' % ('F', PTL('x', CHN(j_)), 'F', PTL('x', y_)))],
                 'mpbid', '( %s ` %s ) =/= 0' % ('F', PTL('x', y_)))
        xr, sx, _ = icc_out(cx, 'x', 'S', C1, xin, lift(w, sr, Ax), lift(w, f['c1r'], Ax))
        yr_ = lift(w, nur if y_ == '-u U' else vr, Ax)
        zc = ptc(cx, 'x', y_, xr, yr_)
        rz = cx([xr, yr_, w.inst('crre')], 'syl2anc', '( Re ` %s ) = x' % PTL('x', y_))
        x0 = lin8(w, Ax, [sx, lift(w, s0, Ax)], '0 < x', {'x': xr, 'S': lift(w, sr, Ax)})
        zh = hp0_mem(cx, PTL('x', y_), zc, rz, x0)
        return c([ld0_mem(w, Ax, 'F', PTL('x', y_), zh, lx2)], 'ralrimiva', 'A. x e. ( S [,] %s ) %s e. %s' % (C1, PTL('x', y_), D0))

    def vline(x_, lo, hi, lor, hir, mem_fn):
        At = '( %s /\\ t e. ( %s [,] %s ) )' % (A0, lo, hi)
        ct = Ctx(w, At)
        tin = ct([], 'simpr', 't e. ( %s [,] %s )' % (lo, hi))
        trr, _, _ = icc_out(ct, 't', lo, hi, tin, lift(w, lor, At), lift(w, hir, At))
        return c([mem_fn(At, ct, tin, trr)], 'ralrimiva', 'A. t e. ( %s [,] %s ) %s e. %s' % (lo, hi, PTL(x_, 't'), D0))

    def right_mem(At, ct, tin, trr):
        z = PTL(C1, 't')
        zc = ptc(ct, C1, 't', lift(w, f['c1r'], At), trr)
        rz = ct([lift(w, f['c1r'], At), trr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (z, C1))
        r1 = ct([lift(w, f['c1g'], At), ct([rz], 'eqcomd', '%s = ( Re ` %s )' % (C1, z))], 'breqtrd', '1 < ( Re ` %s )' % z)
        rzr = ct([zc], 'recld', '( Re ` %s ) e. RR' % z)
        r0 = lin8(w, At, [r1], '0 < ( Re ` %s )' % z, {'( Re ` %s )' % z: rzr})
        zhp = hp0_mem(ct, z, zc, None, r0)
        nzb, _ = ral_at(w, At, lift(w, nz, At), 'w', z, '( 1 < ( Re ` w ) -> ( F ` w ) =/= 0 )', zhp)
        fnz = ct([r1, nzb], 'mpd', '( F ` %s ) =/= 0' % z)
        return ld0_mem(w, At, 'F', z, zhp, fnz)

    def left_mem(At, ct, tin, trr):
        ly, _ = ral_at(w, At, lift(w, left, At), 'y', 't', '( %s ` %s ) =/= 0' % ('F', PTL('S', 'y')), tin)
        zc = ptc(ct, 'S', 't', lift(w, sr, At), trr)
        rz = ct([lift(w, sr, At), trr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = S' % PTL('S', 't'))
        zh = hp0_mem(ct, PTL('S', 't'), zc, rz, lift(w, s0, At))
        return ld0_mem(w, At, 'F', PTL('S', 't'), zh, ly)
    hb = hline('-u U', g0, '0')
    ht = hline('V', gk, 'K')
    vr_all = vline(C1, '-u U', 'V', nur, vr, right_mem)
    vl_all = vline('S', '-u U', 'V', nur, vr, left_mem)
    def hseg(y_, yr_, hl):
        HS = tsub(stmt('ef3hseg'), {'M': y_, 'P': 'S', 'Q': C1, 'E': 'S', 'K': C1, 'D': D0})
        ha, hcn = ante_of(HS)
        sx, cx_ = c([sr], 'rexrd', 'S e. RR*'), c([f['c1r']], 'rexrd', '%s e. RR*' % C1)
        sle = lin8(w, A0, [sc1], 'S <_ %s' % C1, {'S': sr, C1: f['c1r']})
        sin = c([sx, cx_, sle, w.inst('lbicc2')], 'syl3anc', 'S e. ( S [,] %s )' % C1)
        cin = c([sx, cx_, sle, w.inst('ubicc2')], 'syl3anc', '%s e. ( S [,] %s )' % (C1, C1))
        return c([conj(w, A0, ha, {'%s e. RR' % y_: yr_, 'S e. RR': sr, '%s e. RR' % C1: f['c1r'], 'S e. ( S [,] %s )' % C1: sin, '%s e. ( S [,] %s )' % (C1, C1): cin, top_and(top_and(ha)[1])[1]: hl}), w.inst('ef3hseg')], 'syl', hcn)
    def vseg(x_, xr_, lo, hi, a, b, ain, bin_, vl):
        VS = tsub(stmt('ef3vseg'), {'P': x_, 'L': lo, 'H': hi, 'E': a, 'K': b, 'D': D0})
        va, vcn = ante_of(VS)
        return c([conj(w, A0, va, {'%s e. RR' % x_: xr_, '%s e. RR' % lo: nur, '%s e. RR' % hi: vr, '%s e. ( %s [,] %s )' % (a, lo, hi): ain, '%s e. ( %s [,] %s )' % (b, lo, hi): bin_, top_and(top_and(va)[1])[1]: vl}), w.inst('ef3vseg')], 'syl', vcn)
    nux, vx = c([nur], 'rexrd', '-u U e. RR*'), c([vr], 'rexrd', 'V e. RR*')
    uvl = lin8(w, A0, [tu, tv, t2], '-u U <_ V', lvn)
    nuin = c([nux, vx, uvl, w.inst('lbicc2')], 'syl3anc', '-u U e. ( -u U [,] V )')
    vin = c([nux, vx, uvl, w.inst('ubicc2')], 'syl3anc', 'V e. ( -u U [,] V )')
    segs = {'BOT': hseg('-u U', nur, hb), 'TOP': hseg('V', vr, ht), 'LEFT': vseg('S', sr, '-u U', 'V', '-u U', 'V', nuin, vin, vl_all),
            'RIGHT': vseg(C1, f['c1r'], '-u U', 'V', '-u U', 'V', nuin, vin, vr_all)}
    ends = {'BOT': (P_('S', '-u U'), P_(C1, '-u U')), 'TOP': (P_('S', 'V'), P_(C1, 'V')), 'LEFT': (P_('S', '-u U'), P_('S', 'V')),
            'RIGHT': (P_(C1, '-u U'), P_(C1, 'V'))}
    reals = {'S': sr, C1: f['c1r'], '-u U': nur, 'V': vr, '-u T': ntr, 'T': tr}
    def pcc(x_, y_):
        return ptc(c, x_, y_, reals[x_], reals[y_])
    def hy(k):
        a, b = ends[k]
        xa, ya = a[2:].split(' + ( _i x. ')[0], None
        return c([c([pcc(*pt_parts(a)), pcc(*pt_parts(b))], 'jca', '( %s e. CC /\\ %s e. CC )' % (a, b)), c([ldc, segs[k]], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (LDF_, D0, a, b, D0))],
                 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (a, b, LDF_, D0, a, b, D0))
    lcl = {k: c([hy(k), w.inst('lintcl')], 'syl', '%s e. CC' % LI(*ends[k])) for k in ends}
    rt = c([hy('TOP'), w.inst('lintrev')], 'syl', '%s = -u %s' % (LI(ends['TOP'][1], ends['TOP'][0]), LI(*ends['TOP'])))
    rl = c([hy('LEFT'), w.inst('lintrev')], 'syl', '%s = -u %s' % (LI(ends['LEFT'][1], ends['LEFT'][0]), LI(*ends['LEFT'])))
    # algebra
    BOTl, TOPl, LEFTl, RIGHT = (LI(*ends[k]) for k in ('BOT', 'TOP', 'LEFT', 'RIGHT'))
    clos = c([c([lcl['BOT'], lcl['TOP']], 'jca', '( %s e. CC /\\ %s e. CC )' % (BOTl, TOPl)), c([lcl['LEFT'], lcl['RIGHT']], 'jca', '( %s e. CC /\\ %s e. CC )' % (LEFTl, RIGHT))], 'jca',
             '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. CC /\\ %s e. CC ) )' % (BOTl, TOPl, LEFTl, RIGHT))
    TOPr, LEFTr = LI(ends['TOP'][1], ends['TOP'][0]), LI(ends['LEFT'][1], ends['LEFT'][0])
    BIG = '( ( %s + %s ) + ( -u %s + -u %s ) )' % (BOTl, RIGHT, TOPl, LEFTl)
    e_b = c([rco, c([rt, rl], 'oveq12d', '( %s + %s ) = ( -u %s + -u %s )' % (TOPr, LEFTr, TOPl, LEFTl)) and
             c([c([], 'eqidd', '( %s + %s ) = ( %s + %s )' % (BOTl, RIGHT, BOTl, RIGHT)), c([rt, rl], 'oveq12d', '( %s + %s ) = ( -u %s + -u %s )' % (TOPr, LEFTr, TOPl, LEFTl))],
               'oveq12d', '( ( %s + %s ) + ( %s + %s ) ) = %s' % (BOTl, RIGHT, TOPr, LEFTr, BIG))], 'eqtrd', '%s = %s' % (RI, BIG))
    SR_ = '( %s x. %s )' % (TPI, SRF)
    e_s = c([c([ch2], 'eqcomd', '%s = %s' % (SR_, RI)), e_b], 'eqtrd', '%s = %s' % (SR_, BIG))
    cl = Closure(w, A0, {BOTl: ('CC', lcl['BOT']), TOPl: ('CC', lcl['TOP']), RIGHT: ('CC', lcl['RIGHT']), LEFTl: ('CC', lcl['LEFT'])})
    for k in (BOTl, TOPl, RIGHT, LEFTl):
        cl.atom(k)
    RHS = '( ( ( %s + %s ) - %s ) - %s )' % (BOTl, RIGHT, TOPl, LEFTl)
    fin = c([c([e_s, ringeq(w, A0, BIG, RHS, cl)], 'eqtrd', '%s = %s' % (SR_, RHS)), clos], 'jca', G)
    return finish_id(w, A00, A0, fin, LX, LO_, LT, LY, 'ef6rid')


def finish_id(w, A00, A0, fin, LX, LO_, LT, LY, lab):
    c0 = Ctx(w, A00)
    rb1 = w.s([w.s([cbvral(w, '( S [,] %s )' % C1, 'x', 'o', '( %s ` %s ) =/= 0' % ('F', PTL('x', CHN('j'))))[0]], 'ralbii', '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LX, LO_))], 'idi',
              '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LX, LO_))
    rb2 = cbvral(w, '( -u U [,] V )', 't', 'y', '( %s ` %s ) =/= 0' % ('F', PTL('S', 't')))[0]
    RL0 = '( A. j e. ( 0 ... K ) %s /\\ %s )' % (LX, LT)
    RL1 = '( A. j e. ( 0 ... K ) %s /\\ %s )' % (LO_, LY)
    rb = w.s([rb1, rb2], 'anbi12i', '( %s <-> %s )' % (RL0, RL1))
    ddeq = dd_ren(w)
    a0 = rebuild(w, c0, A0, {RL1: c0([c0.g(RL0), c0.a1(rb, '( %s <-> %s )' % (RL0, RL1))], 'mpbid', RL1), DDR(): c0([c0.g(DD()), c0.a1(ddeq, '( %s <-> %s )' % (DD(), DDR()))], 'mpbid', DDR())})
    w.qed([a0, fin], 'syl', S[lab])
    return run8(w)




GENS = {'ef6rid': gen_id}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
