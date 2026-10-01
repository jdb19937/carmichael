"""Sortie EF4: the vertical split (ef4vsl), the contour identity (ef4id)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
from c8_o import numst
import congr as _cg
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
import ef1lib as _ef1


def gen_vsl():
    w = W('ef4vsl', 'A line integral along a vertical segment inside ` D ` splits at an intermediate height ( ~ lintsplit ; Lean ` integral_add_adjacent_intervals ` on the right edge).')
    A0, G = ante_of(S['ef4vsl'])
    c = Ctx(w, A0)
    gcn = c.g('G e. ( D -cn-> CC )'); cr = c.g('C e. RR'); pr = c.g('P e. RR'); qr = c.g('Q e. RR'); rr = c.g('R e. RR')
    pq = c.g('P <_ Q'); qrl = c.g('Q <_ R'); prl = c.g('P < R')
    alt = c.g('A. t e. ( P [,] R ) %s e. D' % PV('t'))
    Aa, Bb, Qq = PV('P'), PV('R'), PV('Q')
    ac, bc, qc = ptc(c, 'C', 'P', cr, pr), ptc(c, 'C', 'R', cr, rr), ptc(c, 'C', 'Q', cr, qr)
    px, rx = c([pr], 'rexrd', 'P e. RR*'), c([rr], 'rexrd', 'R e. RR*')
    ple = lin8(w, A0, [prl], 'P <_ R', {'P': pr, 'R': rr})
    pin = c([px, rx, ple, w.inst('lbicc2')], 'syl3anc', 'P e. ( P [,] R )')
    rin = c([px, rx, ple, w.inst('ubicc2')], 'syl3anc', 'R e. ( P [,] R )')
    VS = tsub(stmt('ef3vseg'), {'P': 'C', 'L': 'P', 'H': 'R', 'E': 'P', 'K': 'R'})
    va, vcn = ante_of(VS)
    seg = c([conj(w, A0, va, {'C e. RR': cr, 'P e. RR': pr, 'R e. RR': rr, 'P e. ( P [,] R )': pin, 'R e. ( P [,] R )': rin, top_and(top_and(va)[1])[1]: alt}), w.inst('ef3vseg')], 'syl', vcn)
    SS = '( ( Q - P ) / ( R - P ) )'
    rpp = c([c([rr, pr], 'resubcld', '( R - P ) e. RR'), lin8(w, A0, [prl], '0 < ( R - P )', {'P': pr, 'R': rr})], 'elrpd', '( R - P ) e. RR+')
    qpr = c([qr, pr], 'resubcld', '( Q - P ) e. RR')
    s0 = c([qpr, rpp, lin8(w, A0, [pq], '0 <_ ( Q - P )', {'P': pr, 'Q': qr})], 'divge0d', '0 <_ %s' % SS)
    s1 = c([lin8(w, A0, [qrl], '( Q - P ) <_ ( R - P )', {'P': pr, 'Q': qr, 'R': rr}), c([qpr, rpp, w.inst('divle1le')], 'syl2anc', '( %s <_ 1 <-> ( Q - P ) <_ ( R - P ) )' % SS)], 'mpbird', '%s <_ 1' % SS)
    ssr = c([qpr, rpp], 'rerpdivcld', '%s e. RR' % SS)
    sin = icc_in(c, SS, '0', '1', ssr, numst(w, A0, '0', 'RR'), numst(w, A0, '1', 'RR'), s0, s1)
    cl = Closure(w, A0, {'C': ('RR', cr), 'P': ('RR', pr), 'R': ('RR', rr), SS: ('RR', ssr), '_i': ('CC', ic_(c))})
    for k in ('C', 'P', 'R', SS, '_i'):
        cl.atom(k)
    RHS = '( %s + ( %s x. ( %s - %s ) ) )' % (Aa, SS, Bb, Aa)
    e1 = ringeq(w, A0, RHS, PV('( P + ( %s x. ( R - P ) ) )' % SS), cl)
    dc = c([c([qpr], 'recnd', '( Q - P ) e. CC'), c([rpp], 'rpcnd', '( R - P ) e. CC'), c([rpp], 'rpne0d', '( R - P ) =/= 0')], 'divcan1d', '( %s x. ( R - P ) ) = ( Q - P )' % SS)
    e2 = c([c([dc], 'oveq2d', '( P + ( %s x. ( R - P ) ) ) = ( P + ( Q - P ) )' % SS), c([c([pr], 'recnd', 'P e. CC'), c([qr], 'recnd', 'Q e. CC')], 'pncan3d', '( P + ( Q - P ) ) = Q')], 'eqtrd', '( P + ( %s x. ( R - P ) ) ) = Q' % SS)
    e3 = c([c([e2], 'oveq2d', '( _i x. ( P + ( %s x. ( R - P ) ) ) ) = ( _i x. Q )' % SS)], 'oveq2d', '%s = %s' % (PV('( P + ( %s x. ( R - P ) ) )' % SS), Qq))
    cq = c([c([e1, e3], 'eqtrd', '%s = %s' % (RHS, Qq))], 'eqcomd', '%s = %s' % (Qq, RHS))
    hy = c([c([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (Aa, Bb)), c([gcn, seg], 'jca', '( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (Aa, Bb))], 'jca',
           '( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (Aa, Bb, Aa, Bb))
    w.qed([hy, sin, cq, w.inst('lintsplit')], 'syl3anc', S['ef4vsl'])
    return run8(w)



def c1_facts(w, c, yr, y100):
    """C1 = 1 + 1 / log Y: e. RR, 1 < C1, C1 <_ 5 / 4, and Y e. RR+, 1 < Y"""
    A = c.A
    y1 = lin8(w, A, [y100], '1 < Y', {'Y': yr})
    yp = c([yr, lin8(w, A, [y100], '0 < Y', {'Y': yr})], 'elrpd', 'Y e. RR+')
    L = '( log ` Y )'
    lp = c([yr, y1], 'rplogcld', '%s e. RR+' % L)
    lr = c([lp], 'rpred', '%s e. RR' % L)
    l4 = c([c([yr, y100], 'jca', '( Y e. RR /\\ ; ; 1 0 0 <_ Y )'), w.inst('ef1l4')], 'syl', '4 <_ %s' % L)
    UP = '( 1 / %s )' % L
    upp = c([lp], 'rpreccld', '%s e. RR+' % UP)
    upr = c([upp], 'rpred', '%s e. RR' % UP)
    c1r = c([numst(w, A, '1', 'RR'), upr], 'readdcld', '%s e. RR' % C1)
    c1g = lin8(w, A, [c([upp], 'rpgt0d', '0 < %s' % UP)], '1 < %s' % C1, {UP: upr})
    u4 = c([c([l4, c([numst(w, A, '4', 'RR+'), lp], 'lerecd', '( 4 <_ %s <-> ( 1 / %s ) <_ ( 1 / 4 ) )' % (L, L))], 'mpbid', '( 1 / %s ) <_ ( 1 / 4 )' % L)], 'idi', '%s <_ ( 1 / 4 )' % UP)
    c54 = lin8(w, A, [u4], '%s <_ ( 5 / 4 )' % C1, {UP: upr})
    return dict(y1=y1, yp=yp, c1r=c1r, c1g=c1g, c54=c54, l4=l4, lr=lr, lp=lp)


def gen_id(idc=False):
    from ef4_b import lfn_pt, LD0F, ld0_mem, hp0_mem
    w = W('ef4idc', 'The edge integrals and the Perron sum of the contour of ~ ef4id are complex numbers.') if idc else W('ef4id', 'The contour identity of Lean ` contour_ne_one ` ( ` hmaster ` ): on the rectangle ` [ S , c ] x [ - U , V ] ` cut at the heights ` G ` , ` PS + 2 pi i SR = ( BOT - TOP ) + ( EB + ET ) - LEFT ` ( ~ ef3chain , ~ rectintco , the right edge split at ` +- T ` by ~ ef4vsl , its middle ` - PS ` by ~ ef4rm ).')
    A00, G = ante_of(S['ef4idc'] if idc else S['ef4id'])
    LX = 'A. x e. ( S [,] %s ) ( %s ` %s ) =/= 0' % (C1, LFN, PTL('x', CHN('j')))
    LO_ = 'A. o e. ( S [,] %s ) ( %s ` %s ) =/= 0' % (C1, LFN, PTL('o', CHN('j')))
    LT = 'A. t e. ( -u U [,] V ) ( %s ` %s ) =/= 0' % (LFN, PTL('S', 't'))
    LY = 'A. y e. ( -u U [,] V ) ( %s ` %s ) =/= 0' % (LFN, PTL('S', 'y'))
    A0 = A00.replace(LX, LO_).replace(LT, LY)
    c = Ctx(w, A0)
    chi = c.g(CHI); yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    ur = c.g('U e. RR'); vr = c.g('V e. RR'); tu = c.g('T <_ U'); tv = c.g('T <_ V')
    sr = c.g('S e. RR'); s916 = c.g('( 9 / ; 1 6 ) <_ S'); sc1 = c.g('S < %s' % C1)
    kn = c.g('K e. NN'); gf = c.g('G : ( 0 ... K ) --> RR')
    STEP = 'A. j e. ( 0 ..^ K ) ( %s < %s /\\ ( %s - %s ) <_ 1 )' % (CHN('j'), GJ1, GJ1, CHN('j'))
    stp = c.g(STEP)
    g0 = c.g('( G ` 0 ) = -u U'); gk = c.g('( G ` K ) = V')
    lines = c.g('A. j e. ( 0 ... K ) %s' % LO_)
    left = c.g(LY)
    f = c1_facts(w, c, yr, y100)
    dd = c([chi, w.inst('ef2ddl')], 'syl', DD(LFN, 'N'))
    hol, _, _, _, nz = dd_parts(w, A0, dd, LFN, 'N')
    D0 = LD0F(LFN)
    ldc = c([hol, f['yp'], w.inst('ef3ldc')], 'syl2anc', '%s e. ( %s -cn-> CC )' % (LDL, D0))
    ntr, nur = c([tr], 'renegcld', '-u T e. RR'), c([ur], 'renegcld', '-u U e. RR')
    lvn = {'T': tr, 'U': ur, 'V': vr, 'S': sr}
    s0 = lin8(w, A0, [s916], '0 < S', lvn)
    # the chain
    CH = tsub(stmt('ef3chain'), {'F': LFN, 'A': 'N', 'C': C1, 'M': 'K'})
    cha, chc = ante_of(CH)
    cbx, _ = cbvral(w, '( S [,] %s )' % C1, 'o', 'x', '( %s ` %s ) =/= 0' % (LFN, PTL('o', CHN('j'))))
    rbx = w.s([cbx], 'ralbii', '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LO_, LX))
    linx = c([lines, c.a1(rbx, '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LO_, LX))], 'mpbid', 'A. j e. ( 0 ... K ) %s' % LX)
    cby, _ = cbvral(w, '( -u U [,] V )', 'y', 't', '( %s ` %s ) =/= 0' % (LFN, PTL('S', 'y')))
    lt_ = c([left, c.a1(cby, '( %s <-> %s )' % (LY, LT))], 'mpbid', LT)
    LTG = 'A. t e. ( ( G ` 0 ) [,] ( G ` K ) ) ( %s ` %s ) =/= 0' % (LFN, PTL('S', 't'))
    ieq = c([c([g0], 'eqcomd', '-u U = ( G ` 0 )'), c([gk], 'eqcomd', 'V = ( G ` K )')], 'oveq12d', '( -u U [,] V ) = ( ( G ` 0 ) [,] ( G ` K ) )')
    ltg = c([lt_, c([ieq], 'raleqdv', '( %s <-> %s )' % (LT, LTG))], 'mpbid', LTG)
    ch = c([conj(w, A0, cha, {DD(LFN, 'N'): dd, 'Y e. RR': yr, '1 < Y': f['y1'], 'S e. RR': sr, '%s e. RR' % C1: f['c1r'], '( 9 / ; 1 6 ) <_ S': s916, 'S < %s' % C1: sc1,
                                  '1 < %s' % C1: f['c1g'], '%s <_ ( 5 / 4 )' % C1: f['c54'], 'K e. NN': kn, 'G : ( 0 ... K ) --> RR': gf, STEP: stp, 'A. j e. ( 0 ... K ) %s' % LX: linx, LTG: ltg}),
             w.inst('ef3chain')], 'syl', chc)
    rw, chc2 = w.wcongr(chc, {}, A0, {}, rules={'( G ` 0 )': ('-u U', g0), '( G ` K )': ('V', gk)})
    ch2 = c([ch, rw], 'mpbid', chc2)
    RI = chc2.split(' = ')[0]
    # rectangle decomposition
    RC = tsub(stmt('rectintco'), {'F': LDL, 'P': 'S', 'Q': C1, 'S': '-u U', 'R': 'V'})
    rca, rcc = ante_of(RC)
    rco = c([c([ldc], 'elexd', '%s e. _V' % LDL), c([sr, f['c1r']], 'jca', '( S e. RR /\\ %s e. RR )' % C1), c([nur, vr], 'jca', '( -u U e. RR /\\ V e. RR )'), w.inst('rectintco')], 'syl3anc', rcc)
    LI = lambda a, b: '( %s lint <. %s , %s >. )' % (LDL, a, b)
    P_ = lambda x, y: PTL(x, y)
    # membership of the lines in LD0
    def hline(y_, eqst, j_):
        """( A0 -> A. x e. ( S [,] C1 ) ( x + i y_ ) e. D0 ) from the line at j_ with ( G ` j_ ) = y_ (eqst)"""
        Ax = '( %s /\\ x e. ( S [,] %s ) )' % (A0, C1)
        cx = Ctx(w, Ax)
        xin = cx([], 'simpr', 'x e. ( S [,] %s )' % C1)
        jin = lift(w, c([kn], 'nnnn0d', 'K e. NN0') and c([c([kn], 'nnnn0d', 'K e. NN0'), w.inst('0elfz' if j_ == '0' else 'nn0fz0')], 'syl' if j_ == '0' else 'sylib', '%s e. ( 0 ... K )' % j_), Ax)
        lj, _ = ral_at(w, Ax, lift(w, lines, Ax), 'j', j_, LO_, jin)
        lx, _ = ral_at(w, Ax, lj, 'o', 'x', '( %s ` %s ) =/= 0' % (LFN, PTL('o', CHN(j_))), xin)
        lx2 = cx([lx, cx([cx([cx([lift(w, eqst, Ax)], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (CHN(j_), y_))], 'oveq2d', '%s = %s' % (PTL('x', CHN(j_)), PTL('x', y_)))], 'fveq2d',
                                  '( %s ` %s ) = ( %s ` %s )' % (LFN, PTL('x', CHN(j_)), LFN, PTL('x', y_))) and
                     cx([cx([cx([cx([lift(w, eqst, Ax)], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (CHN(j_), y_))], 'oveq2d', '%s = %s' % (PTL('x', CHN(j_)), PTL('x', y_)))], 'fveq2d',
                             '( %s ` %s ) = ( %s ` %s )' % (LFN, PTL('x', CHN(j_)), LFN, PTL('x', y_)))], 'neeq1d', '( ( %s ` %s ) =/= 0 <-> ( %s ` %s ) =/= 0 )' % (LFN, PTL('x', CHN(j_)), LFN, PTL('x', y_)))],
                 'mpbid', '( %s ` %s ) =/= 0' % (LFN, PTL('x', y_)))
        xr, sx, _ = icc_out(cx, 'x', 'S', C1, xin, lift(w, sr, Ax), lift(w, f['c1r'], Ax))
        yr_ = lift(w, nur if y_ == '-u U' else vr, Ax)
        zc = ptc(cx, 'x', y_, xr, yr_)
        rz = cx([xr, yr_, w.inst('crre')], 'syl2anc', '( Re ` %s ) = x' % PTL('x', y_))
        x0 = lin8(w, Ax, [sx, lift(w, s0, Ax)], '0 < x', {'x': xr, 'S': lift(w, sr, Ax)})
        zh = hp0_mem(cx, PTL('x', y_), zc, rz, x0)
        return c([ld0_mem(w, Ax, LFN, PTL('x', y_), zh, lx2)], 'ralrimiva', 'A. x e. ( S [,] %s ) %s e. %s' % (C1, PTL('x', y_), D0))

    def vline(x_, lo, hi, lor, hir, mem_fn):
        At = '( %s /\\ t e. ( %s [,] %s ) )' % (A0, lo, hi)
        ct = Ctx(w, At)
        tin = ct([], 'simpr', 't e. ( %s [,] %s )' % (lo, hi))
        trr, _, _ = icc_out(ct, 't', lo, hi, tin, lift(w, lor, At), lift(w, hir, At))
        return c([mem_fn(At, ct, tin, trr)], 'ralrimiva', 'A. t e. ( %s [,] %s ) %s e. %s' % (lo, hi, PTL(x_, 't'), D0))

    def right_mem(At, ct, tin, trr):
        d = lfn_pt(w, At, None, C1, 't', lift(w, f['c1r'], At), trr, lift(w, f['c1g'], At), lift(w, nz, At))
        return d['zin']

    def left_mem(At, ct, tin, trr):
        ly, _ = ral_at(w, At, lift(w, left, At), 'y', 't', '( %s ` %s ) =/= 0' % (LFN, PTL('S', 'y')), tin)
        zc = ptc(ct, 'S', 't', lift(w, sr, At), trr)
        rz = ct([lift(w, sr, At), trr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = S' % PTL('S', 't'))
        zh = hp0_mem(ct, PTL('S', 't'), zc, rz, lift(w, s0, At))
        return ld0_mem(w, At, LFN, PTL('S', 't'), zh, ly)
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
    ntin = icc_in(c, '-u T', '-u U', 'V', ntr, nur, vr, lin8(w, A0, [tu], '-u U <_ -u T', lvn), lin8(w, A0, [tv, t2], '-u T <_ V', lvn))
    ptin = icc_in(c, 'T', '-u U', 'V', tr, nur, vr, lin8(w, A0, [tu, t2], '-u U <_ T', lvn), tv)
    segs = {'BOT': hseg('-u U', nur, hb), 'TOP': hseg('V', vr, ht), 'LEFT': vseg('S', sr, '-u U', 'V', '-u U', 'V', nuin, vin, vl_all),
            'EB': vseg(C1, f['c1r'], '-u U', 'V', '-u U', '-u T', nuin, ntin, vr_all), 'ET': vseg(C1, f['c1r'], '-u U', 'V', 'T', 'V', ptin, vin, vr_all),
            'MID': vseg(C1, f['c1r'], '-u U', 'V', '-u T', 'T', ntin, ptin, vr_all)}
    ends = {'BOT': (P_('S', '-u U'), P_(C1, '-u U')), 'TOP': (P_('S', 'V'), P_(C1, 'V')), 'LEFT': (P_('S', '-u U'), P_('S', 'V')),
            'EB': (P_(C1, '-u U'), P_(C1, '-u T')), 'ET': (P_(C1, 'T'), P_(C1, 'V')), 'MID': (P_(C1, '-u T'), P_(C1, 'T'))}
    reals = {'S': sr, C1: f['c1r'], '-u U': nur, 'V': vr, '-u T': ntr, 'T': tr}
    def pcc(x_, y_):
        return ptc(c, x_, y_, reals[x_], reals[y_])
    def hy(k):
        a, b = ends[k]
        xa, ya = a[2:].split(' + ( _i x. ')[0], None
        return c([c([pcc(*pt_parts(a)), pcc(*pt_parts(b))], 'jca', '( %s e. CC /\\ %s e. CC )' % (a, b)), c([ldc, segs[k]], 'jca', '( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s )' % (LDL, D0, a, b, D0))],
                 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ ( %s cseg %s ) C_ %s ) )' % (a, b, LDL, D0, a, b, D0))
    lcl = {k: c([hy(k), w.inst('lintcl')], 'syl', '%s e. CC' % LI(*ends[k])) for k in ends}
    rt = c([hy('TOP'), w.inst('lintrev')], 'syl', '%s = -u %s' % (LI(ends['TOP'][1], ends['TOP'][0]), LI(*ends['TOP'])))
    rl = c([hy('LEFT'), w.inst('lintrev')], 'syl', '%s = -u %s' % (LI(ends['LEFT'][1], ends['LEFT'][0]), LI(*ends['LEFT'])))
    # right edge split
    V1 = tsub(stmt('ef4vsl'), {'G': LDL, 'D': D0, 'C': C1, 'P': '-u U', 'Q': '-u T', 'R': 'V'})
    v1a, v1c = ante_of(V1)
    uvs = lin8(w, A0, [tu, tv, t2], '-u U < V', lvn)
    s1 = c([conj(w, A0, v1a, {'%s e. ( %s -cn-> CC )' % (LDL, D0): ldc, '%s e. RR' % C1: f['c1r'], '-u U e. RR': nur, '-u T e. RR': ntr, 'V e. RR': vr,
                              '-u U <_ -u T': lin8(w, A0, [tu], '-u U <_ -u T', lvn), '-u T <_ V': lin8(w, A0, [tv, t2], '-u T <_ V', lvn), '-u U < V': uvs, top_and(v1a)[2]: vr_all}), w.inst('ef4vsl')], 'syl', v1c)
    V2 = tsub(stmt('ef4vsl'), {'G': LDL, 'D': D0, 'C': C1, 'P': '-u T', 'Q': 'T', 'R': 'V'})
    v2a, v2c = ante_of(V2)
    ltv = vline(C1, '-u T', 'V', ntr, vr, right_mem)
    s2 = c([conj(w, A0, v2a, {'%s e. ( %s -cn-> CC )' % (LDL, D0): ldc, '%s e. RR' % C1: f['c1r'], '-u T e. RR': ntr, 'T e. RR': tr, 'V e. RR': vr,
                              '-u T <_ T': lin8(w, A0, [t2], '-u T <_ T', lvn), 'T <_ V': tv, '-u T < V': lin8(w, A0, [tv, t2], '-u T < V', lvn), top_and(v2a)[2]: ltv}), w.inst('ef4vsl')], 'syl', v2c)
    RM = tsub(stmt('ef4rm'), {'C': C1})
    rma, rmc = ante_of(RM)
    rm = c([conj(w, A0, rma, {CHI: chi, 'Y e. RR+': f['yp'], '%s e. RR' % C1: f['c1r'], '1 < %s' % C1: f['c1g'], 'T e. RR': tr}), w.inst('ef4rm')], 'syl', rmc)
    RE = tsub(stmt('ef1redge'), {'C': C1})
    rea, rec_ = ante_of(RE)
    red = c([conj(w, A0, rea, {NX: c([chi, w.inst('simpl')], 'syl', NX), 'Y e. RR+': f['yp'], '%s e. RR' % C1: f['c1r'], '1 < %s' % C1: f['c1g'], 'T e. RR': tr}), w.inst('ef1redge')], 'syl', rec_)
    cv, pse = top_and(rec_)
    RHL = pse.split(' = ', 1)[1]
    rhc = c([c([red, w.inst('simpl')], 'syl', cv), w.inst('climcl')], 'syl', '%s e. CC' % RHL)
    psc = c([c([red, w.inst('simpr')], 'syl', pse), rhc], 'eqeltrd', '%s e. CC' % PS1)
    # algebra
    BOTl, TOPl, EBl, ETl, LEFTl, MIDl = (LI(*ends[k]) for k in ('BOT', 'TOP', 'EB', 'ET', 'LEFT', 'MID'))
    if idc:
        fin = c([c([lcl['BOT'], lcl['TOP']], 'jca', '( %s e. CC /\\ %s e. CC )' % (BOTl, TOPl)), c([lcl['EB'], lcl['ET']], 'jca', '( %s e. CC /\\ %s e. CC )' % (EBl, ETl)),
                 c([lcl['LEFT'], psc], 'jca', '( %s e. CC /\\ %s e. CC )' % (LEFTl, PS1))], '3jca', G)
        return finish_id(w, A00, A0, fin, LX, LO_, LT, LY, 'ef4idc')
    RIGHT = LI(P_(C1, '-u U'), P_(C1, 'V'))
    R2 = LI(P_(C1, '-u T'), P_(C1, 'V'))
    TOPr, LEFTr = LI(ends['TOP'][1], ends['TOP'][0]), LI(ends['LEFT'][1], ends['LEFT'][0])
    e_r2 = c([s2, c([rm], 'oveq1d', '( %s + %s ) = ( -u %s + %s )' % (MIDl, ETl, PS1, ETl))], 'eqtrd', '%s = ( -u %s + %s )' % (R2, PS1, ETl))
    e_r = c([s1, c([e_r2], 'oveq2d', '( %s + %s ) = ( %s + ( -u %s + %s ) )' % (EBl, R2, EBl, PS1, ETl))], 'eqtrd', '%s = ( %s + ( -u %s + %s ) )' % (RIGHT, EBl, PS1, ETl))
    BIG = '( ( %s + ( %s + ( -u %s + %s ) ) ) + ( -u %s + -u %s ) )' % (BOTl, EBl, PS1, ETl, TOPl, LEFTl)
    e_b = c([rco, c([c([e_r], 'oveq2d', '( %s + %s ) = ( %s + ( %s + ( -u %s + %s ) ) )' % (BOTl, RIGHT, BOTl, EBl, PS1, ETl)), c([rt, rl], 'oveq12d', '( %s + %s ) = ( -u %s + -u %s )' % (TOPr, LEFTr, TOPl, LEFTl))],
                     'oveq12d', '( ( %s + %s ) + ( %s + %s ) ) = %s' % (BOTl, RIGHT, TOPr, LEFTr, BIG))], 'eqtrd', '%s = %s' % (RI, BIG))
    SR_ = '( %s x. %s )' % (TPI, SRL)
    e_s = c([c([ch2], 'eqcomd', '%s = %s' % (SR_, RI)), e_b], 'eqtrd', '%s = %s' % (SR_, BIG))
    e_p = c([e_s], 'oveq2d', '( %s + %s ) = ( %s + %s )' % (PS1, SR_, PS1, BIG))
    cl = Closure(w, A0, {BOTl: ('CC', lcl['BOT']), TOPl: ('CC', lcl['TOP']), EBl: ('CC', lcl['EB']), ETl: ('CC', lcl['ET']), LEFTl: ('CC', lcl['LEFT']), PS1: ('CC', psc)})
    for k in (BOTl, TOPl, EBl, ETl, LEFTl, PS1):
        cl.atom(k)
    RHS = '( ( ( %s - %s ) + ( %s + %s ) ) - %s )' % (BOTl, TOPl, EBl, ETl, LEFTl)
    fin = c([e_p, ringeq(w, A0, '( %s + %s )' % (PS1, BIG), RHS, cl)], 'eqtrd', G)
    return finish_id(w, A00, A0, fin, LX, LO_, LT, LY, 'ef4id')


def finish_id(w, A00, A0, fin, LX, LO_, LT, LY, lab):
    c0 = Ctx(w, A00)
    rb1 = w.s([w.s([cbvral(w, '( S [,] %s )' % C1, 'x', 'o', '( %s ` %s ) =/= 0' % (LFN, PTL('x', CHN('j'))))[0]], 'ralbii', '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LX, LO_))], 'idi',
              '( A. j e. ( 0 ... K ) %s <-> A. j e. ( 0 ... K ) %s )' % (LX, LO_))
    rb2 = cbvral(w, '( -u U [,] V )', 't', 'y', '( %s ` %s ) =/= 0' % (LFN, PTL('S', 't')))[0]
    RL0 = '( A. j e. ( 0 ... K ) %s /\\ %s )' % (LX, LT)
    RL1 = '( A. j e. ( 0 ... K ) %s /\\ %s )' % (LO_, LY)
    rb = w.s([rb1, rb2], 'anbi12i', '( %s <-> %s )' % (RL0, RL1))
    a0 = rebuild(w, c0, A0, {RL1: c0([c0.g(RL0), c0.a1(rb, '( %s <-> %s )' % (RL0, RL1))], 'mpbid', RL1)})
    w.qed([a0, fin], 'syl', S[lab])
    return run8(w)


def pt_parts(p):
    """( x + ( _i x. y ) ) -> (x, y)"""
    inner = p[2:-2]
    x, rest = inner.split(' + ( _i x. ', 1)
    return x, rest[:-2]


GENS = {'ef4vsl': gen_vsl, 'ef4id': gen_id, 'ef4idc': lambda: gen_id(True)}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
