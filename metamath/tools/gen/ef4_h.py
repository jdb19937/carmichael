"""Sortie EF4: the nonvanishing on the contour (ef4ln), the numerics (ef4nm) and the assembly (ef4core, ef4cnt, ef4ef)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef4lib import *
from c8_o import numst
import congr as _cg
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts
from ef4_g import bz_in, elrab_unpack
from ef4lib import ne0_re, hp0_facts


class Mini:
    def __init__(self, w):
        self.w = w

    def corners(self, cc, x, y, xr, yr):
        w = self.w
        return [cc([xr, yr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = %s' % (PTL(x, y), x)), cc([xr, yr, w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (PTL(x, y), y))]


def gen_ln():
    w = W('ef4ln', 'The contour of Lean ` contour_ne_one ` meets no zero: the cut lines ` [ S , c ] + i G ( j ) ` ( ` hlines ` : the end lines are good heights, an interior line misses ` Im " BZ ` ) and the left edge ` S + i [ - U , T + 2 ] ` ( ` hleftnz ` : ` S ` misses ` Re " BZ ` ).')
    A0, G = ante_of(S['ef4ln'])
    c = Ctx(w, A0)
    M = Mini(w)
    g = c.g
    chi = g(CHI); yr = g('Y e. RR'); y100 = g('; ; 1 0 0 <_ Y'); tr = g('T e. RR'); t2 = g('2 <_ T')
    ur = g('U e. RR'); vr = g('V e. RR'); tu = g('T <_ U'); u1 = g('U <_ ( T + 1 )'); tv = g('T <_ V'); v1 = g('V <_ ( T + 1 )')
    sr = g('S e. RR'); s916 = g('( 9 / ; 1 6 ) <_ S'); s58 = g('S <_ ( 5 / 8 )')
    hgd = g(HGD)
    nsb = g('-. S e. ( Re " %s )' % BZ4)
    kn = g('K e. NN'); gf = g('G : ( 0 ... K ) --> RR'); g0 = g('( G ` 0 ) = -u U'); gk = g('( G ` K ) = V')
    avo = g('A. e e. ( 1 ..^ K ) -. ( G ` e ) e. ( Im " %s )' % BZ4)
    rng = g('A. e e. ( 0 ... K ) ( -u U <_ ( G ` e ) /\\ ( G ` e ) <_ V )')
    f = c1_facts(w, c, yr, y100)
    t4 = c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')
    X4 = BZ4.split(' | ')[0][len('{ r e. '):]
    def in_bz(A, zx, zy, zxr, zyr, fz, hy, lv):
        cc = Ctx(w, A)
        z = PTL(zx, zy)
        zc = ptc(cc, zx, zy, zxr, zyr)
        hy2 = hy + M.corners(cc, zx, zy, zxr, zyr)
        lv2 = dict(lv); lv2['( Re ` %s )' % z] = cc([zc], 'recld', '( Re ` %s ) e. RR' % z); lv2['( Im ` %s )' % z] = cc([zc], 'imcld', '( Im ` %s ) e. RR' % z)

        return bz_in(M, A, '( T + 4 )', lift(w, t4, A), z, zc, fz, hy2, lv2), zc
    def image(A, fn, z, zin, zc):
        cc = Ctx(w, A)
        ff = w.s([], 'ref' if fn == 'Re' else 'imf', '%s : CC --> RR' % fn)
        fun = cc.a1(w.s([ff, w.inst('ffun')], 'ax-mp', 'Fun %s' % fn), 'Fun %s' % fn)
        dm = w.s([ff, w.inst('fdm')], 'ax-mp', 'dom %s = CC' % fn)
        Aa, Bb = X4.split(' crect ')
        Aa, Bb = Aa[2:], Bb[:-2]
        bzdm = cc([cc.a1(w.s([], 'ssrab2', '%s C_ %s' % (BZ4, X4)), '%s C_ %s' % (BZ4, X4)), cc([crect_cc(w, A, Aa, Bb, tr), cc.a1(w.s([dm], 'eqcomi', 'CC = dom %s' % fn), 'CC = dom %s' % fn)], 'sseqtrd', '%s C_ dom %s' % (X4, fn))], 'sstrd', '%s C_ dom %s' % (BZ4, fn))
        return cc([zin, cc([fun, bzdm, w.inst('funfvima2')], 'syl2anc', '( %s e. %s -> ( %s ` %s ) e. ( %s " %s ) )' % (z, BZ4, fn, z, fn, BZ4))], 'mpd', '( %s ` %s ) e. ( %s " %s )' % (fn, z, fn, BZ4))
    # lines
    Aj = '( %s /\\ j e. ( 0 ... K ) )' % A0
    Ax = '( %s /\\ x e. ( S [,] %s ) )' % (Aj, C1)
    cx = Ctx(w, Ax)
    L = lambda st: lift(w, st, Ax)
    jin = w.s([w.s([], 'simpr', '( %s -> j e. ( 0 ... K ) )' % Aj)], 'adantr', '( %s -> j e. ( 0 ... K ) )' % Ax)
    xin = cx([], 'simpr', 'x e. ( S [,] %s )' % C1)
    xr, sx, xc1 = icc_out(cx, 'x', 'S', C1, xin, L(sr), L(f['c1r']))
    gj = cx([L(gf), jin], 'ffvelcdmd', '%s e. RR' % CHN('j'))
    lvx = {'x': xr, 'S': L(sr), C1: L(f['c1r']), 'T': L(tr), 'U': L(ur), 'V': L(vr), CHN('j'): gj}
    vin = icc_in(cx, 'x', '( 1 / 2 )', '3', xr, numst(w, Ax, '( 1 / 2 )', 'RR'), numst(w, Ax, '3', 'RR'), lin8(w, Ax, [sx, L(s916)], '( 1 / 2 ) <_ x', lvx), lin8(w, Ax, [xc1, L(f['c54'])], 'x <_ 3', lvx))
    GD2 = '( %s /\\ %s )' % (GOOD(PTL('v', '-u U'), LFN, LN4), GOOD(PTL('v', 'V'), LFN, LN4))
    gx, gxv = ral_at(w, Ax, L(hgd), 'v', 'x', GD2, vin)
    TGT = '( %s ` %s ) =/= 0' % (LFN, PTL('x', CHN('j')))
    def endcase(eqj, val, sel, gval):
        A2 = '( %s /\\ j = %s )' % (Ax, eqj)
        c2 = Ctx(w, A2)
        gv = c2([c2([c2([], 'simpr', 'j = %s' % eqj)], 'fveq2d', '%s = ( G ` %s )' % (CHN('j'), eqj)), lift(w, gval, A2)], 'eqtrd', '%s = %s' % (CHN('j'), val))
        gd = c2([lift(w, gx, A2), w.inst(sel)], 'syl', GOOD(PTL('x', val), LFN, LN4))
        nz_ = c2([gd, w.inst('simpl')], 'syl', '( %s ` %s ) =/= 0' % (LFN, PTL('x', val)))
        e = c2([c2([c2([gv], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (CHN('j'), val))], 'oveq2d', '%s = %s' % (PTL('x', CHN('j')), PTL('x', val)))], 'fveq2d', '( %s ` %s ) = ( %s ` %s )' % (LFN, PTL('x', CHN('j')), LFN, PTL('x', val)))
        return c2([nz_, c2([e], 'neeq1d', '( %s <-> ( %s ` %s ) =/= 0 )' % (TGT, LFN, PTL('x', val)))], 'mpbird', TGT)
    k0 = endcase('0', '-u U', 'simpl', g0)
    kK = endcase('K', 'V', 'simpr', gk)
    # interior
    Ai = '( ( %s /\\ j =/= 0 ) /\\ j =/= K )' % Ax
    ci = Ctx(w, Ai)
    Li = lambda st: lift(w, st, Ai)
    jz = ci([Li(jin), w.inst('elfzelz')], 'syl', 'j e. ZZ')
    jr = ci([jz], 'zred', 'j e. RR')
    j0 = ci([Li(jin), w.inst('elfzle1')], 'syl', '0 <_ j')
    jk = ci([Li(jin), w.inst('elfzle2')], 'syl', 'j <_ K')
    jne0 = w.s([w.s([], 'simpr', '( ( %s /\\ j =/= 0 ) -> j =/= 0 )' % Ax)], 'adantr', '( %s -> j =/= 0 )' % Ai)
    jnek = ci([], 'simpr', 'j =/= K')
    jp = ci([ci([j0, jne0], 'jca', '( 0 <_ j /\\ j =/= 0 )'), ci([numst(w, Ai, '0', 'RR'), jr], 'ltlend', '( 0 < j <-> ( 0 <_ j /\\ j =/= 0 ) )')], 'mpbird', '0 < j')
    j1 = ci([jp, ci([jz, w.inst('zgt0ge1')], 'syl', '( 0 < j <-> 1 <_ j )')], 'mpbid', '1 <_ j')
    kz = ci([Li(kn)], 'nnzd', 'K e. ZZ')
    jlk = ci([ci([jk, ci([jnek], 'necomd', 'K =/= j')], 'jca', '( j <_ K /\\ K =/= j )'), ci([jr, ci([kz], 'zred', 'K e. RR')], 'ltlend', '( j < K <-> ( j <_ K /\\ K =/= j ) )')], 'mpbird', 'j < K')
    jo = ci([ci([j1, jlk], 'jca', '( 1 <_ j /\\ j < K )'), ci([jz, ci.a1(w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), kz, w.inst('elfzo')], 'syl3anc', '( j e. ( 1 ..^ K ) <-> ( 1 <_ j /\\ j < K ) )')], 'mpbird', 'j e. ( 1 ..^ K )')
    nav, _ = ral_at(w, Ai, Li(avo), 'e', 'j', '-. ( G ` e ) e. ( Im " %s )' % BZ4, jo)
    rj, _ = ral_at(w, Ai, Li(rng), 'e', 'j', '( -u U <_ ( G ` e ) /\\ ( G ` e ) <_ V )', Li(jin))
    rj1, rj2 = conj_split(w, Ai, rj)
    Az = '( %s /\\ ( %s ` %s ) = 0 )' % (Ai, LFN, PTL('x', CHN('j')))
    cz = Ctx(w, Az)
    Lz = lambda st: lift(w, st, Az)
    lvz = {k: Lz(v) for k, v in lvx.items()}
    hz = [Lz(Li(sx)), Lz(Li(xc1)), Lz(Li(L(s916))), Lz(Li(L(f['c54']))), Lz(rj1), Lz(rj2), Lz(Li(L(u1))), Lz(Li(L(v1))), Lz(Li(L(t2)))]
    zb, zc = in_bz(Az, 'x', CHN('j'), Lz(Li(xr)), Lz(Li(gj)), cz([], 'simpr', '( %s ` %s ) = 0' % (LFN, PTL('x', CHN('j')))), hz, lvz)
    zim = image(Az, 'Im', PTL('x', CHN('j')), zb, zc)
    gim = cz([cz([cz([Lz(Li(xr)), Lz(Li(gj)), w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (PTL('x', CHN('j')), CHN('j')))], 'eqcomd', '%s = ( Im ` %s )' % (CHN('j'), PTL('x', CHN('j')))), zim], 'eqeltrd',
             '%s e. ( Im " %s )' % (CHN('j'), BZ4))
    ki = ci([gim, lift(w, nav, Az)], 'pm2.65da', '-. ( %s ` %s ) = 0' % (LFN, PTL('x', CHN('j'))))
    ki2 = ci([ki], 'neqned', TGT)
    Ab = '( %s /\\ j =/= 0 )' % Ax
    cb = Ctx(w, Ab)
    kb = cb([w.s([kK], 'adantlr', '( ( %s /\\ j = K ) -> %s )' % (Ab, TGT)), ki2, cb.a1(w.s([], 'exmidne', '( j = K \\/ j =/= K )'), '( j = K \\/ j =/= K )')], 'mpjaodan', TGT)
    ka = cx([k0, kb, cx.a1(w.s([], 'exmidne', '( j = 0 \\/ j =/= 0 )'), '( j = 0 \\/ j =/= 0 )')], 'mpjaodan', TGT)
    alx = w.s([ka], 'ralrimiva', '( %s -> A. x e. ( S [,] %s ) %s )' % (Aj, C1, TGT))
    alj = c([alx], 'ralrimiva', 'A. j e. ( 0 ... K ) A. x e. ( S [,] %s ) %s' % (C1, TGT))
    # left edge
    At = '( %s /\\ t e. ( -u U [,] ( T + 2 ) ) )' % A0
    ct = Ctx(w, At)
    Lt = lambda st: lift(w, st, At)
    tin = ct([], 'simpr', 't e. ( -u U [,] ( T + 2 ) )')
    t2r = ct([Lt(tr), numst(w, At, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')
    ttr, tlo, thi = icc_out(ct, 't', '-u U', '( T + 2 )', tin, ct([Lt(ur)], 'renegcld', '-u U e. RR'), t2r)
    TL = '( %s ` %s ) =/= 0' % (LFN, PTL('S', 't'))
    Az2 = '( %s /\\ ( %s ` %s ) = 0 )' % (At, LFN, PTL('S', 't'))
    cz2 = Ctx(w, Az2)
    L2 = lambda st: lift(w, st, Az2)
    lv2 = {'S': L2(Lt(sr)), 't': L2(ttr), 'T': L2(Lt(tr)), 'U': L2(Lt(ur))}
    zb2, zc2 = in_bz(Az2, 'S', 't', L2(Lt(sr)), L2(ttr), cz2([], 'simpr', '( %s ` %s ) = 0' % (LFN, PTL('S', 't'))), [L2(Lt(s916)), L2(Lt(s58)), L2(tlo), L2(thi), L2(Lt(u1)), L2(Lt(t2))], lv2)
    zre = image(Az2, 'Re', PTL('S', 't'), zb2, zc2)
    sre = cz2([cz2([cz2([L2(Lt(sr)), L2(ttr), w.inst('crre')], 'syl2anc', '( Re ` %s ) = S' % PTL('S', 't'))], 'eqcomd', 'S = ( Re ` %s )' % PTL('S', 't')), zre], 'eqeltrd', 'S e. ( Re " %s )' % BZ4)
    nl = ct([sre, lift(w, nsb, Az2)], 'pm2.65da', '-. ( %s ` %s ) = 0' % (LFN, PTL('S', 't')))
    alt = c([ct([nl], 'neqned', TL)], 'ralrimiva', 'A. t e. ( -u U [,] ( T + 2 ) ) %s' % TL)
    w.qed([alj, alt], 'jca', S['ef4ln'])
    return run8(w)



def gen_nm():
    w = W('ef4nm', 'The numerics of Lean ` contour_ne_one ` ( ` hb1 ` - ` hb4 ` , ` htotal ` ): the edge bounds ( two horizontal edges, two right extras, the left edge) and the zero-sum bound add up to at most ` 2 pi 400000000 ( y log ^ 2 ( N T y ) / T + y ^ ( 5 / 8 ) log ^ 2 ( N ( T + 2 ) ) ) ` .')
    A0, G = ante_of(S['ef4nm'])
    c = Ctx(w, A0)
    g = c.g
    chi = g(CHI); yr = g('Y e. RR'); y100 = g('; ; 1 0 0 <_ Y'); tr = g('T e. RR'); t2 = g('2 <_ T')
    sr = g('S e. RR'); s58 = g('S <_ ( 5 / 8 )')
    ar = g('A e. RR'); br = g('B e. RR'); ale = g('A <_ %s' % EDGE); ble = g('B <_ %s' % ZB)
    nn = c([c([chi, w.inst('simpl')], 'syl', NX), w.inst('simpl')], 'syl', 'N e. NN')
    nr = c([nn], 'nnred', 'N e. RR'); n1 = c([nn], 'nnge1d', '1 <_ N')
    f = c1_facts(w, c, yr, y100)
    L_ = '( log ` Y )'
    tp = c([tr, lin8(w, A0, [t2], '0 < T', {'T': tr})], 'elrpd', 'T e. RR+')
    cl = Closure(w, A0, {'N': ('NN', nn), 'T': ('RR+', tp), 'Y': ('RR+', f['yp']), 'S': ('RR', sr), L_: ('RR+', f['lp'])})
    R = lambda e: cl.mem(e, 'RR')
    lv = {'N': nr, 'T': tr, 'Y': yr}
    # logs
    N4, N2 = '( N x. ( T + 4 ) )', '( N x. ( T + 2 ) )'
    NTY = '( ( N x. T ) x. Y )'
    ln4r, lntr, lnyr, lr = R(LN4), R(LNT), R(LNY), R(L_)
    n4g = lin8(w, A0, [n1, t2], '1 <_ %s' % N4, lv, products=True)
    ln40 = c([c([R(N4), n4g], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (N4, N4)), w.inst('logge0')], 'syl', '0 <_ %s' % LN4)
    n2g = lin8(w, A0, [n1, t2], '1 <_ %s' % N2, lv, products=True)
    lnt0 = c([c([R(N2), n2g], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (N2, N2)), w.inst('logge0')], 'syl', '0 <_ %s' % LNT)
    TY = '( T x. Y )'
    ty = lin8(w, A0, [t2, y100], '( T + 4 ) <_ %s' % TY, lv, products=True)
    ntyl = c([R('( T + 4 )'), R(TY), nr, lin8(w, A0, [n1], '0 <_ N', lv), ty], 'lemul2ad', '%s <_ ( N x. %s )' % (N4, TY))
    ma = c([c([nr], 'recnd', 'N e. CC'), c([tr], 'recnd', 'T e. CC'), c([yr], 'recnd', 'Y e. CC')], 'mulassd', '%s = ( N x. %s )' % (NTY, TY))
    le4y = c([ntyl, c([ma], 'eqcomd', '( N x. %s ) = %s' % (TY, NTY))], 'breqtrd', '%s <_ %s' % (N4, NTY))
    l4y = c([le4y, c([cl.mem(N4, 'RR+'), cl.mem(NTY, 'RR+'), w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> %s <_ %s )' % (N4, NTY, LN4, LNY))], 'mpbid', '%s <_ %s' % (LN4, LNY))
    T2S = '( ( T + 2 ) ^ 2 )'
    t42 = lin8(w, A0, [t2], '( T + 4 ) <_ %s' % T2S, lv, products=True)
    a1 = c([R('( T + 4 )'), R(T2S), nr, lin8(w, A0, [n1], '0 <_ N', lv), t42], 'lemul2ad', '%s <_ ( N x. %s )' % (N4, T2S))
    nnn = lin8(w, A0, [n1], 'N <_ ( N x. N )', lv, products=True)
    a2 = c([nr, R('( N x. N )'), R(T2S), c([R('( T + 2 )')], 'sqge0d', '0 <_ %s' % T2S), nnn], 'lemul1ad', '( N x. %s ) <_ ( ( N x. N ) x. %s )' % (T2S, T2S))
    cln = Closure(w, A0, {'N': ('RR', nr), 'T': ('RR', tr)}); cln.atom('N'); cln.atom('T')
    ncc, t2c = c([nr], 'recnd', 'N e. CC'), c([R('( T + 2 )')], 'recnd', '( T + 2 ) e. CC')
    e_1 = c([ncc, t2c], 'sqmuld', '( %s ^ 2 ) = ( ( N ^ 2 ) x. %s )' % (N2, T2S))
    e_2 = c([c([ncc], 'sqvald', '( N ^ 2 ) = ( N x. N )')], 'oveq1d', '( ( N ^ 2 ) x. %s ) = ( ( N x. N ) x. %s )' % (T2S, T2S))
    a3 = c([c([e_1, e_2], 'eqtrd', '( %s ^ 2 ) = ( ( N x. N ) x. %s )' % (N2, T2S))], 'eqcomd', '( ( N x. N ) x. %s ) = ( %s ^ 2 )' % (T2S, N2))
    le42 = le_tr(w, A0, a1, N4, '( N x. %s )' % T2S, c([a2, a3], 'breqtrd', '( N x. %s ) <_ ( %s ^ 2 )' % (T2S, N2)), '( %s ^ 2 )' % N2)
    lg2 = c([le42, c([cl.mem(N4, 'RR+'), cl.mem('( %s ^ 2 )' % N2, 'RR+'), w.inst('logleb')], 'syl2anc', '( %s <_ ( %s ^ 2 ) <-> %s <_ ( log ` ( %s ^ 2 ) ) )' % (N4, N2, LN4, N2))], 'mpbid', '%s <_ ( log ` ( %s ^ 2 ) )' % (LN4, N2))
    rex = c([cl.mem(N2, 'RR+'), c.a1(w.s([], '2z', '2 e. ZZ'), '2 e. ZZ'), w.inst('relogexp')], 'syl2anc', '( log ` ( %s ^ 2 ) ) = ( 2 x. %s )' % (N2, LNT))
    l42 = c([lg2, rex], 'breqtrd', '%s <_ ( 2 x. %s )' % (LN4, LNT))
    nt1 = lin8(w, A0, [n1, t2], '1 <_ ( N x. T )', lv, products=True)
    y1n = c([numst(w, A0, '1', 'RR'), R('( N x. T )'), yr, lin8(w, A0, [y100], '0 <_ Y', lv), nt1], 'lemul1ad', '( 1 x. Y ) <_ %s' % NTY)
    yle = c([c([c([c([yr], 'recnd', 'Y e. CC')], 'mullidd', '( 1 x. Y ) = Y')], 'eqcomd', 'Y = ( 1 x. Y )'), y1n], 'eqbrtrd', 'Y <_ %s' % NTY)
    ly = c([yle, c([f['yp'], cl.mem(NTY, 'RR+'), w.inst('logleb')], 'syl2anc', '( Y <_ %s <-> %s <_ %s )' % (NTY, L_, LNY))], 'mpbid', '%s <_ %s' % (L_, LNY))
    lvl = {LN4: ln4r, LNT: lntr, LNY: lnyr, L_: lr}
    lny1 = lin8(w, A0, [f['l4'], ly], '1 <_ %s' % LNY, lvl)
    # squares
    sq_a = c([c([ln4r, ln40], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (LN4, LN4)), c([lnyr, l4y], 'jca', '( %s e. RR /\\ %s <_ %s )' % (LNY, LN4, LNY)), w.inst('le2sq2')], 'syl2anc', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LN4, LNY))
    sq_b0 = c([c([ln4r, ln40], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (LN4, LN4)), c([R('( 2 x. %s )' % LNT), l42], 'jca', '( ( 2 x. %s ) e. RR /\\ %s <_ ( 2 x. %s ) )' % (LNT, LN4, LNT)), w.inst('le2sq2')], 'syl2anc',
              '( %s ^ 2 ) <_ ( ( 2 x. %s ) ^ 2 )' % (LN4, LNT))
    cll = Closure(w, A0, {LNT: ('RR', lntr)}); cll.atom(LNT)
    s2e = c([c([numst(w, A0, '2', 'CC'), c([lntr], 'recnd', '%s e. CC' % LNT)], 'sqmuld', '( ( 2 x. %s ) ^ 2 ) = ( ( 2 ^ 2 ) x. ( %s ^ 2 ) )' % (LNT, LNT)),
             c([c.a1(w.s([], 'sq2', '( 2 ^ 2 ) = 4'), '( 2 ^ 2 ) = 4')], 'oveq1d', '( ( 2 ^ 2 ) x. ( %s ^ 2 ) ) = ( 4 x. ( %s ^ 2 ) )' % (LNT, LNT))], 'eqtrd', '( ( 2 x. %s ) ^ 2 ) = ( 4 x. ( %s ^ 2 ) )' % (LNT, LNT))
    sq_b = c([sq_b0, s2e], 'breqtrd', '( %s ^ 2 ) <_ ( 4 x. ( %s ^ 2 ) )' % (LN4, LNT))
    lsq = c([lnyr], 'resqcld', '( %s ^ 2 ) e. RR' % LNY)
    lvs = dict(lvl); lvs['( %s ^ 2 )' % LNY] = lsq
    yy = lin8(w, A0, [lny1], '%s <_ ( %s ^ 2 )' % (LNY, LNY), {LNY: lnyr}, products=True)
    sq_c = lin8(w, A0, [ly, yy], '%s <_ ( %s ^ 2 )' % (L_, LNY), lvs)
    sq_d = lin8(w, A0, [l4y, yy], '%s <_ ( %s ^ 2 )' % (LN4, LNY), lvs)
    YS, Y58, YC = '( Y ^c S )', '( Y ^c ( 5 / 8 ) )', '( Y ^c %s )' % C1
    ys = c([s58, c([yr, f['y1'], sr, numst(w, A0, '( 5 / 8 )', 'RR')], 'cxpled', '( S <_ ( 5 / 8 ) <-> %s <_ %s )' % (YS, Y58))], 'mpbid', '%s <_ %s' % (YS, Y58))
    yc3 = c([c([c([yr, f['y1']], 'jca', '( Y e. RR /\\ 1 < Y )'), w.inst('ef1yc')], 'syl', ante_of(stmt('ef1yc'))[1]), w.inst('simpr')], 'syl', '%s <_ ( 3 x. Y )' % YC)
    # the edges
    IT = '( 1 / T )'
    YIT = '( Y x. %s )' % IT
    itp = c([tp], 'rpreccld', '%s e. RR+' % IT)
    yit0 = c([yr, R(IT), lin8(w, A0, [y100], '0 <_ Y', lv), c([itp], 'rpge0d', '0 <_ %s' % IT)], 'mulge0d', '0 <_ %s' % YIT)
    divr = lambda X: c([c([R(X)], 'recnd', '%s e. CC' % X), c([tp], 'rpcnd', 'T e. CC'), c([tp], 'rpne0d', 'T =/= 0')], 'divrecd', '( %s / T ) = ( %s x. %s )' % (X, X, IT))
    catoms = {LN4: ln4r, LNT: lntr, LNY: lnyr, L_: lr, IT: R(IT), 'Y': yr, YS: R(YS), Y58: R(Y58), YC: R(YC)}
    CA = Closure(w, A0, {k: ('RR', v) for k, v in catoms.items()})
    for k in catoms:
        CA.atom(k)
    P1b = '( ( %s ^ 2 ) x. %s )' % (LNY, YIT)
    p1e = c([divr('( Y x. ( %s ^ 2 ) )' % LNY), ringeq(w, A0, '( ( Y x. ( %s ^ 2 ) ) x. %s )' % (LNY, IT), P1b, CA)], 'eqtrd', '%s = %s' % (P1, P1b))
    K2 = '( %s x. ( %s ^ 2 ) )' % (KGH, LN4)
    k2r = R(K2)
    k20 = c([numst(w, A0, KGH, 'RR'), R('( %s ^ 2 )' % LN4), lin8(w, A0, [], '0 <_ %s' % KGH, {}), c([ln4r], 'sqge0d', '0 <_ ( %s ^ 2 )' % LN4)], 'mulge0d', '0 <_ %s' % K2)
    kt0 = c([k2r, tp, k20], 'divge0d', '0 <_ ( %s / T )' % K2)
    ycp = c([f['yp'], f['c1r']], 'rpcxpcld', '%s e. RR+' % YC)
    h1 = c([numst(w, A0, '4', 'RR+'), f['lp'], R(YC), c([ycp], 'rpge0d', '0 <_ %s' % YC), f['l4']], 'lediv2ad', '( %s / %s ) <_ ( %s / 4 )' % (YC, L_, YC))
    h2 = c([R(YC), R('( 3 x. Y )'), numst(w, A0, '4', 'RR+'), yc3], 'lediv1dd', '( %s / 4 ) <_ ( ( 3 x. Y ) / 4 )' % YC)
    h3 = le_tr(w, A0, h1, '( %s / %s )' % (YC, L_), '( %s / 4 )' % YC, h2, '( ( 3 x. Y ) / 4 )')
    h4 = c([R('( %s / %s )' % (YC, L_)), R('( ( 3 x. Y ) / 4 )'), R('( %s / T )' % K2), kt0, h3], 'lemul2ad', '%s <_ ( ( %s / T ) x. ( ( 3 x. Y ) / 4 ) )' % (HB, K2))
    HBb = '( ( %s / T ) x. ( ( 3 x. Y ) / 4 ) )' % K2
    h5 = c([c([divr(K2)], 'oveq1d', '%s = ( ( %s x. %s ) x. ( ( 3 x. Y ) / 4 ) )' % (HBb, K2, IT)), ringeq(w, A0, '( ( %s x. %s ) x. ( ( 3 x. Y ) / 4 ) )' % (K2, IT), '( ; ; ; ; ; ; ; 1 5 7 5 0 0 0 0 x. ( ( %s ^ 2 ) x. %s ) )' % (LN4, YIT), CA)], 'eqtrd',
            '%s = ( ; ; ; ; ; ; ; 1 5 7 5 0 0 0 0 x. ( ( %s ^ 2 ) x. %s ) )' % (HBb, LN4, YIT))
    q4 = c([R('( %s ^ 2 )' % LN4), R('( %s ^ 2 )' % LNY), R(YIT), yit0, sq_a], 'lemul1ad', '( ( %s ^ 2 ) x. %s ) <_ %s' % (LN4, YIT, P1b))
    RBb = '( 8 x. ( %s x. %s ) )' % (L_, YIT)
    r1 = c([c([divr('( Y x. %s )' % L_)], 'oveq2d', '%s = ( 8 x. ( ( Y x. %s ) x. %s ) )' % (RB, L_, IT)), ringeq(w, A0, '( 8 x. ( ( Y x. %s ) x. %s ) )' % (L_, IT), RBb, CA)], 'eqtrd', '%s = %s' % (RB, RBb))
    r2 = c([lr, R('( %s ^ 2 )' % LNY), R(YIT), yit0, sq_c], 'lemul1ad', '( %s x. %s ) <_ %s' % (L_, YIT, P1b))
    lb1 = c([R(YS), R(Y58), R('( %s ^ 2 )' % LN4), R('( 4 x. ( %s ^ 2 ) )' % LNT), c([c([f['yp'], sr], 'rpcxpcld', '%s e. RR+' % YS)], 'rpge0d', '0 <_ %s' % YS),
             c([ln4r], 'sqge0d', '0 <_ ( %s ^ 2 )' % LN4), ys, sq_b], 'lemul12ad', '( %s x. ( %s ^ 2 ) ) <_ ( %s x. ( 4 x. ( %s ^ 2 ) ) )' % (YS, LN4, Y58, LNT))
    z2e = c([c([divr(LN4)], 'oveq2d', '( ( %s x. Y ) x. ( %s / T ) ) = ( ( %s x. Y ) x. ( %s x. %s ) )' % (KB, LN4, KB, LN4, IT)), ringeq(w, A0, '( ( %s x. Y ) x. ( %s x. %s ) )' % (KB, LN4, IT), '( %s x. ( %s x. %s ) )' % (KB, LN4, YIT), CA)], 'eqtrd',
            '( ( %s x. Y ) x. ( %s / T ) ) = ( %s x. ( %s x. %s ) )' % (KB, LN4, KB, LN4, YIT))
    z2 = c([ln4r, R('( %s ^ 2 )' % LNY), R(YIT), yit0, sq_d], 'lemul1ad', '( %s x. %s ) <_ %s' % (LN4, YIT, P1b))
    z1 = c([R(YS), R(Y58), R('( %s ^ 2 )' % LNT), c([lntr], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNT), ys], 'lemul1ad', '( %s x. ( %s ^ 2 ) ) <_ ( %s x. ( %s ^ 2 ) )' % (YS, LNT, Y58, LNT))
    # linear combination: A <_ 2040000000 Q, B <_ 73600 Q
    Q = '( %s + %s )' % (P1, P2)
    atoms = {HB: R(HB), RB: R(RB), LB: R(LB), P1: R(P1), P2: R(P2), P1b: R(P1b), 'A': ar, 'B': br, YS: R(YS), Y58: R(Y58), LNT: lntr, LN4: ln4r, YIT: R(YIT), L_: lr,
             '( ( %s ^ 2 ) x. %s )' % (LN4, YIT): R('( ( %s ^ 2 ) x. %s )' % (LN4, YIT)), '( %s x. %s )' % (L_, YIT): R('( %s x. %s )' % (L_, YIT)), '( %s x. %s )' % (LN4, YIT): R('( %s x. %s )' % (LN4, YIT)),
             '( %s x. ( %s ^ 2 ) )' % (YS, LN4): R('( %s x. ( %s ^ 2 ) )' % (YS, LN4)), '( %s x. ( %s ^ 2 ) )' % (YS, LNT): R('( %s x. ( %s ^ 2 ) )' % (YS, LNT)),
             '( %s x. ( %s ^ 2 ) )' % (Y58, LNT): R('( %s x. ( %s ^ 2 ) )' % (Y58, LNT))}
    p10 = c([R('( Y x. ( %s ^ 2 ) )' % LNY), tp, c([yr, R('( %s ^ 2 )' % LNY), lin8(w, A0, [y100], '0 <_ Y', lv), c([lnyr], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNY)], 'mulge0d', '0 <_ ( Y x. ( %s ^ 2 ) )' % LNY)], 'divge0d', '0 <_ %s' % P1)
    p20 = c([R(Y58), R('( %s ^ 2 )' % LNT), c([c([f['yp'], numst(w, A0, '( 5 / 8 )', 'RR')], 'rpcxpcld', '%s e. RR+' % Y58)], 'rpge0d', '0 <_ %s' % Y58), c([lntr], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNT)], 'mulge0d', '0 <_ %s' % P2)
    lb2 = c([numst(w, A0, KL, 'CC'), c([R(YS)], 'recnd', '%s e. CC' % YS), c([R('( %s ^ 2 )' % LN4)], 'recnd', '( %s ^ 2 ) e. CC' % LN4)], 'mulassd', '%s = ( %s x. ( %s x. ( %s ^ 2 ) ) )' % (LB, KL, YS, LN4))
    p2e = ringeq(w, A0, '( %s x. ( 4 x. ( %s ^ 2 ) ) )' % (Y58, LNT), '( 4 x. %s )' % P2, CA)
    z1e = c([numst(w, A0, '; ; ; ; 7 2 0 0 0', 'CC'), c([R(YS)], 'recnd', '%s e. CC' % YS), c([R('( %s ^ 2 )' % LNT)], 'recnd', '( %s ^ 2 ) e. CC' % LNT)], 'mulassd',
             '( ( ; ; ; ; 7 2 0 0 0 x. %s ) x. ( %s ^ 2 ) ) = ( ; ; ; ; 7 2 0 0 0 x. ( %s x. ( %s ^ 2 ) ) )' % (YS, LNT, YS, LNT))
    lvq = dict(atoms)
    lvq['( %s / T )' % LN4] = R('( %s / T )' % LN4)
    lvq['Y'] = yr
    hyps_a = [ale, h4, h5, q4, r1, r2, lb2, lb1, p2e, p1e, p10, p20]
    ea = lin8(w, A0, hyps_a, 'A <_ ( ; ; ; ; ; ; ; ; ; 2 0 4 0 0 0 0 0 0 0 x. %s )' % Q, dict(lvq, **{HBb: R(HBb), '( ( %s ^ 2 ) x. %s )' % (LN4, YIT): R('( ( %s ^ 2 ) x. %s )' % (LN4, YIT))}))
    eb = lin8(w, A0, [ble, z1e, z1, z2e, z2, p1e, p10, p20], 'B <_ ( ; ; ; ; 7 3 6 0 0 x. %s )' % Q, lvq)
    # with pi
    PI2 = '( 2 x. _pi )'
    pi2r = c.a1(w.s([w.s([], '2re', '2 e. RR'), w.s([], 'pire', '_pi e. RR')], 'remulcli', '%s e. RR' % PI2), '%s e. RR' % PI2)
    pi6 = lin8(w, A0, [c.a1(w.s([], 'pigt3', '3 < _pi'), '3 < _pi')], '6 <_ %s' % PI2, {'_pi': c.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR')})
    pi0 = lin8(w, A0, [pi6], '0 <_ %s' % PI2, {PI2: pi2r})
    qr = R(Q)
    q0 = lin8(w, A0, [p10, p20], '0 <_ %s' % Q, {P1: R(P1), P2: R(P2)})
    X1 = '( ; ; ; ; ; ; ; ; 3 4 0 0 0 0 0 0 0 x. %s )' % Q
    x10 = c([numst(w, A0, '; ; ; ; ; ; ; ; 3 4 0 0 0 0 0 0 0', 'RR'), qr, lin8(w, A0, [], '0 <_ ; ; ; ; ; ; ; ; 3 4 0 0 0 0 0 0 0', {}), q0], 'mulge0d', '0 <_ %s' % X1)
    e6 = c([numst(w, A0, '6', 'RR'), pi2r, R(X1), x10, pi6], 'lemul1ad', '( 6 x. %s ) <_ ( %s x. %s )' % (X1, PI2, X1))
    cq = Closure(w, A0, {Q: ('RR', qr)}); cq.atom(Q)
    e6b = c([ringeq(w, A0, '( ; ; ; ; ; ; ; ; ; 2 0 4 0 0 0 0 0 0 0 x. %s )' % Q, '( 6 x. %s )' % X1, cq), e6], 'eqbrtrd', '( ; ; ; ; ; ; ; ; ; 2 0 4 0 0 0 0 0 0 0 x. %s ) <_ ( %s x. %s )' % (Q, PI2, X1))
    fa = le_tr(w, A0, ea, 'A', '( ; ; ; ; ; ; ; ; ; 2 0 4 0 0 0 0 0 0 0 x. %s )' % Q, e6b, '( %s x. %s )' % (PI2, X1))
    X2 = '( ; ; ; ; 7 3 6 0 0 x. %s )' % Q
    fb = c([br, R(X2), pi2r, pi0, eb], 'lemul2ad', '( %s x. B ) <_ ( %s x. %s )' % (PI2, PI2, X2))
    sm = c([fa, fb], 'le2addd', '( A + ( %s x. B ) ) <_ ( ( %s x. %s ) + ( %s x. %s ) )' % (PI2, PI2, X1, PI2, X2))
    ad = c([c([pi2r], 'recnd', '%s e. CC' % PI2), c([R(X1)], 'recnd', '%s e. CC' % X1), c([R(X2)], 'recnd', '%s e. CC' % X2)], 'adddid', '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) + ( %s x. %s ) )' % (PI2, X1, X2, PI2, X1, PI2, X2))
    X12 = '( %s + %s )' % (X1, X2)
    KQ = '( %s x. %s )' % (KC, Q)
    kq = lin8(w, A0, [q0], '%s <_ %s' % (X12, KQ), {Q: qr})
    fk = c([R(X12), R(KQ), pi2r, pi0, kq], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (PI2, X12, PI2, KQ))
    fin = le_tr(w, A0, c([sm, c([ad], 'eqcomd', '( ( %s x. %s ) + ( %s x. %s ) ) = ( %s x. %s )' % (PI2, X1, PI2, X2, PI2, X12))], 'breqtrd', '( A + ( %s x. B ) ) <_ ( %s x. %s )' % (PI2, PI2, X12)),
                '( A + ( %s x. B ) )' % PI2, '( %s x. %s )' % (PI2, X12), fk, '( %s x. %s )' % (PI2, KQ))
    w.qed([fin], 'idi', S['ef4nm'])
    return run8(w)



def gen_core():
    w = W('ef4core', 'Lean ` contour_ne_one ` for chosen heights ` - U ` , ` V ` , abscissa ` S ` and cuts ` G ` : ` abs ( PS + 2 pi i SC ) <_ 2 pi 400000000 ( P1 + P2 ) ` ( ~ ef4id , ~ ef4zs , ~ ef4hed , ~ ef4rx , ~ ef3left , ~ ef4nm ).')
    A0, G = ante_of(S['ef4core'])
    c = Ctx(w, A0)
    g = c.g
    chi = g(CHI); yr = g('Y e. RR'); y100 = g('; ; 1 0 0 <_ Y'); tr = g('T e. RR'); t2 = g('2 <_ T')
    ur = g('U e. RR'); vr = g('V e. RR'); tu = g('T <_ U'); u1 = g('U <_ ( T + 1 )'); tv = g('T <_ V'); v1 = g('V <_ ( T + 1 )')
    sr = g('S e. RR'); s916 = g('( 9 / ; 1 6 ) <_ S'); s58 = g('S <_ ( 5 / 8 )')
    hgd = g(HGD)
    mn0 = g('M e. NN0'); vm = g('V <_ ( -u U + ( M / 2 ) )'); mt = g('( -u U + ( M / 2 ) ) <_ ( T + 2 )')
    f = c1_facts(w, c, yr, y100)
    lv = {'T': tr, 'U': ur, 'V': vr, 'S': sr, C1: f['c1r']}
    dd = c([chi, w.inst('ef2ddl')], 'syl', DD(LFN, 'N'))
    hol = c([dd, w.inst('simp1')], 'syl', HOLF(LFN, HP0))
    nur = c([ur], 'renegcld', '-u U e. RR')
    # 1. nonvanishing on the contour
    AV1 = 'A. j e. ( 1 ..^ K ) -. ( G ` j ) e. ( Im " %s )' % BZ4
    AV0 = 'A. j e. ( 0 ... K ) ( -u U <_ ( G ` j ) /\\ ( G ` j ) <_ V )'
    cb1, bb1 = cbvral(w, '( 1 ..^ K )', 'j', 'e', '-. ( G ` j ) e. ( Im " %s )' % BZ4)
    cb0, bb0 = cbvral(w, '( 0 ... K )', 'j', 'e', '( -u U <_ ( G ` j ) /\\ ( G ` j ) <_ V )')
    e1 = c([g(AV1), c.a1(cb1, '( %s <-> A. e e. ( 1 ..^ K ) %s )' % (AV1, bb1))], 'mpbid', 'A. e e. ( 1 ..^ K ) %s' % bb1)
    e0 = c([g(AV0), c.a1(cb0, '( %s <-> A. e e. ( 0 ... K ) %s )' % (AV0, bb0))], 'mpbid', 'A. e e. ( 0 ... K ) %s' % bb0)
    lna = ante_of(stmt('ef4ln'))[0]
    ln = c([rebuild(w, c, lna, {'A. e e. ( 1 ..^ K ) %s' % bb1: e1, 'A. e e. ( 0 ... K ) %s' % bb0: e0}), w.inst('ef4ln')], 'syl', ante_of(stmt('ef4ln'))[1])
    lines, left2 = conj_split(w, A0, ln)
    TL = '( %s ` %s ) =/= 0' % (LFN, PTL('S', 't'))
    t2r = c([tr, numst(w, A0, '2', 'RR')], 'readdcld', '( T + 2 ) e. RR')
    def left_on(hi, hir, hle):
        ss = c([c([nur, t2r], 'jca', '( -u U e. RR /\\ ( T + 2 ) e. RR )'), c([c([nur], 'leidd', '-u U <_ -u U'), hle], 'jca', '( -u U <_ -u U /\\ %s <_ ( T + 2 ) )' % hi), w.inst('iccss')], 'syl2anc',
               '( -u U [,] %s ) C_ ( -u U [,] ( T + 2 ) )' % hi)
        return c([left2, c([ss, w.inst('ssralv')], 'syl', '( A. t e. ( -u U [,] ( T + 2 ) ) %s -> A. t e. ( -u U [,] %s ) %s )' % (TL, hi, TL))], 'mpd', 'A. t e. ( -u U [,] %s ) %s' % (hi, TL))
    leftV = left_on('V', vr, lin8(w, A0, [v1], 'V <_ ( T + 2 )', lv))
    PM = '( -u U + ( M / 2 ) )'
    leftM = left_on(PM, None, mt)
    # 2. the identity
    sc1 = lin8(w, A0, [s58, f['c1g']], 'S < %s' % C1, lv)
    ida = ante_of(stmt('ef4id'))[0]
    idc = ante_of(stmt('ef4id'))[1]
    LXQ = 'A. j e. ( 0 ... K ) A. x e. ( S [,] %s ) ( %s ` %s ) =/= 0' % (C1, LFN, PTL('x', CHN('j')))
    ide = c([rebuild(w, c, ida, {'S < %s' % C1: sc1, LXQ: lines, 'A. t e. ( -u U [,] V ) %s' % TL: leftV}), w.inst('ef4id')], 'syl', idc)
    # 3. zero sums
    NZ2 = 'A. v e. ( ( 1 / 2 ) [,] 3 ) ( ( %s ` %s ) =/= 0 /\\ ( %s ` %s ) =/= 0 )' % (LFN, PTL('v', '-u U'), LFN, PTL('v', 'V'))
    GA, GB = GOOD(PTL('v', '-u U'), LFN, LN4), GOOD(PTL('v', 'V'), LFN, LN4)
    NA, NB = '( %s ` %s ) =/= 0' % (LFN, PTL('v', '-u U')), '( %s ` %s ) =/= 0' % (LFN, PTL('v', 'V'))
    imp = w.s([w.s([], 'simpl', '( %s -> %s )' % (GA, NA)), w.s([], 'simpl', '( %s -> %s )' % (GB, NB))], 'anim12i', '( ( %s /\\ %s ) -> ( %s /\\ %s ) )' % (GA, GB, NA, NB))
    nz2 = c([hgd, w.s([w.s([imp], 'ralimi', '( %s -> %s )' % (HGD, NZ2))], 'a1i', '( %s -> ( %s -> %s ) )' % (A0, HGD, NZ2))], 'mpd', NZ2)
    zsa = ante_of(stmt('ef4zs'))[0]
    zspec = {NZ2: nz2}
    zs = c([rebuild(w, c, zsa, zspec), w.inst('ef4zs')], 'syl', ante_of(stmt('ef4zs'))[1])
    scc = c([rebuild(w, c, zsa, zspec), w.inst('ef4scc')], 'syl', ante_of(stmt('ef4scc'))[1])
    scec, srlc = conj_split(w, A0, scc)
    # 4. the left edge
    LE = tsub(stmt('ef3left'), {'F': LFN, 'A': 'N', 'P': '-u U', 'Q': 'V'})
    lea, lec = ante_of(LE)
    lspec = {DD(LFN, 'N'): dd, '1 < Y': f['y1'], '-u U e. RR': nur, '-u ( T + 1 ) <_ -u U': lin8(w, A0, [u1], '-u ( T + 1 ) <_ -u U', lv), '-u U <_ 0': lin8(w, A0, [tu, t2], '-u U <_ 0', lv),
             '0 <_ %s' % PM: lin8(w, A0, [vm, tv, t2], '0 <_ %s' % PM, dict(lv, M=c([mn0], 'nn0red', 'M e. RR'))), 'A. t e. ( -u U [,] %s ) %s' % (PM, TL): leftM,
             '-u U < V': lin8(w, A0, [tu, tv, t2], '-u U < V', lv), 'V <_ %s' % PM: vm}
    le_ = c([rebuild(w, c, lea, lspec), w.inst('ef3left')], 'syl', lec)
    # 5. horizontal edges
    D0 = '{ v e. %s | ( %s ` v ) =/= 0 }' % (HP0, LFN)
    Ax = '( %s /\\ x e. ( S [,] %s ) )' % (A0, C1)
    cx = Ctx(w, Ax)
    xin = cx([], 'simpr', 'x e. ( S [,] %s )' % C1)
    xr, sx, xc = icc_out(cx, 'x', 'S', C1, xin, lift(w, sr, Ax), lift(w, f['c1r'], Ax))
    lvx = {'x': xr, 'S': lift(w, sr, Ax), C1: lift(w, f['c1r'], Ax)}
    vin = icc_in(cx, 'x', '( 1 / 2 )', '3', xr, numst(w, Ax, '( 1 / 2 )', 'RR'), numst(w, Ax, '3', 'RR'), lin8(w, Ax, [sx, lift(w, s916, Ax)], '( 1 / 2 ) <_ x', lvx), lin8(w, Ax, [xc, lift(w, f['c54'], Ax)], 'x <_ 3', lvx))
    gx, _ = ral_at(w, Ax, lift(w, hgd, Ax), 'v', 'x', '( %s /\\ %s )' % (GA, GB), vin)
    K2 = '( %s x. ( %s ^ 2 ) )' % (KGH, LN4)
    def hedge(H, sel, hr, th):
        gd = cx([gx, w.inst(sel)], 'syl', GOOD(PTL('x', H), LFN, LN4))
        al = c([gd], 'ralrimiva', 'A. x e. ( S [,] %s ) %s' % (C1, GOOD(PTL('x', H), LFN, LN4)))
        HE = tsub(stmt('ef4hed'), {'F': LFN, 'C': C1, 'H': H, 'K': K2})
        hea, hec = ante_of(HE)
        n4p = c([c([c([c([chi, w.inst('simpl')], 'syl', NX), w.inst('simpl')], 'syl', 'N e. NN'), w.inst('nnrpd')], 'syl', 'N e. RR+'), c([c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [t2], '0 < ( T + 4 )', lv)], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( N x. ( T + 4 ) ) e. RR+')
        k2r = c([numst(w, A0, KGH, 'RR'), c([c([n4p], 'relogcld', '%s e. RR' % LN4)], 'resqcld', '( %s ^ 2 ) e. RR' % LN4)], 'remulcld', '%s e. RR' % K2)
        spec = {HOLF(LFN, HP0): hol, '1 < Y': f['y1'], '0 < S': lin8(w, A0, [s916], '0 < S', lv), 'S <_ %s' % C1: lin8(w, A0, [s58, f['c1g']], 'S <_ %s' % C1, lv), '0 < T': lin8(w, A0, [t2], '0 < T', lv),
                '%s e. RR' % H: hr, 'T <_ ( abs ` %s )' % H: th, '%s e. RR' % K2: k2r, '%s e. RR' % C1: f['c1r'], top_and(hea)[2]: al}
        return c([rebuild(w, c, hea, spec), w.inst('ef4hed')], 'syl', hec)
    au = c([c([c([ur], 'recnd', 'U e. CC'), w.inst('absneg')], 'syl', '( abs ` -u U ) = ( abs ` U )'), c([ur, lin8(w, A0, [tu, t2], '0 <_ U', lv)], 'absidd', '( abs ` U ) = U')], 'eqtrd', '( abs ` -u U ) = U')
    thu = c([tu, c([au], 'eqcomd', 'U = ( abs ` -u U )')], 'breqtrd', 'T <_ ( abs ` -u U )')
    thv = c([tv, c([c([vr, lin8(w, A0, [tv, t2], '0 <_ V', lv)], 'absidd', '( abs ` V ) = V')], 'eqcomd', 'V = ( abs ` V )')], 'breqtrd', 'T <_ ( abs ` V )')
    hb = hedge('-u U', 'simpl', nur, thu)
    ht = hedge('V', 'simpr', vr, thv)
    # 6. right extras
    def redge(Ua, Va, uar, var_, ule, vul, farf):
        RX = tsub(stmt('ef4rx'), {'U': Ua, 'V': Va})
        rxa, rxc = ante_of(RX)
        At = '( %s /\\ t e. ( %s [,] %s ) )' % (A0, Ua, Va)
        ct = Ctx(w, At)
        tin = ct([], 'simpr', 't e. ( %s [,] %s )' % (Ua, Va))
        trr, tlo, thi = icc_out(ct, 't', Ua, Va, tin, lift(w, uar, At), lift(w, var_, At))
        far = c([farf(At, ct, trr, tlo, thi)], 'ralrimiva', 'A. t e. ( %s [,] %s ) T <_ ( abs ` t )' % (Ua, Va))
        spec = {'%s e. RR' % Ua: uar, '%s e. RR' % Va: var_, '0 < T': lin8(w, A0, [t2], '0 < T', lv), '%s <_ %s' % (Ua, Va): ule, '( %s - %s ) <_ 1' % (Va, Ua): vul, top_and(rxa)[2]: far}
        return c([rebuild(w, c, rxa, spec), w.inst('ef4rx')], 'syl', rxc)
    ntr = c([tr], 'renegcld', '-u T e. RR')
    def far_neg(At, ct, trr, tlo, thi):
        lvt = {'t': trr, 'T': lift(w, tr, At), 'U': lift(w, ur, At)}
        an = ct([trr, lin8(w, At, [thi, lift(w, t2, At)], 't <_ 0', lvt)], 'absnidd', '( abs ` t ) = -u t')
        return ct([lin8(w, At, [thi], 'T <_ -u t', lvt), ct([an], 'eqcomd', '-u t = ( abs ` t )')], 'breqtrd', 'T <_ ( abs ` t )')
    def far_pos(At, ct, trr, tlo, thi):
        lvt = {'t': trr, 'T': lift(w, tr, At)}
        return ct([tlo, ct([ct([trr, lin8(w, At, [tlo, lift(w, t2, At)], '0 <_ t', lvt)], 'absidd', '( abs ` t ) = t')], 'eqcomd', 't = ( abs ` t )')], 'breqtrd', 'T <_ ( abs ` t )')
    eb = redge('-u U', '-u T', nur, ntr, lin8(w, A0, [tu], '-u U <_ -u T', lv), lin8(w, A0, [u1], '( -u T - -u U ) <_ 1', lv), far_neg)
    et = redge('T', 'V', tr, vr, tv, lin8(w, A0, [v1], '( V - T ) <_ 1', lv), far_pos)
    # 7. closures and the triangle inequality on the identity
    idcc = c([rebuild(w, c, ida, {'S < %s' % C1: sc1, LXQ: lines, 'A. t e. ( -u U [,] V ) %s' % TL: leftV}), w.inst('ef4idc')], 'syl', ante_of(stmt('ef4idc'))[1])
    pa, pb, pc = conj_split(w, A0, idcc)
    botc, topc = conj_split(w, A0, pa)
    ebc, etc_ = conj_split(w, A0, pb)
    leftc, psc = conj_split(w, A0, pc)
    AB = lambda X: '( abs ` %s )' % X
    W1_ = '( ( %s - %s ) + ( %s + %s ) )' % (BOT, TOP, EB, ET)
    X0 = '( %s - %s )' % (W1_, LEFT)
    bt = c([botc, topc], 'subcld', '( %s - %s ) e. CC' % (BOT, TOP))
    ee = c([ebc, etc_], 'addcld', '( %s + %s ) e. CC' % (EB, ET))
    w1c = c([bt, ee], 'addcld', '%s e. CC' % W1_)
    tri1 = c([w1c, leftc, w.inst('abs2dif2')], 'syl2anc', '%s <_ ( %s + %s )' % (AB(X0), AB(W1_), AB(LEFT)))
    tri2_ = c([bt, ee], 'abstrid', '%s <_ ( %s + %s )' % (AB(W1_), AB('( %s - %s )' % (BOT, TOP)), AB('( %s + %s )' % (EB, ET))))
    tri3 = c([botc, topc, w.inst('abs2dif2')], 'syl2anc', '%s <_ ( %s + %s )' % (AB('( %s - %s )' % (BOT, TOP)), AB(BOT), AB(TOP)))
    tri4 = c([ebc, etc_], 'abstrid', '%s <_ ( %s + %s )' % (AB('( %s + %s )' % (EB, ET)), AB(EB), AB(ET)))
    def absr(X, st):
        return c([st], 'abscld', '%s e. RR' % AB(X))
    lvA = {AB(X0): absr(X0, c([w1c, leftc], 'subcld', '%s e. CC' % X0)), AB(W1_): absr(W1_, w1c), AB(LEFT): absr(LEFT, leftc), AB('( %s - %s )' % (BOT, TOP)): absr('( %s - %s )' % (BOT, TOP), bt),
           AB('( %s + %s )' % (EB, ET)): absr('( %s + %s )' % (EB, ET), ee), AB(BOT): absr(BOT, botc), AB(TOP): absr(TOP, topc), AB(EB): absr(EB, ebc), AB(ET): absr(ET, etc_)}
    cl = Closure(w, A0, {'Y': ('RR+', f['yp']), 'T': ('RR+', c([tr, lin8(w, A0, [t2], '0 < T', lv)], 'elrpd', 'T e. RR+')), 'S': ('RR', sr), 'N': ('NN', c([c([chi, w.inst('simpl')], 'syl', NX), w.inst('simpl')], 'syl', 'N e. NN')),
                         '( log ` Y )': ('RR+', f['lp'])})
    for k in (HB, RB, LB):
        lvA[k] = cl.mem(k, 'RR')
    ea = lin8(w, A0, [tri1, tri2_, tri3, tri4, hb, ht, eb, et, le_], '%s <_ %s' % (AB(X0), EDGE), lvA)
    A_ = AB('( %s + ( %s x. %s ) )' % (PS1, TPI, SRL))
    ea2 = c([c([ide], 'fveq2d', '%s = %s' % (A_, AB(X0))), ea], 'eqbrtrd', '%s <_ %s' % (A_, EDGE))
    # 8. the full sum
    SD = '( %s - %s )' % (SCE, SRL)
    sdc = c([scec, srlc], 'subcld', '%s e. CC' % SD)
    tpc = c.a1(w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI), '%s e. CC' % TPI)
    clz = Closure(w, A0, {PS1: ('CC', psc), SCE: ('CC', scec), SRL: ('CC', srlc), TPI: ('CC', tpc)})
    for k in (PS1, SCE, SRL, TPI):
        clz.atom(k)
    L1 = '( %s + ( %s x. %s ) )' % (PS1, TPI, SCE)
    L2 = '( ( %s + ( %s x. %s ) ) + ( %s x. %s ) )' % (PS1, TPI, SRL, TPI, SD)
    eq = ringeq(w, A0, L1, L2, clz)
    l1c = c([psc, c([tpc, srlc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, SRL))], 'addcld', '( %s + ( %s x. %s ) ) e. CC' % (PS1, TPI, SRL))
    tri = c([l1c, c([tpc, sdc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, SD))], 'abstrid', '%s <_ ( %s + %s )' % (AB(L2), A_, AB('( %s x. %s )' % (TPI, SD))))
    PI2 = '( 2 x. _pi )'
    atp = c([c.a1(w.s([], '2cn', '2 e. CC'), '2 e. CC'), c.a1(w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'), '( _i x. _pi ) e. CC')], 'absmuld',
            '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI)
    a2 = c.a1(w.s([w.s([], '0le2', '0 <_ 2'), w.s([w.s([], '2re', '2 e. RR')], 'absidi', '( 0 <_ 2 -> ( abs ` 2 ) = 2 )')], 'ax-mp', '( abs ` 2 ) = 2'), '( abs ` 2 ) = 2')
    aip = c([c([c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )'),
             c([c.a1(w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1'), c.a1(w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], 'pire', '_pi e. RR'), w.s([], 'pipos', '0 < _pi')], 'ltleii', '0 <_ _pi'), w.s([w.s([], 'pire', '_pi e. RR')], 'absidi', '( 0 <_ _pi -> ( abs ` _pi ) = _pi )')], 'ax-mp', '( abs ` _pi ) = _pi'), '( abs ` _pi ) = _pi')],
                'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')
    aip2 = c([aip, c([c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mullidd', '( 1 x. _pi ) = _pi')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = _pi')
    atp2 = c([atp, c([a2, aip2], 'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = %s' % PI2)], 'eqtrd', '( abs ` %s ) = %s' % (TPI, PI2))
    amx = c([c([tpc, sdc], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TPI, SD, TPI, SD)), c([atp2], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, SD, PI2, SD))], 'eqtrd',
            '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, SD, PI2, SD))
    tri2 = c([c([c([eq], 'fveq2d', '%s = %s' % (AB(L1), AB(L2))), tri], 'eqbrtrd', '%s <_ ( %s + %s )' % (AB(L1), A_, AB('( %s x. %s )' % (TPI, SD)))), c([amx], 'oveq2d', '( %s + %s ) = ( %s + ( %s x. %s ) )' % (A_, AB('( %s x. %s )' % (TPI, SD)), A_, PI2, AB(SD)))],
             'breqtrd', '%s <_ ( %s + ( %s x. %s ) )' % (AB(L1), A_, PI2, AB(SD)))
    NM = tsub(stmt('ef4nm'), {'A': A_, 'B': AB(SD)})
    nma, nmc = ante_of(NM)
    nm = c([rebuild(w, c, nma, {'%s e. RR' % A_: c([l1c], 'abscld', '%s e. RR' % A_), '%s e. RR' % AB(SD): c([sdc], 'abscld', '%s e. RR' % AB(SD)), '%s <_ %s' % (A_, EDGE): ea2, '%s <_ %s' % (AB(SD), ZB): zs}),
            w.inst('ef4nm')], 'syl', nmc)
    fin = le_tr(w, A0, tri2, AB(L1), '( %s + ( %s x. %s ) )' % (A_, PI2, AB(SD)), nm, nmc.split(' <_ ', 1)[1])
    w.qed([fin], 'idi', S['ef4core'])
    return run8(w)



def gen_cnt():
    w = W('ef4cnt', 'Lean ` contour_ne_one ` : for ` chi ` nonprincipal, ` y >_ 100 ` , ` T >_ 2 ` , ` abs ( PS + 2 pi i SC ) <_ 2 pi 400000000 ( y log ^ 2 ( N T y ) / T + y ^ ( 5 / 8 ) log ^ 2 ( N ( T + 2 ) ) ) ` ( ` PS ` = ` 2 pi i ` times the Perron sum; the heights by ~ ef2gh and ~ ef4ghb , the abscissa by ~ ef3sig , the cuts by ~ ef4cut , then ~ ef4core ; Lean ` 100000000 ` ).')
    A0, G = ante_of(S['ef4cnt'])
    c = Ctx(w, A0)
    chi = c.g(CHI); yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    dd = c([chi, w.inst('ef2ddl')], 'syl', DD(LFN, 'N'))
    nn = c([c([chi, w.inst('simpl')], 'syl', NX), w.inst('simpl')], 'syl', 'N e. NN')
    lv = {'T': tr, 'Y': yr}
    n4p = c([c([nn], 'nnrpd', 'N e. RR+'), c([c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR'), lin8(w, A0, [t2], '0 < ( T + 4 )', lv)], 'elrpd', '( T + 4 ) e. RR+')], 'rpmulcld', '( N x. ( T + 4 ) ) e. RR+')
    n4g = lin8(w, A0, [c([nn], 'nnge1d', '1 <_ N'), t2], '1 <_ ( N x. ( T + 4 ) )', {'T': tr, 'N': c([nn], 'nnred', 'N e. RR')}, products=True)
    ln40 = c([c([c([n4p], 'rpred', '( N x. ( T + 4 ) ) e. RR'), n4g], 'jca', '( ( N x. ( T + 4 ) ) e. RR /\\ 1 <_ ( N x. ( T + 4 ) ) )'), w.inst('logge0')], 'syl', '0 <_ %s' % LN4)
    h0 = c([c.a1(w.s([], 'hash0', '( # ` (/) ) = 0'), '( # ` (/) ) = 0'), lin8(w, A0, [ln40], '0 <_ ( ; 1 6 x. %s )' % LN4, {LN4: c([n4p], 'relogcld', '%s e. RR' % LN4)})], 'eqbrtrd', '( # ` (/) ) <_ ( ; 1 6 x. %s )' % LN4)
    spec0 = {DD(LFN, 'N'): dd, '(/) e. Fin': c.a1(w.s([], '0fi', '(/) e. Fin'), '(/) e. Fin'), '(/) C_ RR': c.a1(w.s([], '0ss', '(/) C_ RR'), '(/) C_ RR'), '( # ` (/) ) <_ ( ; 1 6 x. %s )' % LN4: h0}
    GH = tsub(stmt('ef2gh'), {'F': LFN, 'A': 'N', 'G': '(/)'})
    gha, ghc = ante_of(GH)
    top = c([rebuild(w, c, gha, spec0), w.inst('ef2gh')], 'syl', ghc)
    GB_ = tsub(stmt('ef4ghb'), {'F': LFN, 'A': 'N', 'G': '(/)'})
    gba, gbc = ante_of(GB_)
    bot = c([rebuild(w, c, gba, spec0), w.inst('ef4ghb')], 'syl', gbc)
    IV = '( T [,] ( T + 1 ) )'
    # drop the gap clauses
    def drop(st, fc):
        body = fc.split(' e. %s ' % IV, 1)[1]
        gap, rest = top_and(body)
        imp = w.s([w.s([], 'simpr', '( %s -> %s )' % (body, rest))], 'reximi', '( E. u e. %s %s -> E. u e. %s %s )' % (IV, body, IV, rest))
        return c([st, c.a1(imp, '( E. u e. %s %s -> E. u e. %s %s )' % (IV, body, IV, rest))], 'mpd', 'E. u e. %s %s' % (IV, rest)), rest
    top2, RT = drop(top, ghc)
    bot2, RB0 = drop(bot, gbc)
    cbr, RBy = cbvral_rex(w, IV, 'u', 'y', RB0)
    bot3 = c([bot2, c.a1(cbr, '( E. u e. %s %s <-> E. y e. %s %s )' % (IV, RB0, IV, RBy))], 'mpbid', 'E. y e. %s %s' % (IV, RBy))
    A1 = '( ( %s /\\ u e. %s ) /\\ %s )' % (A0, IV, RT)
    A2 = '( ( %s /\\ y e. %s ) /\\ %s )' % (A1, IV, RBy)
    c2 = Ctx(w, A2)
    L2 = lambda st: lift(w, st, A2)
    t1r = c2([L2(tr), numst(w, A2, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    uin = lift(w, w.s([w.s([], 'simpr', '( ( %s /\\ u e. %s ) -> u e. %s )' % (A0, IV, IV))], 'adantr', '( %s -> u e. %s )' % (A1, IV)), A2)
    yin = w.s([w.s([], 'simpr', '( ( %s /\\ y e. %s ) -> y e. %s )' % (A1, IV, IV))], 'adantr', '( %s -> y e. %s )' % (A2, IV))
    urr, tu_, u1_ = icc_out(c2, 'u', 'T', '( T + 1 )', uin, L2(tr), t1r)
    yrr, ty_, y1_ = icc_out(c2, 'y', 'T', '( T + 1 )', yin, L2(tr), t1r)
    rt2 = lift(w, w.s([], 'simpr', '( %s -> %s )' % (A1, RT)), A2)
    rb2 = c2([], 'simpr', RBy)
    GD2 = tsub(HGD, {'U': 'y', 'V': 'u'})
    gd = c2([c2([rb2, rt2], 'jca', '( %s /\\ %s )' % (RBy, RT)), c2.a1(w.s([], 'r19.26', '( %s <-> ( %s /\\ %s ) )' % (GD2, RBy, RT)), '( %s <-> ( %s /\\ %s ) )' % (GD2, RBy, RT))], 'mpbird', GD2)
    # sigma
    MM = '( |^ ` ( 2 x. ( y + u ) ) )'
    tyu = c2([numst(w, A2, '2', 'RR'), c2([yrr, urr], 'readdcld', '( y + u ) e. RR')], 'remulcld', '( 2 x. ( y + u ) ) e. RR')
    mz = c2([tyu, w.inst('ceilcl')], 'syl', '%s e. ZZ' % MM)
    mr = c2([mz], 'zred', '%s e. RR' % MM)
    mge = c2([tyu, w.inst('ceilge')], 'syl', '( 2 x. ( y + u ) ) <_ %s' % MM)
    mlt = c2([tyu, w.inst('ceilm1lt')], 'syl', '( %s - 1 ) < ( 2 x. ( y + u ) )' % MM)
    lvm = {'y': yrr, 'u': urr, 'T': L2(tr), MM: mr}
    hy = [mge, mlt, ty_, y1_, tu_, u1_, L2(t2)]
    mn0 = c2([c2([mz, lin8(w, A2, hy, '0 <_ %s' % MM, lvm)], 'jca', '( %s e. ZZ /\\ 0 <_ %s )' % (MM, MM)), c2.a1(w.s([], 'elnn0z', '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (MM, MM, MM)), '( %s e. NN0 <-> ( %s e. ZZ /\\ 0 <_ %s ) )' % (MM, MM, MM))], 'mpbird', '%s e. NN0' % MM)
    PMM = '( -u y + ( %s / 2 ) )' % MM
    BZI = tsub(stmt('ef3bz'), {'F': LFN, 'A': 'N', 'U': '( T + 4 )'})
    bza, bzc = ante_of(BZI)
    bzs = c2([c2([L2(dd), c2([L2(tr), numst(w, A2, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')], 'jca', bza), w.inst('ef3bz')], 'syl', bzc)
    bzf = c2([bzs, w.inst('simpl')], 'syl', '%s e. Fin' % BZ4)
    def imfin(fn):
        ff = w.s([], 'ref' if fn == 'Re' else 'imf', '%s : CC --> RR' % fn)
        fun = c2.a1(w.s([ff, w.inst('ffun')], 'ax-mp', 'Fun %s' % fn), 'Fun %s' % fn)
        return c2([fun, bzf, w.inst('imafi')], 'syl2anc', '( %s " %s ) e. Fin' % (fn, BZ4)), ff
    ref_, _ = imfin('Re')
    imf_, imff = imfin('Im')
    SG = tsub(stmt('ef3sig'), {'F': LFN, 'A': 'N', 'P': '-u y', 'M': MM, 'B': '( Re " %s )' % BZ4})
    sga, sgc = ante_of(SG)
    sspec = {DD(LFN, 'N'): L2(dd), '-u y e. RR': c2([yrr], 'renegcld', '-u y e. RR'), '-u ( T + 1 ) <_ -u y': lin8(w, A2, hy, '-u ( T + 1 ) <_ -u y', lvm), '-u y <_ 0': lin8(w, A2, hy, '-u y <_ 0', lvm),
             '%s e. NN0' % MM: mn0, '0 <_ %s' % PMM: lin8(w, A2, hy, '0 <_ %s' % PMM, lvm), '%s <_ ( T + 2 )' % PMM: lin8(w, A2, hy, '%s <_ ( T + 2 )' % PMM, lvm), '( Re " %s ) e. Fin' % BZ4: ref_}
    sg = c2([rebuild(w, c2, sga, sspec), w.inst('ef3sig')], 'syl', sgc)
    SIGB = sgc.split(' e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ', 1)[1]
    A3 = '( ( %s /\\ a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ) /\\ %s )' % (A2, SIGB)
    c3 = Ctx(w, A3)
    L3 = lambda st: lift(w, st, A3)
    ain = w.s([w.s([], 'simpr', '( ( %s /\\ a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ) -> a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) )' % A2)], 'adantr', '( %s -> a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) )' % A3)
    ar_, a916, a58 = icc_out(c3, 'a', '( 9 / ; 1 6 )', '( 5 / 8 )', ain, numst(w, A3, '( 9 / ; 1 6 )', 'RR'), numst(w, A3, '( 5 / 8 )', 'RR'))
    # cuts
    CU = tsub(stmt('ef4cut'), {'B': '( Im " %s )' % BZ4, 'P': '-u y', 'Q': 'u'})
    cua, cuc = ante_of(CU)
    imss = c3.a1(w.s([w.s([], 'imassrn', '( Im " %s ) C_ ran Im' % BZ4), w.s([imff, w.inst('frn')], 'ax-mp', 'ran Im C_ RR')], 'sstri', '( Im " %s ) C_ RR' % BZ4), '( Im " %s ) C_ RR' % BZ4)
    cspec = {'( Im " %s ) e. Fin' % BZ4: L3(imf_), '( Im " %s ) C_ RR' % BZ4: imss, '-u y e. RR': c3([L3(yrr)], 'renegcld', '-u y e. RR'), 'u e. RR': L3(urr),
             '1 <_ ( u - -u y )': lin8(w, A3, [L3(h) for h in hy], '1 <_ ( u - -u y )', {k: L3(v) for k, v in lvm.items()})}
    cut = c3([rebuild(w, c3, cua, cspec), w.inst('ef4cut')], 'syl', cuc)
    BODY = cuc[len('E. m e. NN E. g '):]
    A4 = '( ( %s /\\ m e. NN ) /\\ %s )' % (A3, BODY)
    c4 = Ctx(w, A4)
    CO = tsub(stmt('ef4core'), {'U': 'y', 'V': 'u', 'S': 'a', 'M': MM, 'K': 'm', 'G': 'g'})
    coa, coc = ante_of(CO)
    L4 = lambda st: lift(w, st, A4)
    kspec = {'y e. RR': L4(yrr), 'u e. RR': L4(urr), 'T <_ y': L4(ty_), 'y <_ ( T + 1 )': L4(y1_), 'T <_ u': L4(tu_), 'u <_ ( T + 1 )': L4(u1_), GD2: L4(gd),
             'a e. RR': L4(ar_), '( 9 / ; 1 6 ) <_ a': L4(a916), 'a <_ ( 5 / 8 )': L4(a58), '%s e. NN0' % MM: L4(mn0),
             'u <_ ( -u y + ( %s / 2 ) )' % MM: L4(lin8(w, A2, hy, 'u <_ ( -u y + ( %s / 2 ) )' % MM, lvm)), '( -u y + ( %s / 2 ) ) <_ ( T + 2 )' % MM: L4(sspec['%s <_ ( T + 2 )' % PMM])}
    co = c4([rebuild(w, c4, coa, kspec), w.inst('ef4core')], 'syl', coc)
    e1 = w.s([co], 'ex', '( ( %s /\\ m e. NN ) -> ( %s -> %s ) )' % (A3, BODY, G))
    e2 = w.s([e1], 'exlimdv', '( ( %s /\\ m e. NN ) -> ( E. g %s -> %s ) )' % (A3, BODY, G))
    e3 = c3([e2], 'rexlimdva', '( %s -> %s )' % (cuc, G))
    e4 = c3([cut, e3], 'mpd', G)
    e5 = w.s([e4], 'ex', '( ( %s /\\ a e. ( ( 9 / ; 1 6 ) [,] ( 5 / 8 ) ) ) -> ( %s -> %s ) )' % (A2, SIGB, G))
    e6 = c2([e5], 'rexlimdva', '( %s -> %s )' % (sgc, G))
    e7 = c2([sg, e6], 'mpd', G)
    e8 = w.s([e7], 'ex', '( ( %s /\\ y e. %s ) -> ( %s -> %s ) )' % (A1, IV, RBy, G))
    c1 = Ctx(w, A1)
    e9 = c1([e8], 'rexlimdva', '( E. y e. %s %s -> %s )' % (IV, RBy, G))
    e10 = c1([lift(w, bot3, A1), e9], 'mpd', G)
    e11 = w.s([e10], 'ex', '( ( %s /\\ u e. %s ) -> ( %s -> %s ) )' % (A0, IV, RT, G))
    e12 = c([e11], 'rexlimdva', '( E. u e. %s %s -> %s )' % (IV, RT, G))
    w.qed([top2, e12], 'mpd', S['ef4cnt'])
    return run8(w)


def cbvral_rex(w, X, var, new, body):
    eq, nb = w.wcongr(body, {var: new}, '%s = %s' % (var, new), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, new, var, new))})
    return w.s([eq], 'cbvrexvw', '( E. %s e. %s %s <-> E. %s e. %s %s )' % (var, X, body, new, X, nb)), nb



def gen_ef():
    from ef4_e import box_hp
    w = W('ef4ef', 'Lean ` explicit_formula_ne_one ` : for ` chi ` nonprincipal, ` y >_ 100 ` , ` T >_ 2 ` , ` abs ( psi ( y , chi ) + sum_rho m_rho y ^ rho / rho ) <_ 500000000 ( y log ^ 2 ( N T y ) / T + y ^ ( 5 / 8 ) log ^ 2 ( N ( T + 2 ) ) + log ^ 2 ( N T y ) ) ` , the sum over the zeros of ` ( s - 1 ) L ( s , chi ) ` off 1 in ` [ 1 / 2 , 1 ] x [ - T , T ] ` ( ~ ef1psb , ~ ef4cnt ; Lean ` 200000000 ` ).')
    A0, G = ante_of(S['ef4ef'])
    c = Ctx(w, A0)
    chi = c.g(CHI); yr = c.g('Y e. RR'); y100 = c.g('; ; 1 0 0 <_ Y'); tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    nx = c([chi, w.inst('simpl')], 'syl', NX)
    nn = c([nx, w.inst('simpl')], 'syl', 'N e. NN')
    f = c1_facts(w, c, yr, y100)
    cnt = c([w.s([], 'id', '( %s -> %s )' % (A0, A0)), w.inst('ef4cnt')], 'syl', ante_of(stmt('ef4cnt'))[1])
    PSB = stmt('ef1psb')
    pba, pbc = ante_of(PSB)
    psb = c([rebuild(w, c, pba, {NX: nx}), w.inst('ef1psb')], 'syl', pbc)
    # closures
    RE = tsub(stmt('ef1redge'), {'C': C1})
    rea, rec_ = ante_of(RE)
    red = c([rebuild(w, c, rea, {NX: nx, 'Y e. RR+': f['yp'], '%s e. RR' % C1: f['c1r'], '1 < %s' % C1: f['c1g']}), w.inst('ef1redge')], 'syl', rec_)
    cv, pse = top_and(rec_)
    RHL = pse.split(' = ', 1)[1]
    psc = c([c([red, w.inst('simpr')], 'syl', pse), c([c([red, w.inst('simpl')], 'syl', cv), w.inst('climcl')], 'syl', '%s e. CC' % RHL)], 'eqeltrd', '%s e. CC' % PS1)
    An = '( %s /\\ n e. ( 1 ... ( |_ ` Y ) ) )' % A0
    cn = Ctx(w, An)
    nin = cn([cn([], 'simpr', 'n e. ( 1 ... ( |_ ` Y ) )'), w.inst('elfznn')], 'syl', 'n e. NN')
    XCn = '( X ` ( ( ZRHom ` ( Z/nZ ` N ) ) ` n ) )'
    tn = cn([cn([cn([lift(w, nx, An), nin], 'jca', '( %s /\\ n e. NN )' % NX), w.inst('lchrcl')], 'syl', '%s e. CC' % XCn), cn([cn([nin, w.inst('vmacl')], 'syl', '( Lam ` n ) e. RR')], 'recnd', '( Lam ` n ) e. CC')], 'mulcld',
            '( %s x. ( Lam ` n ) ) e. CC' % XCn)
    psic = c([c([], 'fzfid', '( 1 ... ( |_ ` Y ) ) e. Fin'), tn], 'fsumcl', '%s e. CC' % PSI)
    EZ = tsub(stmt('ezf'), {'A': '( 1 / 2 )'})
    eza, ezc = ante_of(EZ)
    ez = c([rebuild(w, c, eza, {NX: nx, '( 1 / 2 ) e. RR': numst(w, A0, '( 1 / 2 )', 'RR'), '0 < ( 1 / 2 )': c.a1(w.s([], 'halfgt0', '0 < ( 1 / 2 )'), '0 < ( 1 / 2 )'),
                                 '( 1 / 2 ) <_ 1': c.a1(w.s([w.s([], 'halfre', '( 1 / 2 ) e. RR'), w.s([], '1re', '1 e. RR'), w.s([], 'halflt1', '( 1 / 2 ) < 1')], 'ltleii', '( 1 / 2 ) <_ 1'), '( 1 / 2 ) <_ 1')}), w.inst('ezf')], 'syl', ezc)
    zfin, zord = conj_split(w, A0, ez)
    Aq = '( %s /\\ q e. %s )' % (A0, ZFE)
    cq = Ctx(w, Aq)
    qz = cq([], 'simpr', 'q e. %s' % ZFE)
    from ef4_g import elrab_unpack
    qbx, _, _ = elrab_unpack(w, Aq, 'r', BOX('( 1 / 2 )', 'T'), '( r =/= 1 /\\ ( %s ` r ) = 0 )' % E, 'q', qz)
    qh = box_hp(w, Aq, 'q', qbx, numst(w, Aq, '( 1 / 2 )', 'RR'), cq.a1(w.s([], 'halfgt0', '0 < ( 1 / 2 )'), '0 < ( 1 / 2 )'), lift(w, tr, Aq), '( 1 / 2 )')
    qc, q0, _ = hp0_facts(cq, 'q', qh)
    qne = ne0_re(cq, 'q', qc, q0)
    EH = '( %s holord q )' % E
    oq = cq([qz, cq([lift(w, zord, Aq), w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (ZFE, EH))], 'mpd', '%s e. NN' % EH)
    tq = cq([cq([oq], 'nncnd', '%s e. CC' % EH), cq([cq([cq([lift(w, f['yp'], Aq)], 'rpcnd', 'Y e. CC'), qc], 'cxpcld', '( Y ^c q ) e. CC'), qc, qne], 'divcld', '( ( Y ^c q ) / q ) e. CC')], 'mulcld',
            '( %s x. ( ( Y ^c q ) / q ) ) e. CC' % EH)
    scc = c([zfin, tq], 'fsumcl', '%s e. CC' % SCE)
    tpc = c.a1(w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI), '%s e. CC' % TPI)
    clz = Closure(w, A0, {PS1: ('CC', psc), SCE: ('CC', scc), PSI: ('CC', psic), TPI: ('CC', tpc)})
    for k in (PS1, SCE, PSI, TPI):
        clz.atom(k)
    AA = '( %s + ( %s x. %s ) )' % (PS1, TPI, SCE)
    BB = '( %s - ( %s x. %s ) )' % (PS1, TPI, PSI)
    SUM = '( %s + %s )' % (PSI, SCE)
    eq = ringeq(w, A0, '( %s x. %s )' % (TPI, SUM), '( %s - %s )' % (AA, BB), clz)
    aac = clz.mem(AA, 'CC'); bbc = clz.mem(BB, 'CC')
    ad = c([aac, bbc, w.inst('abs2dif2')], 'syl2anc', '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (AA, BB, AA, BB))
    PI2 = '( 2 x. _pi )'
    atp = abs_tpi(w, c)
    sc2 = c([psic, scc], 'addcld', '%s e. CC' % SUM)
    am = c([c([tpc, sc2], 'absmuld', '( abs ` ( %s x. %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (TPI, SUM, TPI, SUM)), c([atp], 'oveq1d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, SUM, PI2, SUM))], 'eqtrd',
            '( abs ` ( %s x. %s ) ) = ( %s x. ( abs ` %s ) )' % (TPI, SUM, PI2, SUM))
    l1 = c([c([c([am], 'eqcomd', '( %s x. ( abs ` %s ) ) = ( abs ` ( %s x. %s ) )' % (PI2, SUM, TPI, SUM)), c([eq], 'fveq2d', '( abs ` ( %s x. %s ) ) = ( abs ` ( %s - %s ) )' % (TPI, SUM, AA, BB))], 'eqtrd',
               '( %s x. ( abs ` %s ) ) = ( abs ` ( %s - %s ) )' % (PI2, SUM, AA, BB)), ad], 'eqbrtrd', '( %s x. ( abs ` %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (PI2, SUM, AA, BB))
    CB = ante_of(stmt('ef4cnt'))[1].split(' <_ ', 1)[1]
    PB = pbc.split(' <_ ', 1)[1]
    RHS1 = '( %s + %s )' % (CB, PB)
    lv1 = {'( abs ` %s )' % AA: c([aac], 'abscld', '( abs ` %s ) e. RR' % AA), '( abs ` %s )' % BB: c([bbc], 'abscld', '( abs ` %s ) e. RR' % BB)}
    tp = c([tr, lin8(w, A0, [t2], '0 < T', {'T': tr})], 'elrpd', 'T e. RR+')
    cl = Closure(w, A0, {'Y': ('RR+', f['yp']), 'T': ('RR+', tp), 'N': ('NN', nn), '_pi': ('RR+', c.a1(w.s([], 'pirp', '_pi e. RR+'), '_pi e. RR+'))})
    LTY = '( log ` ( T x. Y ) )'
    for k in (CB, PB):
        lv1[k] = cl.mem(k, 'RR')
    l2 = c([cnt, psb], 'le2addd', '( ( abs ` %s ) + ( abs ` %s ) ) <_ %s' % (AA, BB, RHS1))
    # divide by 2 pi
    pi2p = c([c.a1(w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), c.a1(w.s([], 'pirp', '_pi e. RR+'), '_pi e. RR+')], 'rpmulcld', '%s e. RR+' % PI2)
    R_ = '( ( %s x. ( %s + %s ) ) + ( ( ; ; 2 0 0 x. ( ( Y x. ( %s ^ 2 ) ) / T ) ) + ( ; 3 0 x. ( %s ^ 2 ) ) ) )' % (KC, P1, P2, LTY, LTY)
    e2 = c([c([numst(w, A0, '2', 'CC'), c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mulcld', '%s e. CC' % PI2), cl.mem('( %s x. ( %s + %s ) )' % (KC, P1, P2), 'CC'),
            cl.mem('( ( ; ; 2 0 0 x. ( ( Y x. ( %s ^ 2 ) ) / T ) ) + ( ; 3 0 x. ( %s ^ 2 ) ) )' % (LTY, LTY), 'CC')], 'adddid', '( %s x. %s ) = %s' % (PI2, R_, RHS1))
    l3 = le_tr(w, A0, l1, '( %s x. ( abs ` %s ) )' % (PI2, SUM), '( ( abs ` %s ) + ( abs ` %s ) )' % (AA, BB), c([l2, c([e2], 'eqcomd', '%s = ( %s x. %s )' % (RHS1, PI2, R_))], 'breqtrd', '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s x. %s )' % (AA, BB, PI2, R_)),
               '( %s x. %s )' % (PI2, R_))
    asr = c([sc2], 'abscld', '( abs ` %s ) e. RR' % SUM)
    l4 = c([l3, c([asr, cl.mem(R_, 'RR'), pi2p], 'lemul2d', '( ( abs ` %s ) <_ %s <-> ( %s x. ( abs ` %s ) ) <_ ( %s x. %s ) )' % (SUM, R_, PI2, SUM, PI2, R_))], 'mpbird', '( abs ` %s ) <_ %s' % (SUM, R_))
    # R <_ KE ( P1 + P2 + LNY ^ 2 )
    TY = '( T x. Y )'
    ty1 = lin8(w, A0, [t2, y100], '1 <_ %s' % TY, {'T': tr, 'Y': yr}, products=True)
    lty0 = c([c([cl.mem(TY, 'RR'), ty1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (TY, TY)), w.inst('logge0')], 'syl', '0 <_ %s' % LTY)
    NTY = '( ( N x. T ) x. Y )'
    nr = c([nn], 'nnred', 'N e. RR')
    a1_ = c([numst(w, A0, '1', 'RR'), nr, cl.mem(TY, 'RR'), lin8(w, A0, [ty1], '0 <_ %s' % TY, {TY: cl.mem(TY, 'RR')}), c([nn], 'nnge1d', '1 <_ N')], 'lemul1ad', '( 1 x. %s ) <_ ( N x. %s )' % (TY, TY))
    a2_ = c([cl.mem(TY, 'CC')], 'mullidd', '( 1 x. %s ) = %s' % (TY, TY))
    a3_ = c([c([nr], 'recnd', 'N e. CC'), c([tr], 'recnd', 'T e. CC'), c([yr], 'recnd', 'Y e. CC')], 'mulassd', '%s = ( N x. %s )' % (NTY, TY))
    tyle = c([c([c([a2_], 'eqcomd', '%s = ( 1 x. %s )' % (TY, TY)), a1_], 'eqbrtrd', '%s <_ ( N x. %s )' % (TY, TY)), c([a3_], 'eqcomd', '( N x. %s ) = %s' % (TY, NTY))], 'breqtrd', '%s <_ %s' % (TY, NTY))
    lle = c([tyle, c([cl.mem(TY, 'RR+'), cl.mem(NTY, 'RR+'), w.inst('logleb')], 'syl2anc', '( %s <_ %s <-> %s <_ %s )' % (TY, NTY, LTY, LNY))], 'mpbid', '%s <_ %s' % (LTY, LNY))
    sq = c([c([cl.mem(LTY, 'RR'), lty0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (LTY, LTY)), c([cl.mem(LNY, 'RR'), lle], 'jca', '( %s e. RR /\\ %s <_ %s )' % (LNY, LTY, LNY)), w.inst('le2sq2')], 'syl2anc', '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LTY, LNY))
    ysq = c([cl.mem('( %s ^ 2 )' % LTY, 'RR'), cl.mem('( %s ^ 2 )' % LNY, 'RR'), yr, lin8(w, A0, [y100], '0 <_ Y', {'Y': yr}), sq], 'lemul2ad', '( Y x. ( %s ^ 2 ) ) <_ ( Y x. ( %s ^ 2 ) )' % (LTY, LNY))
    yl = c([cl.mem('( Y x. ( %s ^ 2 ) )' % LTY, 'RR'), cl.mem('( Y x. ( %s ^ 2 ) )' % LNY, 'RR'), tp, ysq], 'lediv1dd', '( ( Y x. ( %s ^ 2 ) ) / T ) <_ %s' % (LTY, P1))
    p10 = c([cl.mem('( Y x. ( %s ^ 2 ) )' % LNY, 'RR'), tp, c([yr, cl.mem('( %s ^ 2 )' % LNY, 'RR'), lin8(w, A0, [y100], '0 <_ Y', {'Y': yr}), c([cl.mem(LNY, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNY)], 'mulge0d', '0 <_ ( Y x. ( %s ^ 2 ) )' % LNY)], 'divge0d', '0 <_ %s' % P1)
    p20 = c([cl.mem('( Y ^c ( 5 / 8 ) )', 'RR'), cl.mem('( %s ^ 2 )' % LNT, 'RR'), c([c([f['yp'], numst(w, A0, '( 5 / 8 )', 'RR')], 'rpcxpcld', '( Y ^c ( 5 / 8 ) ) e. RR+')], 'rpge0d', '0 <_ ( Y ^c ( 5 / 8 ) )'), c([cl.mem(LNT, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNT)], 'mulge0d', '0 <_ %s' % P2)
    ly0 = c([cl.mem(LNY, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % LNY)
    lvr = {P1: cl.mem(P1, 'RR'), P2: cl.mem(P2, 'RR'), '( %s ^ 2 )' % LNY: cl.mem('( %s ^ 2 )' % LNY, 'RR'), '( %s ^ 2 )' % LTY: cl.mem('( %s ^ 2 )' % LTY, 'RR'), '( ( Y x. ( %s ^ 2 ) ) / T )' % LTY: cl.mem('( ( Y x. ( %s ^ 2 ) ) / T )' % LTY, 'RR')}
    l5 = lin8(w, A0, [yl, sq, p10, p20, ly0], '%s <_ %s' % (R_, G.split(' <_ ', 1)[1]), lvr)
    fin = le_tr(w, A0, l4, '( abs ` %s )' % SUM, R_, l5, G.split(' <_ ', 1)[1])
    w.qed([fin], 'idi', S['ef4ef'])
    return run8(w)


def abs_tpi(w, c):
    PI2 = '( 2 x. _pi )'
    atp = c([c.a1(w.s([], '2cn', '2 e. CC'), '2 e. CC'), c.a1(w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'), '( _i x. _pi ) e. CC')], 'absmuld',
            '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI)
    a2 = c.a1(w.s([w.s([], '0le2', '0 <_ 2'), w.s([w.s([], '2re', '2 e. RR')], 'absidi', '( 0 <_ 2 -> ( abs ` 2 ) = 2 )')], 'ax-mp', '( abs ` 2 ) = 2'), '( abs ` 2 ) = 2')
    ap_ = c.a1(w.s([w.s([w.s([], '0re', '0 e. RR'), w.s([], 'pire', '_pi e. RR'), w.s([], 'pipos', '0 < _pi')], 'ltleii', '0 <_ _pi'), w.s([w.s([], 'pire', '_pi e. RR')], 'absidi', '( 0 <_ _pi -> ( abs ` _pi ) = _pi )')], 'ax-mp', '( abs ` _pi ) = _pi'), '( abs ` _pi ) = _pi')
    aip = c([c([c.a1(w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'), c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )'),
             c([c.a1(w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1'), ap_], 'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')
    aip2 = c([aip, c([c.a1(w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mullidd', '( 1 x. _pi ) = _pi')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = _pi')
    return c([atp, c([a2, aip2], 'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = %s' % PI2)], 'eqtrd', '( abs ` %s ) = %s' % (TPI, PI2))


def crect_cc(w, A, Aa, Bb, tr):
    """( A -> ( Aa crect Bb ) C_ CC ) for the corners of BZ ( T + 4 )"""
    c = Ctx(w, A)
    t4 = c([lift(w, tr, A), numst(w, A, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')
    ac = ptc(c, '( 1 / 2 )', '-u ( T + 4 )', numst(w, A, '( 1 / 2 )', 'RR'), c([t4], 'renegcld', '-u ( T + 4 ) e. RR'))
    bc = ptc(c, '( 3 / 2 )', '( T + 4 )', numst(w, A, '( 3 / 2 )', 'RR'), t4)
    return c([ac, bc, w.inst('crectss')], 'syl2anc', '( %s crect %s ) C_ CC' % (Aa, Bb))


GENS = {'ef4ln': gen_ln, 'ef4nm': gen_nm, 'ef4core': gen_core, 'ef4cnt': gen_cnt, 'ef4ef': gen_ef}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
