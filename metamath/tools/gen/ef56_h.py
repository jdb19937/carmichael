"""Sortie EF56: the zeta contour meets no zero (ef6ln, after EF4's ef4ln, for a generic F)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift
import lin
lin.FASTPATH = True
from ef4_a import ic_, ptc, icc_in, icc_out
from ef4_f import c1_facts
from ef4_g import bz_in, elrab_unpack
from ef4_h import Mini, crect_cc


def gen_ln():
    w = W('ef6ln', 'For ` F ` nonvanishing on the two end lines, the contour of Lean ` contour_zeta ` meets no zero of ` F ` : the cut lines ` [ S , c ] + i G ( j ) ` ( ` hlines ` : the end lines are good heights, an interior line misses ` Im " BZ ` ) and the left edge ` S + i [ - U , T + 2 ] ` ( ` hleftnz ` : ` S ` misses ` Re " BZ ` ).')
    A0, G = ante_of(S['ef6ln'])
    c = Ctx(w, A0)
    M = Mini(w)
    g = c.g
    yr = g('Y e. RR'); y100 = g('; ; 1 0 0 <_ Y'); tr = g('T e. RR'); t2 = g('2 <_ T')
    ur = g('U e. RR'); vr = g('V e. RR'); tu = g('T <_ U'); u1 = g('U <_ ( T + 1 )'); tv = g('T <_ V'); v1 = g('V <_ ( T + 1 )')
    sr = g('S e. RR'); s916 = g('( 9 / ; 1 6 ) <_ S'); s58 = g('S <_ ( 5 / 8 )')
    hgd = g(NZE)
    nsb = g('-. S e. ( Re " %s )' % BZF)
    kn = g('K e. NN'); gf = g('G : ( 0 ... K ) --> RR'); g0 = g('( G ` 0 ) = -u U'); gk = g('( G ` K ) = V')
    avo = g('A. e e. ( 1 ..^ K ) -. ( G ` e ) e. ( Im " %s )' % BZF)
    rng = g('A. e e. ( 0 ... K ) ( -u U <_ ( G ` e ) /\\ ( G ` e ) <_ V )')
    f = c1_facts(w, c, yr, y100)
    t4 = c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')
    X4 = BZF.split(' | ')[0][len('{ r e. '):]
    def in_bz(A, zx, zy, zxr, zyr, fz, hy, lv):
        cc = Ctx(w, A)
        z = PTL(zx, zy)
        zc = ptc(cc, zx, zy, zxr, zyr)
        hy2 = hy + M.corners(cc, zx, zy, zxr, zyr)
        lv2 = dict(lv); lv2['( Re ` %s )' % z] = cc([zc], 'recld', '( Re ` %s ) e. RR' % z); lv2['( Im ` %s )' % z] = cc([zc], 'imcld', '( Im ` %s ) e. RR' % z)

        return bz_inF(M, A, '( T + 4 )', lift(w, t4, A), z, zc, fz, hy2, lv2), zc
    def image(A, fn, z, zin, zc):
        cc = Ctx(w, A)
        ff = w.s([], 'ref' if fn == 'Re' else 'imf', '%s : CC --> RR' % fn)
        fun = cc.a1(w.s([ff, w.inst('ffun')], 'ax-mp', 'Fun %s' % fn), 'Fun %s' % fn)
        dm = w.s([ff, w.inst('fdm')], 'ax-mp', 'dom %s = CC' % fn)
        Aa, Bb = X4.split(' crect ')
        Aa, Bb = Aa[2:], Bb[:-2]
        bzdm = cc([cc.a1(w.s([], 'ssrab2', '%s C_ %s' % (BZF, X4)), '%s C_ %s' % (BZF, X4)), cc([crect_cc(w, A, Aa, Bb, tr), cc.a1(w.s([dm], 'eqcomi', 'CC = dom %s' % fn), 'CC = dom %s' % fn)], 'sseqtrd', '%s C_ dom %s' % (X4, fn))], 'sstrd', '%s C_ dom %s' % (BZF, fn))
        return cc([zin, cc([fun, bzdm, w.inst('funfvima2')], 'syl2anc', '( %s e. %s -> ( %s ` %s ) e. ( %s " %s ) )' % (z, BZF, fn, z, fn, BZF))], 'mpd', '( %s ` %s ) e. ( %s " %s )' % (fn, z, fn, BZF))
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
    GD2 = '( ( F ` %s ) =/= 0 /\\ ( F ` %s ) =/= 0 )' % (PTL('v', '-u U'), PTL('v', 'V'))
    gx, gxv = ral_at(w, Ax, L(hgd), 'v', 'x', GD2, vin)
    TGT = '( %s ` %s ) =/= 0' % ('F', PTL('x', CHN('j')))
    def endcase(eqj, val, sel, gval):
        A2 = '( %s /\\ j = %s )' % (Ax, eqj)
        c2 = Ctx(w, A2)
        gv = c2([c2([c2([], 'simpr', 'j = %s' % eqj)], 'fveq2d', '%s = ( G ` %s )' % (CHN('j'), eqj)), lift(w, gval, A2)], 'eqtrd', '%s = %s' % (CHN('j'), val))
        nz_ = c2([lift(w, gx, A2), w.inst(sel)], 'syl', '( %s ` %s ) =/= 0' % ('F', PTL('x', val)))
        e = c2([c2([c2([gv], 'oveq2d', '( _i x. %s ) = ( _i x. %s )' % (CHN('j'), val))], 'oveq2d', '%s = %s' % (PTL('x', CHN('j')), PTL('x', val)))], 'fveq2d', '( %s ` %s ) = ( %s ` %s )' % ('F', PTL('x', CHN('j')), 'F', PTL('x', val)))
        return c2([nz_, c2([e], 'neeq1d', '( %s <-> ( %s ` %s ) =/= 0 )' % (TGT, 'F', PTL('x', val)))], 'mpbird', TGT)
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
    nav, _ = ral_at(w, Ai, Li(avo), 'e', 'j', '-. ( G ` e ) e. ( Im " %s )' % BZF, jo)
    rj, _ = ral_at(w, Ai, Li(rng), 'e', 'j', '( -u U <_ ( G ` e ) /\\ ( G ` e ) <_ V )', Li(jin))
    rj1, rj2 = conj_split(w, Ai, rj)
    Az = '( %s /\\ ( %s ` %s ) = 0 )' % (Ai, 'F', PTL('x', CHN('j')))
    cz = Ctx(w, Az)
    Lz = lambda st: lift(w, st, Az)
    lvz = {k: Lz(v) for k, v in lvx.items()}
    hz = [Lz(Li(sx)), Lz(Li(xc1)), Lz(Li(L(s916))), Lz(Li(L(f['c54']))), Lz(rj1), Lz(rj2), Lz(Li(L(u1))), Lz(Li(L(v1))), Lz(Li(L(t2)))]
    zb, zc = in_bz(Az, 'x', CHN('j'), Lz(Li(xr)), Lz(Li(gj)), cz([], 'simpr', '( %s ` %s ) = 0' % ('F', PTL('x', CHN('j')))), hz, lvz)
    zim = image(Az, 'Im', PTL('x', CHN('j')), zb, zc)
    gim = cz([cz([cz([Lz(Li(xr)), Lz(Li(gj)), w.inst('crim')], 'syl2anc', '( Im ` %s ) = %s' % (PTL('x', CHN('j')), CHN('j')))], 'eqcomd', '%s = ( Im ` %s )' % (CHN('j'), PTL('x', CHN('j')))), zim], 'eqeltrd',
             '%s e. ( Im " %s )' % (CHN('j'), BZF))
    ki = ci([gim, lift(w, nav, Az)], 'pm2.65da', '-. ( %s ` %s ) = 0' % ('F', PTL('x', CHN('j'))))
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
    TL = '( %s ` %s ) =/= 0' % ('F', PTL('S', 't'))
    Az2 = '( %s /\\ ( %s ` %s ) = 0 )' % (At, 'F', PTL('S', 't'))
    cz2 = Ctx(w, Az2)
    L2 = lambda st: lift(w, st, Az2)
    lv2 = {'S': L2(Lt(sr)), 't': L2(ttr), 'T': L2(Lt(tr)), 'U': L2(Lt(ur))}
    zb2, zc2 = in_bz(Az2, 'S', 't', L2(Lt(sr)), L2(ttr), cz2([], 'simpr', '( %s ` %s ) = 0' % ('F', PTL('S', 't'))), [L2(Lt(s916)), L2(Lt(s58)), L2(tlo), L2(thi), L2(Lt(u1)), L2(Lt(t2))], lv2)
    zre = image(Az2, 'Re', PTL('S', 't'), zb2, zc2)
    sre = cz2([cz2([cz2([L2(Lt(sr)), L2(ttr), w.inst('crre')], 'syl2anc', '( Re ` %s ) = S' % PTL('S', 't'))], 'eqcomd', 'S = ( Re ` %s )' % PTL('S', 't')), zre], 'eqeltrd', 'S e. ( Re " %s )' % BZF)
    nl = ct([sre, lift(w, nsb, Az2)], 'pm2.65da', '-. ( %s ` %s ) = 0' % ('F', PTL('S', 't')))
    alt = c([ct([nl], 'neqned', TL)], 'ralrimiva', 'A. t e. ( -u U [,] ( T + 2 ) ) %s' % TL)
    w.qed([alj, alt], 'jca', S['ef6ln'])
    return run8(w)





GENS = {'ef6ln': gen_ln}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
