"""Sortie EF56: the set of absolute ordinates of the zeros of g near +-T (ef6gc) and the good heights of g (ef6gd)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from c8_o import numst
import congr as _cg
from cl import lift, Closure
import lin
lin.FASTPATH = True
from ef2lib import zs_unpack, sq_data
from ef4_a import icc_in, icc_out

KS4 = ['T', '( T + 1 )', '-u ( T + 1 )', KB1]


def aim_facts(w):
    imcc = w.s([w.s([], 'imf', 'Im : CC --> RR'), w.s([], 'ax-resscn', 'RR C_ CC'), w.inst('fss')], 'mp2an', 'Im : CC --> CC')
    aif = w.s([w.s([], 'absf', 'abs : CC --> RR'), imcc, w.inst('fco')], 'mp2an', '%s : CC --> RR' % AIM)
    return aif


def ks_reals(c, tr):
    w = c.w
    t1 = c([tr, numst(w, c.A, '1', 'RR')], 'readdcld', '( T + 1 ) e. RR')
    nt1 = c([t1], 'renegcld', '-u ( T + 1 ) e. RR')
    kb = c([nt1, numst(w, c.A, '1', 'RR')], 'readdcld', '%s e. RR' % KB1)
    return dict(zip(KS4, [tr, t1, nt1, kb]))


def gen_gc():
    w = W('ef6gc', 'The absolute ordinates of the zeros of ` g ` in the four ` 13 / 8 ` -squares about ` 2 + i T ` , ` 2 + i ( T + 1 ) ` , ` 2 - i ( T + 1 ) ` , ` 2 - i T ` form a finite set of reals with at most ` 4 <_ 16 log ( T + 4 ) ` elements ( ~ ef6go ).')
    A0 = ante_of(S['ef6gc'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); t2 = c.g('2 <_ T')
    kr = ks_reals(c, tr)
    aif = aim_facts(w)
    fun = c.a1(w.s([aif, w.inst('ffun')], 'ax-mp', 'Fun %s' % AIM), 'Fun %s' % AIM)
    go = {}
    for K in KS4:
        st = c([kr[K], w.inst('ef6go')], 'syl', tsub(S['ef6go'], {'K': K}).split(' -> ', 1)[1][:-2])
        go[K] = conj_split(w, A0, st)
    ddg = c.a1(w.s([], 'ef2ddg', DD(GF, '1')), DD(GF, '1'))
    zf = {}
    for K in KS4:
        zc = tsub(ante_of(stmt('ef2zs'))[1], {'F': GF, 'A': '1', 'T': K})
        zf[K] = c([c([c([ddg, kr[K]], 'jca', '( %s /\\ %s e. RR )' % (DD(GF, '1'), K)), w.inst('ef2zs')], 'syl', zc), w.inst('simp1')], 'syl', top_and(zc)[0])
    Z = {K: ZSG(K) for K in KS4}
    U1_ = '( %s u. %s )' % (Z['T'], Z['( T + 1 )'])
    U2_ = '( %s u. %s )' % (Z['-u ( T + 1 )'], Z[KB1])
    u1f = c([zf['T'], zf['( T + 1 )'], w.inst('unfi')], 'syl2anc', '%s e. Fin' % U1_)
    u2f = c([zf['-u ( T + 1 )'], zf[KB1], w.inst('unfi')], 'syl2anc', '%s e. Fin' % U2_)
    wf = c([u1f, u2f, w.inst('unfi')], 'syl2anc', '%s e. Fin' % WG4)
    gf = c([fun, wf, w.inst('imafi')], 'syl2anc', '%s e. Fin' % GG)
    grr = c.a1(w.s([w.s([], 'imassrn', '%s C_ ran %s' % (GG, AIM)), w.s([aif, w.inst('frn')], 'ax-mp', 'ran %s C_ RR' % AIM)], 'sstri', '%s C_ RR' % GG), '%s C_ RR' % GG)
    I = {K: '( %s " %s )' % (AIM, Z[K]) for K in KS4}
    IU1 = '( %s " %s )' % (AIM, U1_); IU2 = '( %s " %s )' % (AIM, U2_)
    e1 = w.s([], 'imaundi', '%s = ( %s u. %s )' % (GG, IU1, IU2))
    e2 = w.s([], 'imaundi', '%s = ( %s u. %s )' % (IU1, I['T'], I['( T + 1 )']))
    e3 = w.s([], 'imaundi', '%s = ( %s u. %s )' % (IU2, I['-u ( T + 1 )'], I[KB1]))
    iu1f = c([go['T'][0], go['( T + 1 )'][0], w.inst('unfi')], 'syl2anc', '( %s u. %s ) e. Fin' % (I['T'], I['( T + 1 )']))
    iu2f = c([go['-u ( T + 1 )'][0], go[KB1][0], w.inst('unfi')], 'syl2anc', '( %s u. %s ) e. Fin' % (I['-u ( T + 1 )'], I[KB1]))
    h1 = c([go['T'][0], go['( T + 1 )'][0], w.inst('hashun2')], 'syl2anc', '( # ` ( %s u. %s ) ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (I['T'], I['( T + 1 )'], I['T'], I['( T + 1 )']))
    h2 = c([go['-u ( T + 1 )'][0], go[KB1][0], w.inst('hashun2')], 'syl2anc', '( # ` ( %s u. %s ) ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (I['-u ( T + 1 )'], I[KB1], I['-u ( T + 1 )'], I[KB1]))
    A1_ = '( %s u. %s )' % (I['T'], I['( T + 1 )']); A2_ = '( %s u. %s )' % (I['-u ( T + 1 )'], I[KB1])
    h3 = c([iu1f, iu2f, w.inst('hashun2')], 'syl2anc', '( # ` ( %s u. %s ) ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (A1_, A2_, A1_, A2_))
    geq = w.s([e1, w.s([e2, e3], 'uneq12i', '( %s u. %s ) = ( %s u. %s )' % (IU1, IU2, A1_, A2_))], 'eqtri', '%s = ( %s u. %s )' % (GG, A1_, A2_))
    hg = c([c.a1(w.s([geq], 'fveq2i', '( # ` %s ) = ( # ` ( %s u. %s ) )' % (GG, A1_, A2_)), '( # ` %s ) = ( # ` ( %s u. %s ) )' % (GG, A1_, A2_)), h3], 'eqbrtrd', '( # ` %s ) <_ ( ( # ` %s ) + ( # ` %s ) )' % (GG, A1_, A2_))
    hr = lambda X, fs: c([c([fs, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % X)], 'nn0red', '( # ` %s ) e. RR' % X)
    lv = {'( # ` %s )' % GG: hr(GG, gf), '( # ` %s )' % A1_: hr(A1_, iu1f), '( # ` %s )' % A2_: hr(A2_, iu2f)}
    for K in KS4:
        lv['( # ` %s )' % I[K]] = hr(I[K], go[K][0])
    # 1 <_ L4
    A4 = '( 1 x. ( T + 4 ) )'
    a4r = c([numst(w, A0, '1', 'RR'), c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')], 'remulcld', '%s e. RR' % A4)
    six = lin8(w, A0, [t2], '6 <_ %s' % A4, {'T': tr, A4: a4r}) if False else None
    a4e = c([c([c([tr, numst(w, A0, '4', 'RR')], 'readdcld', '( T + 4 ) e. RR')], 'recnd', '( T + 4 ) e. CC')], 'mullidd', '%s = ( T + 4 )' % A4)
    six = c([lin8(w, A0, [t2], '6 <_ ( T + 4 )', {'T': tr}), c([a4e], 'eqcomd', '( T + 4 ) = %s' % A4)], 'breqtrd', '6 <_ %s' % A4)
    a4p = c([a4r, lin8(w, A0, [six], '0 < %s' % A4, {A4: a4r})], 'elrpd', '%s e. RR+' % A4)
    ere = c.a1(w.s([], 'epr', '_e e. RR+'), '_e e. RR+')
    e3_ = c.a1(w.s([w.s([], 'egt2lt3', '( 2 < _e /\\ _e < 3 )')], 'simpri', '_e < 3'), '_e < 3')
    ele = lin8(w, A0, [e3_, six], '_e <_ %s' % A4, {'_e': c([ere], 'rpred', '_e e. RR'), A4: a4r})
    lg1 = c([c.a1(w.s([], 'loge', '( log ` _e ) = 1'), '( log ` _e ) = 1'), c([ele, c([ere, a4p], 'logled', '( _e <_ %s <-> ( log ` _e ) <_ %s )' % (A4, L4))], 'mpbid', '( log ` _e ) <_ %s' % L4)], 'eqbrtrrd', '1 <_ %s' % L4)
    lv[L4] = c([a4p], 'relogcld', '%s e. RR' % L4)
    hy = [hg, h1, h2, lg1] + [go[K][1] for K in KS4]
    fin = lin8(w, A0, hy, '( # ` %s ) <_ ( ; 1 6 x. %s )' % (GG, L4), lv)
    w.qed([c([gf, grr, fin], '3jca', ante_of(S['ef6gc'])[1])], 'idi', S['ef6gc'])
    return run8(w)



def gen_gd():
    w = W('ef6gd', 'A height ` H e. [ T , T + 1 ] ` at distance ` >_ 1 / ( 4000 log ( T + 4 ) ) ` from the absolute ordinates of the zeros of ` g ` near ` +- T ` ( ~ ef6gc ) is good for ` g ` at ` +- H ` : ` g =/= 0 ` and ` abs ( g-prime / g ) <_ 21000000 log ^ 2 ( T + 4 ) ` on the horizontal lines ( ~ ef6gg ; replaces Lean ` abs_sin_log_two_ge ` and ` norm_gFun_ge_sin ` ).')
    A0 = ante_of(S['ef6gd'])[0]
    c = Ctx(w, A0)
    tr = c.g('T e. RR'); t2 = c.g('2 <_ T'); hin = c.g('H e. %s' % IVT)
    GAPB = '( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - g ) )' % (GAP, L4)
    gall = c.g('A. g e. %s %s' % (GG, GAPB))
    kr = ks_reals(c, tr)
    hr, th, h1 = icc_out(c, 'H', 'T', '( T + 1 )', hin, tr, kr['( T + 1 )'])
    lvh = {'T': tr, 'H': hr}
    ddg = c.a1(w.s([], 'ef2ddg', DD(GF, '1')), DD(GF, '1'))
    aif = aim_facts(w)
    fun = c.a1(w.s([aif, w.inst('ffun')], 'ax-mp', 'Fun %s' % AIM), 'Fun %s' % AIM)
    dm = c.a1(w.s([aif, w.inst('fdm')], 'ax-mp', 'dom %s = CC' % AIM), 'dom %s = CC' % AIM)
    Z = {K: ZSG(K) for K in KS4}
    def zcc(K):
        d = sq_data(w, A0, K, kr[K])
        return c([c.a1(w.s([], 'ssrab2', '%s C_ %s' % (Z[K], SQ(CT(K), R138))), '%s C_ %s' % (Z[K], SQ(CT(K), R138))), c([d['a'], d['b'], w.inst('crectss')], 'syl2anc', '%s C_ CC' % SQ(CT(K), R138))], 'sstrd', '%s C_ CC' % Z[K])
    U1_ = '( %s u. %s )' % (Z['T'], Z['( T + 1 )'])
    U2_ = '( %s u. %s )' % (Z['-u ( T + 1 )'], Z[KB1])
    u1c = c([zcc('T'), zcc('( T + 1 )')], 'unssd', '%s C_ CC' % U1_)
    u2c = c([zcc('-u ( T + 1 )'), zcc(KB1)], 'unssd', '%s C_ CC' % U2_)
    wcc = c([u1c, u2c], 'unssd', '%s C_ CC' % WG4)
    wdm = c([wcc, c([dm], 'eqcomd', 'CC = dom %s' % AIM)], 'sseqtrd', '%s C_ dom %s' % (WG4, AIM))
    def gap_for(UX, sub_w, Ks, sign):
        """( A0 -> A. p e. UX gap ( Hs - Im p ) ) with Hs = H (sign +) or -u H (sign -)"""
        Hs = 'H' if sign > 0 else '-u H'
        Ap = '( %s /\\ p e. %s )' % (A0, UX)
        cp = Ctx(w, Ap)
        Lp = lambda st: lift(w, st, Ap)
        pin = cp([], 'simpr', 'p e. %s' % UX)
        pw = cp([Lp(sub_w), pin], 'sseldd', 'p e. %s' % WG4)
        pim = cp([pw, cp([Lp(fun), Lp(wdm), w.inst('funfvima2')], 'syl2anc', '( p e. %s -> ( %s ` p ) e. %s )' % (WG4, AIM, GG))], 'mpd', '( %s ` p ) e. %s' % (AIM, GG))
        pcc = cp([Lp(wcc), pw], 'sseldd', 'p e. CC')
        av = cp([cp.a1(w.s([], 'imf', 'Im : CC --> RR'), 'Im : CC --> RR'), pcc, w.inst('fvco3')], 'syl2anc', '( %s ` p ) = ( abs ` ( Im ` p ) )' % AIM)
        gp, _ = ral_at(w, Ap, Lp(gall), 'g', '( %s ` p )' % AIM, GAPB, pim)
        gp2 = cp([gp, cp([cp([av], 'oveq2d', '( H - ( %s ` p ) ) = ( H - ( abs ` ( Im ` p ) ) )' % AIM)], 'fveq2d', '( abs ` ( H - ( %s ` p ) ) ) = ( abs ` ( H - ( abs ` ( Im ` p ) ) ) )' % AIM)], 'breqtrd',
                 '( 1 / ( %s x. %s ) ) <_ ( abs ` ( H - ( abs ` ( Im ` p ) ) ) )' % (GAP, L4))
        # sign of Im p on the two squares
        imr = cp([pcc], 'imcld', '( Im ` p ) e. RR')
        def side(K):
            A2 = '( %s /\\ p e. %s )' % (Ap, Z[K])
            d = zs_unpack(w, A2, GF, K, lift(w, kr[K], A2), 'p', w.s([], 'simpr', '( %s -> p e. %s )' % (A2, Z[K])))
            lvd = {k: v for k, v in d['lv'].items() if k not in KS4[1:]}; lvd['T'] = lift(w, tr, A2)
            hy = d['hy'] + [lift(w, t2, A2)]
            if sign > 0:
                return w.s([lin8(w, A2, hy, '0 < ( Im ` p )', lvd)], 'ex', '( %s -> ( p e. %s -> 0 < ( Im ` p ) ) )' % (Ap, Z[K]))
            return w.s([lin8(w, A2, hy, '( Im ` p ) < 0', lvd)], 'ex', '( %s -> ( p e. %s -> ( Im ` p ) < 0 ) )' % (Ap, Z[K]))
        SG = '0 < ( Im ` p )' if sign > 0 else '( Im ` p ) < 0'
        jo = w.s([side(Ks[0]), side(Ks[1])], 'jaod', '( %s -> ( ( p e. %s \\/ p e. %s ) -> %s ) )' % (Ap, Z[Ks[0]], Z[Ks[1]], SG))
        el = cp([pin, cp.a1(w.s([], 'elun', '( p e. %s <-> ( p e. %s \\/ p e. %s ) )' % (UX, Z[Ks[0]], Z[Ks[1]])), '( p e. %s <-> ( p e. %s \\/ p e. %s ) )' % (UX, Z[Ks[0]], Z[Ks[1]]))], 'mpbid', '( p e. %s \\/ p e. %s )' % (Z[Ks[0]], Z[Ks[1]]))
        sg = cp([el, jo], 'mpd', SG)
        hh = Lp(hr)
        if sign > 0:
            ab = cp([imr, lin8(w, Ap, [sg], '0 <_ ( Im ` p )', {'( Im ` p )': imr})], 'absidd', '( abs ` ( Im ` p ) ) = ( Im ` p )')
            e = cp([cp([ab], 'oveq2d', '( H - ( abs ` ( Im ` p ) ) ) = ( H - ( Im ` p ) )')], 'fveq2d', '( abs ` ( H - ( abs ` ( Im ` p ) ) ) ) = ( abs ` ( H - ( Im ` p ) ) )')
        else:
            ab = cp([imr, lin8(w, Ap, [sg], '( Im ` p ) <_ 0', {'( Im ` p )': imr})], 'absnidd', '( abs ` ( Im ` p ) ) = -u ( Im ` p )')
            hc, ic = cp([hh], 'recnd', 'H e. CC'), cp([imr], 'recnd', '( Im ` p ) e. CC')
            cl = Closure(w, Ap, {'H': ('CC', hc), '( Im ` p )': ('CC', ic)}); cl.atom('H'); cl.atom('( Im ` p )')
            r1 = ringeq(w, Ap, '( H - -u ( Im ` p ) )', '-u ( -u H - ( Im ` p ) )', cl)
            e0 = cp([cp([ab], 'oveq2d', '( H - ( abs ` ( Im ` p ) ) ) = ( H - -u ( Im ` p ) )'), r1], 'eqtrd', '( H - ( abs ` ( Im ` p ) ) ) = -u ( -u H - ( Im ` p ) )')
            e = cp([cp([e0], 'fveq2d', '( abs ` ( H - ( abs ` ( Im ` p ) ) ) ) = ( abs ` -u ( -u H - ( Im ` p ) ) )'),
                    cp([cp([cp([hc], 'negcld', '-u H e. CC'), ic], 'subcld', '( -u H - ( Im ` p ) ) e. CC')], 'absnegd', '( abs ` -u ( -u H - ( Im ` p ) ) ) = ( abs ` ( -u H - ( Im ` p ) ) )')], 'eqtrd',
                   '( abs ` ( H - ( abs ` ( Im ` p ) ) ) ) = ( abs ` ( -u H - ( Im ` p ) ) )')
        fin = cp([gp2, e], 'breqtrd', '( 1 / ( %s x. %s ) ) <_ ( abs ` ( %s - ( Im ` p ) ) )' % (GAP, L4, Hs))
        return c([fin], 'ralrimiva', 'A. p e. %s ( 1 / ( %s x. %s ) ) <_ ( abs ` ( %s - ( Im ` p ) ) )' % (UX, GAP, L4, Hs))
    s1 = c.a1(w.s([], 'ssun1', '%s C_ %s' % (U1_, WG4)), '%s C_ %s' % (U1_, WG4))
    s2 = c.a1(w.s([], 'ssun2', '%s C_ %s' % (U2_, WG4)), '%s C_ %s' % (U2_, WG4))
    gtop = gap_for(U1_, s1, ['T', '( T + 1 )'], 1)
    gbot = gap_for(U2_, s2, ['-u ( T + 1 )', KB1], -1)
    ah = c([hr, lin8(w, A0, [th, t2], '0 <_ H', lvh)], 'absidd', '( abs ` H ) = H')
    GT = tsub(S['ef6gg'], {'F': GF, 'A': '1', 'K': 'T'})
    gta, gtc = ante_of(GT)
    top = c([rebuild(w, c, gta, {DD(GF, '1'): ddg, '( abs ` H ) <_ ( T + 1 )': c([ah, h1], 'eqbrtrd', '( abs ` H ) <_ ( T + 1 )'), top_and(gta)[2]: gtop}), w.inst('ef6gg')], 'syl', gtc)
    GB_ = tsub(S['ef6gg'], {'F': GF, 'A': '1', 'K': '-u ( T + 1 )', 'H': '-u H'})
    gba, gbc = ante_of(GB_)
    nh = c([hr], 'renegcld', '-u H e. RR')
    nhin = icc_in(c, '-u H', '-u ( T + 1 )', KB1, nh, kr['-u ( T + 1 )'], kr[KB1], lin8(w, A0, [h1], '-u ( T + 1 ) <_ -u H', lvh), lin8(w, A0, [th], '-u H <_ %s' % KB1, lvh))
    anh = c([c([c([hr], 'recnd', 'H e. CC'), w.inst('absneg')], 'syl', '( abs ` -u H ) = ( abs ` H )'), ah], 'eqtrd', '( abs ` -u H ) = H')
    bot = c([rebuild(w, c, gba, {DD(GF, '1'): ddg, '-u H e. ( -u ( T + 1 ) [,] %s )' % KB1: nhin, '( abs ` -u H ) <_ ( T + 1 )': c([anh, h1], 'eqbrtrd', '( abs ` -u H ) <_ ( T + 1 )'),
                                 '-u ( T + 1 ) e. RR': kr['-u ( T + 1 )'], top_and(gba)[2]: gbot}), w.inst('ef6gg')], 'syl', gbc)
    w.qed([top, bot], 'jca', S['ef6gd'])
    return run8(w)


GENS = {'ef6gc': gen_gc, 'ef6gd': gen_gd}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
