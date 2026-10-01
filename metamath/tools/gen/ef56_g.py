"""Sortie EF56: the zeros of g in one 13/8-square share their ordinate (ef6gz, ef6go)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef56lib import *
from cl import lift, Closure
import congr as _cg
from c8_o import numst
import lin
lin.FASTPATH = True


def gen_gz():
    w = W('ef6gz', 'Two ordinates ` 2 pi n / log 2 ` , ` 2 pi m / log 2 ` of zeros of ` g ` at distance at most ` 13 / 4 ` are equal: ` 2 pi / log 2 > 6 ` ( ~ pigt3 , ~ log2le1 ).')
    A0 = ante_of(S['ef6gz'])[0]
    c = Ctx(w, A0)
    nz = c.g('n e. ZZ'); mz = c.g('m e. ZZ'); ab = c.g('( abs ` ( %s - %s ) ) <_ ( ; 1 3 / 4 )' % (IMN('n'), IMN('m')))
    L = '( log ` 2 )'
    lrp = c([numst(w, A0, '2', 'RR'), c.a1(w.s([], '1lt2', '1 < 2'), '1 < 2')], 'rplogcld', '%s e. RR+' % L)
    lr = c([lrp], 'rpred', '%s e. RR' % L)
    l1 = c.a1(w.s([], 'log2le1', '%s < 1' % L), '%s < 1' % L)
    pi3 = c.a1(w.s([], 'pigt3', '3 < _pi'), '3 < _pi')
    pr = c.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
    nr = c([nz], 'zred', 'n e. RR'); mr = c([mz], 'zred', 'm e. RR')
    def im(n, nr_):
        TN = '( 2 x. ( _pi x. %s ) )' % n
        tr_ = c([numst(w, A0, '2', 'RR'), c([pr, nr_], 'remulcld', '( _pi x. %s ) e. RR' % n)], 'remulcld', '%s e. RR' % TN)
        ar_ = c([tr_, lrp], 'rerpdivcld', '%s e. RR' % IMN(n))
        al = c([c([tr_], 'recnd', '%s e. CC' % TN), c([lrp], 'rpcnd', '%s e. CC' % L), c([lrp], 'rpne0d', '%s =/= 0' % L)], 'divcan1d', '( %s x. %s ) = %s' % (IMN(n), L, TN))
        return ar_, al
    Ar, Al = im('n', nr); Br, Bl = im('m', mr)
    A_, B_ = IMN('n'), IMN('m')
    abr = c([Ar, Br], 'resubcld', '( %s - %s ) e. RR' % (A_, B_))
    ab2 = c([ab, c([abr, numst(w, A0, '( ; 1 3 / 4 )', 'RR')], 'absled', '( ( abs ` ( %s - %s ) ) <_ ( ; 1 3 / 4 ) <-> ( -u ( ; 1 3 / 4 ) <_ ( %s - %s ) /\\ ( %s - %s ) <_ ( ; 1 3 / 4 ) ) )' % (A_, B_, A_, B_, A_, B_))],
            'mpbid', '( -u ( ; 1 3 / 4 ) <_ ( %s - %s ) /\\ ( %s - %s ) <_ ( ; 1 3 / 4 ) )' % (A_, B_, A_, B_))
    lo = c([ab2, w.inst('simpl')], 'syl', '-u ( ; 1 3 / 4 ) <_ ( %s - %s )' % (A_, B_))
    hi = c([ab2, w.inst('simpr')], 'syl', '( %s - %s ) <_ ( ; 1 3 / 4 )' % (A_, B_))
    base = {A_: Ar, B_: Br}
    def half(n, m, nz_, mz_, nr_, mr_, Xr, Yr, Xl, Yl, X, Y):
        """( A0 -> -. n < m ), where X = IMN(n), Y = IMN(m); uses Y - X <_ 13/4"""
        A2 = '( %s /\\ %s < %s )' % (A0, n, m)
        c2 = Ctx(w, A2)
        L2 = lambda st: lift(w, st, A2)
        n1 = c2([c2([L2(nz_), L2(mz_), w.inst('zltp1le')], 'syl2anc', '( %s < %s <-> ( %s + 1 ) <_ %s )' % (n, m, n, m)), c2([], 'simpr', '%s < %s' % (n, m))], 'mpbird' if False else 'x', 'x') if False else None
        n1 = c2([c2([], 'simpr', '%s < %s' % (n, m)), c2([L2(nz_), L2(mz_), w.inst('zltp1le')], 'syl2anc', '( %s < %s <-> ( %s + 1 ) <_ %s )' % (n, m, n, m))], 'mpbid', '( %s + 1 ) <_ %s' % (n, m))
        lvn = {n: L2(nr_), m: L2(mr_)}
        d1 = lin8(w, A2, [n1], '1 <_ ( %s - %s )' % (m, n), lvn)
        DIF = '( %s - %s )' % (Y, X)
        difr = c2([L2(Yr), L2(Xr)], 'resubcld', '%s e. RR' % DIF)
        bnd = lin8(w, A2, [L2(lo)], '%s <_ ( ; 1 3 / 4 )' % DIF, {A_: L2(Ar), B_: L2(Br)}) if X == A_ else lin8(w, A2, [L2(hi)], '%s <_ ( ; 1 3 / 4 )' % DIF, {A_: L2(Ar), B_: L2(Br)})
        XX = '( %s x. %s )' % (DIF, L)
        l0 = c2([L2(lrp)], 'rpge0d', '0 <_ %s' % L)
        u1 = c2([difr, numst(w, A2, '( ; 1 3 / 4 )', 'RR'), L2(lr), l0, bnd], 'lemul1ad', '%s <_ ( ( ; 1 3 / 4 ) x. %s )' % (XX, L))
        e1 = c2([c2([L2(Yr)], 'recnd', '%s e. CC' % Y), c2([L2(Xr)], 'recnd', '%s e. CC' % X), c2([L2(lr)], 'recnd', '%s e. CC' % L)], 'subdird', '%s = ( ( %s x. %s ) - ( %s x. %s ) )' % (XX, Y, L, X, L))
        TM, TN = '( 2 x. ( _pi x. %s ) )' % m, '( 2 x. ( _pi x. %s ) )' % n
        e2 = c2([e1, c2([L2(Yl), L2(Xl)], 'oveq12d', '( ( %s x. %s ) - ( %s x. %s ) ) = ( %s - %s )' % (Y, L, X, L, TM, TN))], 'eqtrd', '%s = ( %s - %s )' % (XX, TM, TN))
        MN = '( %s - %s )' % (m, n)
        u2 = c2([numst(w, A2, '1', 'RR'), c2([L2(mr_), L2(nr_)], 'resubcld', '%s e. RR' % MN), L2(pr), c2([L2(pr), lin8(w, A2, [L2(pi3)], '0 <_ _pi', {'_pi': L2(pr)})], 'x', 'x') if False else lin8(w, A2, [L2(pi3)], '0 <_ _pi', {'_pi': L2(pr)}), d1],
                'lemul2ad', '( _pi x. 1 ) <_ ( _pi x. %s )' % MN)
        u3 = c2([c2([L2(pr)], 'recnd', '_pi e. CC'), c2([L2(mr_)], 'recnd', '%s e. CC' % m), c2([L2(nr_)], 'recnd', '%s e. CC' % n)], 'subdid', '( _pi x. %s ) = ( ( _pi x. %s ) - ( _pi x. %s ) )' % (MN, m, n))
        u4 = c2([c2([L2(pr)], 'recnd', '_pi e. CC')], 'mulridd', '( _pi x. 1 ) = _pi')
        PM, PN, PMN = '( _pi x. %s )' % m, '( _pi x. %s )' % n, '( _pi x. %s )' % MN
        xxr = c2([difr, L2(lr)], 'remulcld', '%s e. RR' % XX)
        lv = {XX: xxr, PM: c2([L2(pr), L2(mr_)], 'remulcld', '%s e. RR' % PM), PN: c2([L2(pr), L2(nr_)], 'remulcld', '%s e. RR' % PN), PMN: c2([L2(pr), c2([L2(mr_), L2(nr_)], 'resubcld', '%s e. RR' % MN)], 'remulcld', '%s e. RR' % PMN),
              '_pi': L2(pr), '( _pi x. 1 )': c2([L2(pr), numst(w, A2, '1', 'RR')], 'remulcld', '( _pi x. 1 ) e. RR'), L: L2(lr)}
        g1 = lin8(w, A2, [e2, u2, u3, u4, L2(pi3)], '6 < %s' % XX, lv)
        g2 = lin8(w, A2, [u1, L2(l1)], '%s < 6' % XX, lv)
        ng = c2([xxr, numst(w, A2, '6', 'RR'), g2], 'ltnsymd', '-. 6 < %s' % XX)
        return c([g1, ng], 'pm2.65da', '-. %s < %s' % (n, m))
    h1 = half('n', 'm', nz, mz, nr, mr, Ar, Br, Al, Bl, A_, B_)
    h2 = half('m', 'n', mz, nz, mr, nr, Br, Ar, Bl, Al, B_, A_)
    tri = c([nr, mr, w.inst('lttri3')], 'syl2anc', '( n = m <-> ( -. n < m /\\ -. m < n ) )')
    w.qed([c([h1, h2], 'jca', '( -. n < m /\\ -. m < n )'), tri], 'mpbird', S['ef6gz'])
    return run8(w)


def gen_go():
    from ef2lib import zs_unpack
    w = W('ef6go', 'The zeros of ` g ( s ) = 1 - 2 ^ ( 1 - s ) ` in one ` 13 / 8 ` -square about ` 2 + i K ` have one absolute ordinate at most ( ~ ef5g0 , ~ ef6gz ): the image under ` abs o. Im ` is finite of size at most 1.')
    A0 = 'K e. RR'
    c = Ctx(w, A0)
    kr = c([], 'id', A0)
    Z = ZSG('K')
    IMG = '( %s " %s )' % (AIM, Z)
    ddg = w.s([w.s([], 'ef2ddg', DD(GF, '1'))], 'a1i', '( %s -> %s )' % (A0, DD(GF, '1')))
    zc = tsub(ante_of(stmt('ef2zs'))[1], {'F': GF, 'A': '1', 'T': 'K'})
    zfin = c([c([c([ddg, kr], 'jca', '( %s /\\ K e. RR )' % DD(GF, '1')), w.inst('ef2zs')], 'syl', zc), w.inst('simp1')], 'syl', '%s e. Fin' % Z)
    imcc = w.s([w.s([], 'imf', 'Im : CC --> RR'), w.s([], 'ax-resscn', 'RR C_ CC'), w.inst('fss')], 'mp2an', 'Im : CC --> CC')
    aif = w.s([w.s([], 'absf', 'abs : CC --> RR'), imcc, w.inst('fco')], 'mp2an', '%s : CC --> RR' % AIM)
    fun = c.a1(w.s([aif, w.inst('ffun')], 'ax-mp', 'Fun %s' % AIM), 'Fun %s' % AIM)
    ifin = c([fun, zfin, w.inst('imafi')], 'syl2anc', '%s e. Fin' % IMG)
    def key(C, pin, qin, p, q):
        """( C -> ( Im ` p ) = ( Im ` q ) ) for p, q e. Z"""
        cc_ = Ctx(w, C)
        LC = lambda st: lift(w, st, C)
        def pt(x, xin, n):
            d = zs_unpack(w, C, GF, 'K', LC(kr), x, xin)
            rx = cc_([d['cc']], 'recld', '( Re ` %s ) e. RR' % x)
            lvx = dict(d['lv'])
            r0 = lin8(w, C, d['hy'], '0 < ( Re ` %s )' % x, lvx)
            xh = cc_([cc_([d['cc'], r0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (x, x)), cc_([cc_.a1(w.s([], '0re', '0 e. RR'), '0 e. RR'), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (x, HP0, x, x))],
                     'mpbird', '%s e. %s' % (x, HP0))
            g0 = cc_([d['fz'], cc_([xh, w.inst('ef5g0')], 'syl', tsub(S['ef5g0'], {'S': x, 'n': n}).split(' -> ', 1)[1][:-2])], 'mpbid', 'E. %s e. ZZ %s = %s' % (n, x, GFZ(n)))
            lo = lin8(w, C, d['hy'], '( K - ( ; 1 3 / 8 ) ) <_ ( Im ` %s )' % x, lvx)
            hi = lin8(w, C, d['hy'], '( Im ` %s ) <_ ( K + ( ; 1 3 / 8 ) )' % x, lvx)
            return g0, lo, hi, lvx['( Im ` %s )' % x]
        gp, plo, phi, pim = pt(p, pin, 'n')
        gq, qlo, qhi, qim = pt(q, qin, 'm')
        ex = cc_([gp, gq], 'jca', '( E. n e. ZZ %s = %s /\\ E. m e. ZZ %s = %s )' % (p, GFZ('n'), q, GFZ('m')))
        EXB = 'E. n e. ZZ E. m e. ZZ ( %s = %s /\\ %s = %s )' % (p, GFZ('n'), q, GFZ('m'))
        exb = cc_([ex, cc_.a1(w.s([], 'reeanv', '( %s <-> ( E. n e. ZZ %s = %s /\\ E. m e. ZZ %s = %s ) )' % (EXB, p, GFZ('n'), q, GFZ('m'))),
                            '( %s <-> ( E. n e. ZZ %s = %s /\\ E. m e. ZZ %s = %s ) )' % (EXB, p, GFZ('n'), q, GFZ('m')))], 'mpbird', EXB)
        C2 = '( ( %s /\\ ( n e. ZZ /\\ m e. ZZ ) ) /\\ ( %s = %s /\\ %s = %s ) )' % (C, p, GFZ('n'), q, GFZ('m'))
        c2 = Ctx(w, C2)
        L2 = lambda st: lift(w, st, C2)
        nz = c2.g('n e. ZZ'); mz = c2.g('m e. ZZ'); pe = c2.g('%s = %s' % (p, GFZ('n'))); qe = c2.g('%s = %s' % (q, GFZ('m')))
        pr = c2.a1(w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
        lrp = c2([numst(w, C2, '2', 'RR'), c2.a1(w.s([], '1lt2', '1 < 2'), '1 < 2')], 'rplogcld', '( log ` 2 ) e. RR+')
        def imv(x, xe, n, nzs):
            nr_ = c2([nzs], 'zred', '%s e. RR' % n)
            TN = '( 2 x. ( _pi x. %s ) )' % n
            ar_ = c2([c2([numst(w, C2, '2', 'RR'), c2([pr, nr_], 'remulcld', '( _pi x. %s ) e. RR' % n)], 'remulcld', '%s e. RR' % TN), lrp], 'rerpdivcld', '%s e. RR' % IMN(n))
            e = c2([c2([xe], 'fveq2d', '( Im ` %s ) = ( Im ` %s )' % (x, GFZ(n))), c2([numst(w, C2, '1', 'RR'), ar_], 'crimd', '( Im ` %s ) = %s' % (GFZ(n), IMN(n)))], 'eqtrd', '( Im ` %s ) = %s' % (x, IMN(n)))
            return e, ar_
        ip, ipr = imv(p, pe, 'n', nz); iq, iqr = imv(q, qe, 'm', mz)
        D = '( %s - %s )' % (IMN('n'), IMN('m'))
        lvd = {IMN('n'): ipr, IMN('m'): iqr, '( Im ` %s )' % p: L2(pim), '( Im ` %s )' % q: L2(qim), 'K': L2(kr)}
        d1 = lin8(w, C2, [ip, iq, L2(plo), L2(phi), L2(qlo), L2(qhi)], '-u ( ; 1 3 / 4 ) <_ %s' % D, lvd)
        d2 = lin8(w, C2, [ip, iq, L2(plo), L2(phi), L2(qlo), L2(qhi)], '%s <_ ( ; 1 3 / 4 )' % D, lvd)
        dr = c2([ipr, iqr], 'resubcld', '%s e. RR' % D)
        ab = c2([c2([d1, d2], 'jca', '( -u ( ; 1 3 / 4 ) <_ %s /\\ %s <_ ( ; 1 3 / 4 ) )' % (D, D)), c2([dr, numst(w, C2, '( ; 1 3 / 4 )', 'RR')], 'absled', '( ( abs ` %s ) <_ ( ; 1 3 / 4 ) <-> ( -u ( ; 1 3 / 4 ) <_ %s /\\ %s <_ ( ; 1 3 / 4 ) ) )' % (D, D, D))],
                'mpbird', '( abs ` %s ) <_ ( ; 1 3 / 4 )' % D)
        nm = c2([c2([c2([nz, mz], 'jca', '( n e. ZZ /\\ m e. ZZ )'), ab], 'jca', ante_of(S['ef6gz'])[0]), w.inst('ef6gz')], 'syl', 'n = m')
        fin2 = c2([c2([ip, c2([nm], 'x', 'x') if False else c2([c2([c2([c2([nm], 'oveq2d', '( _pi x. n ) = ( _pi x. m )')], 'oveq2d', '( 2 x. ( _pi x. n ) ) = ( 2 x. ( _pi x. m ) )')], 'oveq1d', '%s = %s' % (IMN('n'), IMN('m')))], 'idi', '%s = %s' % (IMN('n'), IMN('m')))],
                      'eqtrd', '( Im ` %s ) = %s' % (p, IMN('m'))), c2([iq], 'eqcomd', '%s = ( Im ` %s )' % (IMN('m'), q))], 'eqtrd', '( Im ` %s ) = ( Im ` %s )' % (p, q))
        el = w.s([w.s([fin2], 'ex', '( ( %s /\\ ( n e. ZZ /\\ m e. ZZ ) ) -> ( ( %s = %s /\\ %s = %s ) -> ( Im ` %s ) = ( Im ` %s ) ) )' % (C, p, GFZ('n'), q, GFZ('m'), p, q))], 'rexlimdvva',
                 '( %s -> ( %s -> ( Im ` %s ) = ( Im ` %s ) ) )' % (C, EXB, p, q))
        return cc_([exb, el], 'mpd', '( Im ` %s ) = ( Im ` %s )' % (p, q))
    # all elements of the image are equal
    Cab = '( %s /\\ ( a e. %s /\\ b e. %s ) )' % (A0, IMG, IMG)
    ca = Ctx(w, Cab)
    fa = ca([lift(w, fun, Cab), ca.g('a e. %s' % IMG), w.inst('fvelima')], 'syl2anc', 'E. p e. %s ( %s ` p ) = a' % (Z, AIM))
    fb = ca([lift(w, fun, Cab), ca.g('b e. %s' % IMG), w.inst('fvelima')], 'syl2anc', 'E. q e. %s ( %s ` q ) = b' % (Z, AIM))
    EXB = 'E. p e. %s E. q e. %s ( ( %s ` p ) = a /\\ ( %s ` q ) = b )' % (Z, Z, AIM, AIM)
    exb = ca([ca([fa, fb], 'jca', '( E. p e. %s ( %s ` p ) = a /\\ E. q e. %s ( %s ` q ) = b )' % (Z, AIM, Z, AIM)),
              ca.a1(w.s([], 'reeanv', '( %s <-> ( E. p e. %s ( %s ` p ) = a /\\ E. q e. %s ( %s ` q ) = b ) )' % (EXB, Z, AIM, Z, AIM)), '( %s <-> ( E. p e. %s ( %s ` p ) = a /\\ E. q e. %s ( %s ` q ) = b ) )' % (EXB, Z, AIM, Z, AIM))],
             'mpbird', EXB)
    Cpq = '( %s /\\ ( p e. %s /\\ q e. %s ) )' % (Cab, Z, Z)
    Cpq2 = '( %s /\\ ( ( %s ` p ) = a /\\ ( %s ` q ) = b ) )' % (Cpq, AIM, AIM)
    cq = Ctx(w, Cpq2)
    pin = cq.g('p e. %s' % Z); qin = cq.g('q e. %s' % Z)
    k = key(Cpq2, pin, qin, 'p', 'q')
    def aiv(x, xin):
        xcc = cq([lift(w, cq([pin if x == 'p' else qin], 'idi', '%s e. %s' % (x, Z)), Cpq2), cq.a1(w.s([], 'x', 'x'), 'x') if False else None][0:1], 'idi', '%s e. %s' % (x, Z))
        d = zs_unpack(w, Cpq2, GF, 'K', lift(w, kr, Cpq2), x, xin)
        return cq([cq.a1(w.s([], 'imf', 'Im : CC --> RR'), 'Im : CC --> RR'), d['cc'], w.inst('fvco3')], 'syl2anc', '( %s ` %s ) = ( abs ` ( Im ` %s ) )' % (AIM, x, x))
    ap_ = aiv('p', pin); aq_ = aiv('q', qin)
    ab_ = cq([cq([cq([cq.g('( %s ` p ) = a' % AIM)], 'eqcomd', 'a = ( %s ` p )' % AIM), ap_], 'eqtrd', 'a = ( abs ` ( Im ` p ) )'),
              cq([cq([k], 'fveq2d', '( abs ` ( Im ` p ) ) = ( abs ` ( Im ` q ) )'), cq([aq_], 'eqcomd', '( abs ` ( Im ` q ) ) = ( %s ` q )' % AIM)], 'eqtrd', '( abs ` ( Im ` p ) ) = ( %s ` q )' % AIM)],
             'eqtrd', 'a = ( %s ` q )' % AIM)
    ab2 = cq([ab_, cq.g('( %s ` q ) = b' % AIM)], 'eqtrd', 'a = b')
    el = w.s([w.s([ab2], 'ex', '( %s -> ( ( ( %s ` p ) = a /\\ ( %s ` q ) = b ) -> a = b ) )' % (Cpq, AIM, AIM))], 'rexlimdvva', '( %s -> ( %s -> a = b ) )' % (Cab, EXB))
    eab = ca([exb, el], 'mpd', 'a = b')
    nab = ca([eab, ca.a1(w.s([], 'nne', '( -. a =/= b <-> a = b )'), '( -. a =/= b <-> a = b )')], 'mpbird', '-. a =/= b')
    all_ = c([nab], 'ralrimivva', 'A. a e. %s A. b e. %s -. a =/= b' % (IMG, IMG))
    nex = c([all_, c.a1(w.s([], 'ralnex2', '( A. a e. %s A. b e. %s -. a =/= b <-> -. E. a e. %s E. b e. %s a =/= b )' % (IMG, IMG, IMG, IMG)),
                        '( A. a e. %s A. b e. %s -. a =/= b <-> -. E. a e. %s E. b e. %s a =/= b )' % (IMG, IMG, IMG, IMG))], 'mpbid', '-. E. a e. %s E. b e. %s a =/= b' % (IMG, IMG))
    A1 = '( %s /\\ 1 < ( # ` %s ) )' % (A0, IMG)
    c1 = Ctx(w, A1)
    hg = c1([c1([lift(w, ifin, A1)], 'elexd', '%s e. _V' % IMG), c1([], 'simpr', '1 < ( # ` %s )' % IMG), w.inst('hashgt12el')], 'syl2anc', 'E. a e. %s E. b e. %s a =/= b' % (IMG, IMG))
    n1 = c([hg, nex], 'pm2.65da' if False else 'x', 'x') if False else None
    n1 = c([hg, lift(w, nex, A1) if False else None][0:1], 'x', 'x') if False else None
    n1 = c([hg, c([nex], 'adantr' if False else 'x', 'x')], 'x', 'x') if False else None
    nlt = c([hg, w.s([nex], 'adantr', '( %s -> -. E. a e. %s E. b e. %s a =/= b )' % (A1, IMG, IMG))], 'pm2.65da', '-. 1 < ( # ` %s )' % IMG)
    hr = c([c([ifin, w.inst('hashcl')], 'syl', '( # ` %s ) e. NN0' % IMG)], 'nn0red', '( # ` %s ) e. RR' % IMG)
    le = c([nlt, c([hr, numst(w, A0, '1', 'RR')], 'lenltd', '( ( # ` %s ) <_ 1 <-> -. 1 < ( # ` %s ) )' % (IMG, IMG))], 'mpbird', '( # ` %s ) <_ 1' % IMG)
    w.qed([ifin, le], 'jca', S['ef6go'])
    return run8(w)


GENS = {'ef6gz': gen_gz, 'ef6go': gen_go}
if __name__ == '__main__':
    for f in (sys.argv[1:] or list(GENS)):
        GENS[f]()
