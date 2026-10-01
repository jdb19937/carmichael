"""ZL3b E4: the transform of the Gaussian in the rotated plane (zl3ftw).
`MM_DB=sorties/zl3b.mm python3 tools/gen/zl3b_e4.py [LABEL...]`."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from zl3blib import *
from zl3b_d1 import ante_of
from zl3b_d2 import cst
from zl3b_e1 import seg_pre
from zl3b_e3 import fvm, HOLt, mpt_rw
import lin, congr

only = sys.argv[1:]
S = STATEMENTS


def gfbody(U, A, B, Pe, v):
    return '( ( ( %s + %s ) ^ %s ) x. ( exp ` -u ( ( _pi x. %s ) x. ( ( %s + %s ) ^ 2 ) ) ) )' % (v, B, Pe, U, v, A)


def gfv(w, A_, U, A, B, Pe, Z, zc, g, v='y'):
    """( A_ -> ( GF ` Z ) = body(Z) )"""
    st, val = fvm(w, A_, v, gfbody(U, A, B, Pe, v), Z, zc, g)
    assert val == gfbody(U, A, B, Pe, Z), (val, gfbody(U, A, B, Pe, Z))
    return st


def p_nn0(w, A_, pp):
    """( A_ -> P e. NN0 ) from pp: ( A_ -> P e. { 0 , 1 } )"""
    A0 = '( %s /\\ P = 0 )' % A_; A1 = '( %s /\\ P = 1 )' % A_
    return w.s([w.s([w.s([], 'simpr', '( %s -> P = 0 )' % A0), cst(w, A0, '0nn0', '0 e. NN0')], 'eqeltrd', '( %s -> P e. NN0 )' % A0),
                w.s([w.s([], 'simpr', '( %s -> P = 1 )' % A1), cst(w, A1, '1nn0', '1 e. NN0')], 'eqeltrd', '( %s -> P e. NN0 )' % A1),
                w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % A_)], 'mpjaodan', '( %s -> P e. NN0 )' % A_)


def hol_gf(w, A_, U, A, B, Pe, uc, pn, ac, bc):
    FG = GF(U, A, B, Pe)
    sub = STATEMENTS['zl3hol']
    h = D(w, A_, 'syl', [w.s([w.s([uc, pn], 'jca', '( %s -> ( %s e. CC /\\ %s e. NN0 ) )' % (A_, U, Pe)), w.s([ac, bc], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (A_, A, B))], 'jca',
                             '( %s -> ( ( %s e. CC /\\ %s e. NN0 ) /\\ ( %s e. CC /\\ %s e. CC ) ) )' % (A_, U, Pe, A, B)), w.inst('zl3hol')], HOLt(FG))
    return w.s([h], 'simpld', '( %s -> %s e. ( CC -cn-> CC ) )' % (A_, FG))


# ---------------------------------------------------------------- zl3ftw
if __name__ == '__main__' and (not only or 'zl3ftw' in only):
    w = W('zl3ftw', 'The Gaussian ` ( w + K ) ^ P e ^ ( pi T w ^ 2 ) ` integrates along the imaginary axis to ` K ^ P C0 / sqrt T `.')
    g = congr.StepGen('m')
    ph, concl = ante_of(S['zl3ftw'])
    tp = w.s([], 'simp1', '( %s -> T e. RR+ )' % ph); pp = w.s([], 'simp2', '( %s -> P e. { 0 , 1 } )' % ph); kr = w.s([], 'simp3', '( %s -> K e. RR )' % ph)
    tc = D(w, ph, 'rpcnd', [tp], 'T e. CC'); ntc = D(w, ph, 'negcld', [tc], '-u T e. CC'); kc = D(w, ph, 'recnd', [kr], 'K e. CC')
    z0 = cst(w, ph, '0cn', '0 e. CC')
    pn = p_nn0(w, ph, pp)
    OM, OD, PT_ = GF('-u T', '0', 'K', 'P', 'w'), GF('-u T', '0', '0', '1', 'w'), GF('-u T', '0', '0', '0', 'w')
    SQ = '( sqrt ` T )'
    GL1 = '( y e. CC |-> ( %s ` ( %s x. y ) ) )' % (PS1, SQ)
    def hol_w(U, A, B, Pe, uc_, pn_, ac_, bc_):
        cy = hol_gf(w, ph, U, A, B, Pe, uc_, pn_, ac_, bc_)
        bw = lambda v: gfbody(U, A, B, Pe, v)
        ex = mpt_rw(w, ph, 'y', bw, 'w', bw, lambda Av: w.s([], 'eqidd', '( %s -> %s = %s )' % (Av, bw('y'), bw('y'))), g)
        return D(w, ph, 'mpbid', [cy, D(w, ph, 'eleq1d', [ex], '( %s e. ( CC -cn-> CC ) <-> %s e. ( CC -cn-> CC ) )' % (GF(U, A, B, Pe), GF(U, A, B, Pe, 'w')))], '%s e. ( CC -cn-> CC )' % GF(U, A, B, Pe, 'w'))
    omc = hol_w('-u T', '0', 'K', 'P', ntc, pn, z0, kc)
    odc = hol_w('-u T', '0', '0', '1', ntc, cst(w, ph, '1nn0', '1 e. NN0'), z0, z0)
    ptc = hol_w('-u T', '0', '0', '0', ntc, cst(w, ph, '0nn0', '0 e. NN0'), z0, z0)
    n1c = cst(w, ph, 'neg1cn', '-u 1 e. CC')
    ps1y = hol_gf(w, ph, '-u 1', '0', '0', '0', n1c, cst(w, ph, '0nn0', '0 e. NN0'), z0, z0)
    b1_ = lambda v: gfbody('-u 1', '0', '0', '0', v)
    exy = mpt_rw(w, ph, 'y', b1_, 'x', b1_, lambda Av: w.s([], 'eqidd', '( %s -> %s = %s )' % (Av, b1_('y'), b1_('y'))), g)
    ps1c = D(w, ph, 'eleqtrd', [ps1y, D(w, ph, 'eqidd', [], '( CC -cn-> CC ) = ( CC -cn-> CC )')], 'x') if False else \
        D(w, ph, 'mpbid', [ps1y, D(w, ph, 'eleq1d', [exy], '( %s e. ( CC -cn-> CC ) <-> %s e. ( CC -cn-> CC ) )' % (GF('-u 1', '0', '0', '0'), PS1))], '%s e. ( CC -cn-> CC )' % PS1)
    E = lambda U, v: '( exp ` -u ( ( _pi x. %s ) x. ( ( %s + 0 ) ^ 2 ) ) )' % (U, v)
    sqp = D(w, ph, 'rpsqrtcld', [tp], '%s e. RR+' % SQ); sqc = D(w, ph, 'rpcnd', [sqp], '%s e. CC' % SQ)
    sq2 = D(w, ph, 'syl2anc', [D(w, ph, 'rpred', [tp], 'T e. RR'), D(w, ph, 'rpge0d', [tp], '0 <_ T'), w.inst('resqrtth')], '( %s ^ 2 ) = T' % SQ)
    # pointwise: PT_ ` u = GL1 ` u
    Au = '( %s /\\ u e. CC )' % ph
    uc = w.s([], 'simpr', '( %s -> u e. CC )' % Au)
    L1 = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (Au, f))
    pv = gfv(w, Au, '-u T', '0', '0', '0', 'u', uc, g, 'w')
    SU = '( %s x. u )' % SQ
    suc = D(w, Au, 'mulcld', [L1(sqc, '%s e. CC' % SQ), uc], '%s e. CC' % SU)
    ev_ = fvm(w, Au, 'y', '( %s ` ( %s x. y ) )' % (PS1, SQ), 'u', uc, g)[0]
    pv1 = gfv(w, Au, '-u 1', '0', '0', '0', SU, suc, g, 'x')
    u0 = D(w, Au, 'addridd', [uc], '( u + 0 ) = u'); su0 = D(w, Au, 'addridd', [suc], '( %s + 0 ) = %s' % (SU, SU))
    one_a = D(w, Au, 'exp0d', [D(w, Au, 'addcld', [uc, L1(z0, '0 e. CC')], '( u + 0 ) e. CC')], '( ( u + 0 ) ^ 0 ) = 1')
    one_b = D(w, Au, 'exp0d', [D(w, Au, 'addcld', [suc, L1(z0, '0 e. CC')], '( %s + 0 ) e. CC' % SU)], '( ( %s + 0 ) ^ 0 ) = 1' % SU)
    # ( pi x. -u 1 ) x. ( ( SU + 0 ) ^ 2 ) = ( pi x. -u T ) x. ( ( u + 0 ) ^ 2 )
    pic = cst(w, Au, 'picn', '_pi e. CC'); u2 = D(w, Au, 'sqcld', [uc], '( u ^ 2 ) e. CC')
    a1 = D(w, Au, 'eqtrd', [D(w, Au, 'oveq1d', [su0], '( ( %s + 0 ) ^ 2 ) = ( %s ^ 2 )' % (SU, SU)), D(w, Au, 'sqmuld', [L1(sqc, '%s e. CC' % SQ), uc], '( %s ^ 2 ) = ( ( %s ^ 2 ) x. ( u ^ 2 ) )' % (SU, SQ))],
           '( ( %s + 0 ) ^ 2 ) = ( ( %s ^ 2 ) x. ( u ^ 2 ) )' % (SU, SQ))
    a2 = D(w, Au, 'eqtrd', [a1, D(w, Au, 'oveq1d', [L1(sq2, '( %s ^ 2 ) = T' % SQ)], '( ( %s ^ 2 ) x. ( u ^ 2 ) ) = ( T x. ( u ^ 2 ) )' % SQ)], '( ( %s + 0 ) ^ 2 ) = ( T x. ( u ^ 2 ) )' % SU)
    tc1 = L1(tc, 'T e. CC'); n1c1 = cst(w, Au, 'neg1cn', '-u 1 e. CC')
    a3 = D(w, Au, 'eqtrd', [D(w, Au, 'oveq2d', [a2], '( ( _pi x. -u 1 ) x. ( ( %s + 0 ) ^ 2 ) ) = ( ( _pi x. -u 1 ) x. ( T x. ( u ^ 2 ) ) )' % SU),
                            D(w, Au, 'eqcomd', [D(w, Au, 'mulassd', [D(w, Au, 'mulcld', [pic, n1c1], '( _pi x. -u 1 ) e. CC'), tc1, u2], '( ( ( _pi x. -u 1 ) x. T ) x. ( u ^ 2 ) ) = ( ( _pi x. -u 1 ) x. ( T x. ( u ^ 2 ) ) )')],
                              '( ( _pi x. -u 1 ) x. ( T x. ( u ^ 2 ) ) ) = ( ( ( _pi x. -u 1 ) x. T ) x. ( u ^ 2 ) )')], '( ( _pi x. -u 1 ) x. ( ( %s + 0 ) ^ 2 ) ) = ( ( ( _pi x. -u 1 ) x. T ) x. ( u ^ 2 ) )' % SU)
    a4 = D(w, Au, 'eqtrd', [D(w, Au, 'mulassd', [pic, n1c1, tc1], '( ( _pi x. -u 1 ) x. T ) = ( _pi x. ( -u 1 x. T ) )'),
                            D(w, Au, 'oveq2d', [D(w, Au, 'mulm1d', [tc1], '( -u 1 x. T ) = -u T')], '( _pi x. ( -u 1 x. T ) ) = ( _pi x. -u T )')], '( ( _pi x. -u 1 ) x. T ) = ( _pi x. -u T )')
    a5 = D(w, Au, 'eqtrd', [a3, D(w, Au, 'oveq12d', [a4, D(w, Au, 'eqcomd', [D(w, Au, 'oveq1d', [u0], '( ( u + 0 ) ^ 2 ) = ( u ^ 2 )')], '( u ^ 2 ) = ( ( u + 0 ) ^ 2 )')],
                                                  '( ( ( _pi x. -u 1 ) x. T ) x. ( u ^ 2 ) ) = ( ( _pi x. -u T ) x. ( ( u + 0 ) ^ 2 ) )')],
            '( ( _pi x. -u 1 ) x. ( ( %s + 0 ) ^ 2 ) ) = ( ( _pi x. -u T ) x. ( ( u + 0 ) ^ 2 ) )' % SU)
    ee = D(w, Au, 'fveq2d', [D(w, Au, 'negeqd', [a5], '-u ( ( _pi x. -u 1 ) x. ( ( %s + 0 ) ^ 2 ) ) = -u ( ( _pi x. -u T ) x. ( ( u + 0 ) ^ 2 ) )' % SU)], '%s = %s' % (E('-u 1', SU), E('-u T', 'u')))
    b1 = D(w, Au, 'oveq12d', [D(w, Au, 'eqtr4d', [one_b, one_a], '( ( %s + 0 ) ^ 0 ) = ( ( u + 0 ) ^ 0 )' % SU), ee], '%s = %s' % (gfbody('-u 1', '0', '0', '0', SU), gfbody('-u T', '0', '0', '0', 'u')))
    ptgl = D(w, Au, 'eqtr4d', [pv, D(w, Au, 'eqtrd', [D(w, Au, 'eqtrd', [ev_, pv1], '( %s ` u ) = %s' % (GL1, gfbody('-u 1', '0', '0', '0', SU))), b1], '( %s ` u ) = %s' % (GL1, gfbody('-u T', '0', '0', '0', 'u')))],
             '( %s ` u ) = ( %s ` u )' % (PT_, GL1))
    # P = 1: OM ` u = ( K x. ( PT_ ` u ) ) + ( OD ` u ) ;  P = 0: OM ` u = PT_ ` u
    Au1 = '( ( %s /\\ P = 1 ) /\\ u e. CC )' % ph; Au0 = '( ( %s /\\ P = 0 ) /\\ u e. CC )' % ph
    def pw(Ac, k):
        uc_ = w.s([], 'simpr', '( %s -> u e. CC )' % Ac)
        pe = w.s([], 'simplr', '( %s -> P = %s )' % (Ac, k))
        z0_ = cst(w, Ac, '0cn', '0 e. CC'); kc_ = w.s([kc], 'ad2antrr', '( %s -> K e. CC )' % Ac)
        vom = gfv(w, Ac, '-u T', '0', 'K', 'P', 'u', uc_, g, 'w'); vpt = gfv(w, Ac, '-u T', '0', '0', '0', 'u', uc_, g, 'w')
        e_ = E('-u T', 'u')
        ec_ = D(w, Ac, 'efcld', [D(w, Ac, 'negcld', [D(w, Ac, 'mulcld', [D(w, Ac, 'mulcld', [cst(w, Ac, 'picn', '_pi e. CC'), D(w, Ac, 'negcld', [w.s([tc], 'ad2antrr', '( %s -> T e. CC )' % Ac)], '-u T e. CC')], '( _pi x. -u T ) e. CC'),
                                                                        D(w, Ac, 'sqcld', [D(w, Ac, 'addcld', [uc_, z0_], '( u + 0 ) e. CC')], '( ( u + 0 ) ^ 2 ) e. CC')], '( ( _pi x. -u T ) x. ( ( u + 0 ) ^ 2 ) ) e. CC')],
                                                  '-u ( ( _pi x. -u T ) x. ( ( u + 0 ) ^ 2 ) ) e. CC')], '%s e. CC' % e_)
        uk = D(w, Ac, 'addcld', [uc_, kc_], '( u + K ) e. CC'); u0_ = D(w, Ac, 'addcld', [uc_, z0_], '( u + 0 ) e. CC')
        o0 = D(w, Ac, 'exp0d', [u0_], '( ( u + 0 ) ^ 0 ) = 1')
        pt1 = D(w, Ac, 'eqtrd', [vpt, D(w, Ac, 'eqtrd', [D(w, Ac, 'oveq1d', [o0], '( ( ( u + 0 ) ^ 0 ) x. %s ) = ( 1 x. %s )' % (e_, e_)), D(w, Ac, 'mullidd', [ec_], '( 1 x. %s ) = %s' % (e_, e_))],
                                                          '( ( ( u + 0 ) ^ 0 ) x. %s ) = %s' % (e_, e_))], '( %s ` u ) = %s' % (PT_, e_))
        if k == '0':
            om1 = D(w, Ac, 'eqtrd', [D(w, Ac, 'oveq2d', [pe], '( ( u + K ) ^ P ) = ( ( u + K ) ^ 0 )'), D(w, Ac, 'exp0d', [uk], '( ( u + K ) ^ 0 ) = 1')], '( ( u + K ) ^ P ) = 1')
            om2 = D(w, Ac, 'eqtrd', [vom, D(w, Ac, 'eqtrd', [D(w, Ac, 'oveq1d', [om1], '( ( ( u + K ) ^ P ) x. %s ) = ( 1 x. %s )' % (e_, e_)), D(w, Ac, 'mullidd', [ec_], '( 1 x. %s ) = %s' % (e_, e_))],
                                                              '( ( ( u + K ) ^ P ) x. %s ) = %s' % (e_, e_))], '( %s ` u ) = %s' % (OM, e_))
            return D(w, Ac, 'eqtr4d', [om2, pt1], '( %s ` u ) = ( %s ` u )' % (OM, PT_))
        vod = gfv(w, Ac, '-u T', '0', '0', '1', 'u', uc_, g, 'w')
        om1 = D(w, Ac, 'eqtrd', [D(w, Ac, 'oveq2d', [pe], '( ( u + K ) ^ P ) = ( ( u + K ) ^ 1 )'), D(w, Ac, 'exp1d', [uk], '( ( u + K ) ^ 1 ) = ( u + K )')], '( ( u + K ) ^ P ) = ( u + K )')
        om2 = D(w, Ac, 'eqtrd', [vom, D(w, Ac, 'eqtrd', [D(w, Ac, 'oveq1d', [om1], '( ( ( u + K ) ^ P ) x. %s ) = ( ( u + K ) x. %s )' % (e_, e_)), D(w, Ac, 'adddird', [uc_, kc_, ec_], '( ( u + K ) x. %s ) = ( ( u x. %s ) + ( K x. %s ) )' % (e_, e_, e_))],
                                                          '( ( ( u + K ) ^ P ) x. %s ) = ( ( u x. %s ) + ( K x. %s ) )' % (e_, e_, e_))], '( %s ` u ) = ( ( u x. %s ) + ( K x. %s ) )' % (OM, e_, e_))
        od1 = D(w, Ac, 'eqtrd', [vod, D(w, Ac, 'oveq1d', [D(w, Ac, 'eqtrd', [D(w, Ac, 'exp1d', [u0_], '( ( u + 0 ) ^ 1 ) = ( u + 0 )'), D(w, Ac, 'addridd', [uc_], '( u + 0 ) = u')], '( ( u + 0 ) ^ 1 ) = u')],
                                                            '( ( ( u + 0 ) ^ 1 ) x. %s ) = ( u x. %s )' % (e_, e_))], '( %s ` u ) = ( u x. %s )' % (OD, e_))
        r = D(w, Ac, 'eqtr4d', [D(w, Ac, 'addcomd', [D(w, Ac, 'mulcld', [uc_, ec_], '( u x. %s ) e. CC' % e_), D(w, Ac, 'mulcld', [kc_, ec_], '( K x. %s ) e. CC' % e_)],
                                  '( ( u x. %s ) + ( K x. %s ) ) = ( ( K x. %s ) + ( u x. %s ) )' % (e_, e_, e_, e_)),
                                D(w, Ac, 'oveq12d', [D(w, Ac, 'oveq2d', [pt1], '( K x. ( %s ` u ) ) = ( K x. %s )' % (PT_, e_)), od1], '( ( K x. ( %s ` u ) ) + ( %s ` u ) ) = ( ( K x. %s ) + ( u x. %s ) )' % (PT_, OD, e_, e_))],
                '( ( u x. %s ) + ( K x. %s ) ) = ( ( K x. ( %s ` u ) ) + ( %s ` u ) )' % (e_, e_, PT_, OD))
        return D(w, Ac, 'eqtrd', [om2, r], '( %s ` u ) = ( ( K x. ( %s ` u ) ) + ( %s ` u ) )' % (OM, PT_, OD))
    pw1 = pw(Au1, '1'); pw0 = pw(Au0, '0')
    # OD is odd
    Av = '( %s /\\ v e. CC )' % ph
    vc = w.s([], 'simpr', '( %s -> v e. CC )' % Av); nvc = D(w, Av, 'negcld', [vc], '-u v e. CC'); z0v = cst(w, Av, '0cn', '0 e. CC')
    o1 = gfv(w, Av, '-u T', '0', '0', '1', '-u v', nvc, g, 'w'); o2 = gfv(w, Av, '-u T', '0', '0', '1', 'v', vc, g, 'w')
    nv0 = D(w, Av, 'addridd', [nvc], '( -u v + 0 ) = -u v'); v0 = D(w, Av, 'addridd', [vc], '( v + 0 ) = v')
    nn = D(w, Av, 'eqtr4d', [nv0, D(w, Av, 'negeqd', [v0], '-u ( v + 0 ) = -u v')], '( -u v + 0 ) = -u ( v + 0 )')
    v0c = D(w, Av, 'addcld', [vc, z0v], '( v + 0 ) e. CC')
    q1 = D(w, Av, 'eqtrd', [D(w, Av, 'oveq1d', [nn], '( ( -u v + 0 ) ^ 2 ) = ( -u ( v + 0 ) ^ 2 )'), D(w, Av, 'sqnegd', [v0c], '( -u ( v + 0 ) ^ 2 ) = ( ( v + 0 ) ^ 2 )')], '( ( -u v + 0 ) ^ 2 ) = ( ( v + 0 ) ^ 2 )')
    eq_e = D(w, Av, 'fveq2d', [D(w, Av, 'negeqd', [D(w, Av, 'oveq2d', [q1], '( ( _pi x. -u T ) x. ( ( -u v + 0 ) ^ 2 ) ) = ( ( _pi x. -u T ) x. ( ( v + 0 ) ^ 2 ) )')],
                                 '-u ( ( _pi x. -u T ) x. ( ( -u v + 0 ) ^ 2 ) ) = -u ( ( _pi x. -u T ) x. ( ( v + 0 ) ^ 2 ) )')], '%s = %s' % (E('-u T', '-u v'), E('-u T', 'v')))
    q2 = D(w, Av, 'eqtrd', [D(w, Av, 'exp1d', [D(w, Av, 'addcld', [nvc, z0v], '( -u v + 0 ) e. CC')], '( ( -u v + 0 ) ^ 1 ) = ( -u v + 0 )'), nn], '( ( -u v + 0 ) ^ 1 ) = -u ( v + 0 )')
    q3 = D(w, Av, 'eqtrd', [q2, D(w, Av, 'negeqd', [D(w, Av, 'eqcomd', [D(w, Av, 'exp1d', [v0c], '( ( v + 0 ) ^ 1 ) = ( v + 0 )')], '( v + 0 ) = ( ( v + 0 ) ^ 1 )')], '-u ( v + 0 ) = -u ( ( v + 0 ) ^ 1 )')],
            '( ( -u v + 0 ) ^ 1 ) = -u ( ( v + 0 ) ^ 1 )')
    ev = E('-u T', 'v')
    evc = D(w, Av, 'efcld', [D(w, Av, 'negcld', [D(w, Av, 'mulcld', [D(w, Av, 'mulcld', [cst(w, Av, 'picn', '_pi e. CC'), w.s([ntc], 'adantr', '( %s -> -u T e. CC )' % Av)], '( _pi x. -u T ) e. CC'),
                                                                       D(w, Av, 'sqcld', [v0c], '( ( v + 0 ) ^ 2 ) e. CC')], '( ( _pi x. -u T ) x. ( ( v + 0 ) ^ 2 ) ) e. CC')], '-u ( ( _pi x. -u T ) x. ( ( v + 0 ) ^ 2 ) ) e. CC')], '%s e. CC' % ev)
    q4 = D(w, Av, 'oveq12d', [q3, eq_e], '%s = ( -u ( ( v + 0 ) ^ 1 ) x. %s )' % (gfbody('-u T', '0', '0', '1', '-u v'), ev))
    q5 = D(w, Av, 'mulneg1d', [D(w, Av, 'expcld', [v0c, cst(w, Av, '1nn0', '1 e. NN0')], '( ( v + 0 ) ^ 1 ) e. CC'), evc], '( -u ( ( v + 0 ) ^ 1 ) x. %s ) = -u ( ( ( v + 0 ) ^ 1 ) x. %s )' % (ev, ev))
    oddv = D(w, Av, 'eqtr4d', [D(w, Av, 'eqtrd', [D(w, Av, 'eqtrd', [o1, q4], '( %s ` -u v ) = ( -u ( ( v + 0 ) ^ 1 ) x. %s )' % (OD, ev)), q5], '( %s ` -u v ) = -u ( ( ( v + 0 ) ^ 1 ) x. %s )' % (OD, ev)),
                               D(w, Av, 'negeqd', [o2], '-u ( %s ` v ) = -u %s' % (OD, gfbody('-u T', '0', '0', '1', 'v')))], '( %s ` -u v ) = -u ( %s ` v )' % (OD, OD))
    oddall_v = w.s([oddv], 'ralrimiva', '( %s -> A. v e. CC ( %s ` -u v ) = -u ( %s ` v ) )' % (ph, OD, OD))
    Ev = 'v = y'
    iv = w.s([], 'id', '( %s -> %s )' % (Ev, Ev))
    st, nt = congr.wff_congruence('( %s ` -u v ) = -u ( %s ` v )' % (OD, OD), {'v': 'y'}, Ev, {'v': iv}, g)
    w.lines.extend(g.lines); g.lines = []
    cb = w.s([st], 'cbvralvw', '( A. v e. CC ( %s ` -u v ) = -u ( %s ` v ) <-> A. y e. CC ( %s ` -u y ) = -u ( %s ` y ) )' % (OD, OD, OD, OD))
    oddall = D(w, ph, 'sylib', [oddall_v, cb], 'A. y e. CC ( %s ` -u y ) = -u ( %s ` y )' % (OD, OD)) if False else w.s([oddall_v, cb], 'sylib', '( %s -> A. y e. CC ( %s ` -u y ) = -u ( %s ` y ) )' % (ph, OD, OD))
    # per t
    At = '( %s /\\ t e. RR+ )' % ph
    tt = w.s([], 'simpr', '( %s -> t e. RR+ )' % At); ttc = D(w, At, 'rpcnd', [tt], 't e. CC')
    ic = cst(w, At, 'ax-icn', '_i e. CC'); z0t = cst(w, At, '0cn', '0 e. CC')
    P0, Q0 = CP('0', '-u t'), CP('0', 't')
    p0c = D(w, At, 'addcld', [z0t, D(w, At, 'mulcld', [ic, D(w, At, 'negcld', [ttc], '-u t e. CC')], '( _i x. -u t ) e. CC')], '%s e. CC' % P0)
    q0c = D(w, At, 'addcld', [z0t, D(w, At, 'mulcld', [ic, ttc], '( _i x. t ) e. CC')], '%s e. CC' % Q0)
    css = D(w, At, 'syl2anc', [p0c, q0c, w.inst('csegcl')], '( %s cseg %s ) C_ CC' % (P0, Q0))
    Lt = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (At, f))
    def onseg(Ac, pw_, lift):
        """( Ac -> A. u e. ( P0 cseg Q0 ) formula ) from pw_: ( ( Ac' /\\ u e. CC ) -> formula )"""
        return None
    LOM, LPT, LOD, LGL = LI(OM, P0, Q0), LI(PT_, P0, Q0), LI(OD, P0, Q0), LI(GL1, P0, Q0)
    # LPT = LGL
    Aus = '( %s /\\ u e. ( %s cseg %s ) )' % (At, P0, Q0)
    uS = w.s([w.s([], 'simpr', '( %s -> u e. ( %s cseg %s ) )' % (Aus, P0, Q0)), w.s([css], 'adantr', '( %s -> ( %s cseg %s ) C_ CC )' % (Aus, P0, Q0))], 'sseldd', '( %s -> u e. CC )' % Aus)
    def at_u(st, Actx, f):
        """re-derive a pointwise fact proved under ( ph' /\\ u e. CC ) in the segment context"""
        return st
    ptgl_s = w.s([w.s([w.s([ptgl], 'ex', '( %s -> ( u e. CC -> ( %s ` u ) = ( %s ` u ) ) )' % (ph, PT_, GL1))], 'ad2antrr', '( %s -> ( u e. CC -> ( %s ` u ) = ( %s ` u ) ) )' % (Aus, PT_, GL1)), uS], 'mpd',
                 '( %s -> ( %s ` u ) = ( %s ` u ) )' % (Aus, PT_, GL1)) if False else D(w, Aus, 'mpd', [uS, w.s([w.s([ptgl], 'ex', '( %s -> ( u e. CC -> ( %s ` u ) = ( %s ` u ) ) )' % (ph, PT_, GL1))], 'ad2antrr', '( %s -> ( u e. CC -> ( %s ` u ) = ( %s ` u ) ) )' % (Aus, PT_, GL1))],
                                                                                                          '( %s ` u ) = ( %s ` u )' % (PT_, GL1))
    # linteq's bound variable is z: rename
    Azs = '( %s /\\ z e. ( %s cseg %s ) )' % (At, P0, Q0)
    ptgl_all_u = w.s([ptgl_s], 'ralrimiva', '( %s -> A. u e. ( %s cseg %s ) ( %s ` u ) = ( %s ` u ) )' % (At, P0, Q0, PT_, GL1))
    Euz = 'u = z'
    iuz = w.s([], 'id', '( %s -> %s )' % (Euz, Euz))
    st2, _ = congr.wff_congruence('( %s ` u ) = ( %s ` u )' % (PT_, GL1), {'u': 'z'}, Euz, {'u': iuz}, g)
    w.lines.extend(g.lines); g.lines = []
    cbz = w.s([st2], 'cbvralvw', '( A. u e. ( %s cseg %s ) ( %s ` u ) = ( %s ` u ) <-> A. z e. ( %s cseg %s ) ( %s ` z ) = ( %s ` z ) )' % (P0, Q0, PT_, GL1, P0, Q0, PT_, GL1))
    ptgl_all = w.s([ptgl_all_u, cbz], 'sylib', '( %s -> A. z e. ( %s cseg %s ) ( %s ` z ) = ( %s ` z ) )' % (At, P0, Q0, PT_, GL1))
    lpg = D(w, At, 'syl', [w.s([w.s([w.s([p0c, q0c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (At, P0, Q0)), w.s([cst(w, At, 'mptex', '%s e. _V' % PT_), cst(w, At, 'mptex', '%s e. _V' % GL1)], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (At, PT_, GL1))],
                                     'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) ) )' % (At, P0, Q0, PT_, GL1)), ptgl_all], 'jca',
                                '( %s -> ( ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) ) /\\ A. z e. ( %s cseg %s ) ( %s ` z ) = ( %s ` z ) ) )' % (At, P0, Q0, PT_, GL1, P0, Q0, PT_, GL1)),
                           w.inst('linteq')], '%s = %s' % (LPT, LGL))
    # P = 1
    At1 = '( %s /\\ P = 1 )' % At
    Aus1 = '( %s /\\ u e. ( %s cseg %s ) )' % (At1, P0, Q0)
    uS1 = w.s([w.s([], 'simpr', '( %s -> u e. ( %s cseg %s ) )' % (Aus1, P0, Q0)), w.s([w.s([css], 'adantr', '( %s -> ( %s cseg %s ) C_ CC )' % (At1, P0, Q0))], 'adantr', '( %s -> ( %s cseg %s ) C_ CC )' % (Aus1, P0, Q0))],
              'sseldd', '( %s -> u e. CC )' % Aus1)
    F1 = '( %s ` u ) = ( ( K x. ( %s ` u ) ) + ( %s ` u ) )' % (OM, PT_, OD)
    pw1i = w.s([w.s([pw1], 'ex', '( ( %s /\\ P = 1 ) -> ( u e. CC -> %s ) )' % (ph, F1))], 'idi', '( ( %s /\\ P = 1 ) -> ( u e. CC -> %s ) )' % (ph, F1))
    pw1s = D(w, Aus1, 'mpd', [uS1, w.s([w.s([pw1i], 'adantlr', '( ( ( %s /\\ t e. RR+ ) /\\ P = 1 ) -> ( u e. CC -> %s ) )' % (ph, F1))], 'adantr', '( %s -> ( u e. CC -> %s ) )' % (Aus1, F1))], F1)
    all1 = w.s([pw1s], 'ralrimiva', '( %s -> A. u e. ( %s cseg %s ) %s )' % (At1, P0, Q0, F1))
    L1t = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (At1, f))
    lc = D(w, At1, 'syl', [w.s([w.s([L1t(p0c, '%s e. CC' % P0), L1t(q0c, '%s e. CC' % Q0)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (At1, P0, Q0)),
                                 w.s([cst(w, At1, 'mptex', '%s e. _V' % OM), w.s([kc], 'ad2antrr', '( %s -> K e. CC )' % At1),
                                      w.s([w.s([ptc], 'ad2antrr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At1, PT_)), w.s([odc], 'ad2antrr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At1, OD)), L1t(css, '( %s cseg %s ) C_ CC' % (P0, Q0))], '3jca',
                                          '( %s -> ( %s e. ( CC -cn-> CC ) /\\ %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (At1, PT_, OD, P0, Q0))], '3jca',
                                     '( %s -> ( %s e. _V /\\ K e. CC /\\ ( %s e. ( CC -cn-> CC ) /\\ %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At1, OM, PT_, OD, P0, Q0)), all1], '3jca',
                                '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ K e. CC /\\ ( %s e. ( CC -cn-> CC ) /\\ %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) /\\ A. u e. ( %s cseg %s ) %s ) )'
                                % (At1, P0, Q0, OM, PT_, OD, P0, Q0, P0, Q0, F1)), w.inst('lintlc')], '%s = ( ( K x. %s ) + %s )' % (LOM, LPT, LOD))
    # LOD = 0
    nq = D(w, At1, 'eqtrd', [D(w, At1, 'negdid', [L1t(z0t, '0 e. CC'), D(w, At1, 'mulcld', [cst(w, At1, 'ax-icn', '_i e. CC'), L1t(ttc, 't e. CC')], '( _i x. t ) e. CC')], '-u %s = ( -u 0 + -u ( _i x. t ) )' % Q0),
                             D(w, At1, 'oveq12d', [cst(w, At1, 'neg0', '-u 0 = 0'), D(w, At1, 'eqcomd', [D(w, At1, 'mulneg2d', [cst(w, At1, 'ax-icn', '_i e. CC'), L1t(ttc, 't e. CC')], '( _i x. -u t ) = -u ( _i x. t )')], '-u ( _i x. t ) = ( _i x. -u t )')],
                               '( -u 0 + -u ( _i x. t ) ) = %s' % P0)], '-u %s = %s' % (Q0, P0))
    lz = D(w, At1, 'syl', [w.s([w.s([L1t(q0c, '%s e. CC' % Q0), w.s([odc], 'ad2antrr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At1, OD))], 'jca', '( %s -> ( %s e. CC /\\ %s e. ( CC -cn-> CC ) ) )' % (At1, Q0, OD)),
                                w.s([oddall], 'ad2antrr', '( %s -> A. y e. CC ( %s ` -u y ) = -u ( %s ` y ) )' % (At1, OD, OD))], 'jca',
                               '( %s -> ( ( %s e. CC /\\ %s e. ( CC -cn-> CC ) ) /\\ A. y e. CC ( %s ` -u y ) = -u ( %s ` y ) ) )' % (At1, Q0, OD, OD, OD)), w.inst('zl3lod')], '( %s lint <. -u %s , %s >. ) = 0' % (OD, Q0, Q0))
    lod0 = D(w, At1, 'eqtr3d', [D(w, At1, 'oveq2d', [D(w, At1, 'opeq1d', [nq], '<. -u %s , %s >. = <. %s , %s >.' % (Q0, Q0, P0, Q0))], '( %s lint <. -u %s , %s >. ) = %s' % (OD, Q0, Q0, LOD)), lz], '%s = 0' % LOD)
    lpt1 = D(w, At1, 'syl', [w.s([w.s([L1t(p0c, '%s e. CC' % P0), L1t(q0c, '%s e. CC' % Q0)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (At1, P0, Q0)),
                                  w.s([w.s([ptc], 'ad2antrr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At1, PT_)), L1t(css, '( %s cseg %s ) C_ CC' % (P0, Q0))], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (At1, PT_, P0, Q0))],
                                 'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At1, P0, Q0, PT_, P0, Q0)), w.inst('lintcl')], '%s e. CC' % LPT)
    kpe = D(w, At1, 'eqtrd', [D(w, At1, 'oveq2d', [w.s([], 'simpr', '( %s -> P = 1 )' % At1)], '( K ^ P ) = ( K ^ 1 )'), D(w, At1, 'exp1d', [w.s([kc], 'ad2antrr', '( %s -> K e. CC )' % At1)], '( K ^ 1 ) = K')], '( K ^ P ) = K')
    c1 = D(w, At1, 'eqtr4d', [D(w, At1, 'eqtrd', [D(w, At1, 'eqtrd', [lc, D(w, At1, 'oveq2d', [lod0], '( ( K x. %s ) + %s ) = ( ( K x. %s ) + 0 )' % (LPT, LOD, LPT))], '%s = ( ( K x. %s ) + 0 )' % (LOM, LPT)),
                                                  D(w, At1, 'addridd', [D(w, At1, 'mulcld', [w.s([kc], 'ad2antrr', '( %s -> K e. CC )' % At1), lpt1], '( K x. %s ) e. CC' % LPT)], '( ( K x. %s ) + 0 ) = ( K x. %s )' % (LPT, LPT))], '%s = ( K x. %s )' % (LOM, LPT)),
                              D(w, At1, 'oveq1d', [kpe], '( ( K ^ P ) x. %s ) = ( K x. %s )' % (LPT, LPT))], '%s = ( ( K ^ P ) x. %s )' % (LOM, LPT))
    # P = 0
    At0 = '( %s /\\ P = 0 )' % At
    Aus0 = '( %s /\\ u e. ( %s cseg %s ) )' % (At0, P0, Q0)
    uS0 = w.s([w.s([], 'simpr', '( %s -> u e. ( %s cseg %s ) )' % (Aus0, P0, Q0)), w.s([w.s([css], 'adantr', '( %s -> ( %s cseg %s ) C_ CC )' % (At0, P0, Q0))], 'adantr', '( %s -> ( %s cseg %s ) C_ CC )' % (Aus0, P0, Q0))],
              'sseldd', '( %s -> u e. CC )' % Aus0)
    F0 = '( %s ` u ) = ( %s ` u )' % (OM, PT_)
    pw0s = D(w, Aus0, 'mpd', [uS0, w.s([w.s([w.s([pw0], 'ex', '( ( %s /\\ P = 0 ) -> ( u e. CC -> %s ) )' % (ph, F0))], 'adantlr', '( ( ( %s /\\ t e. RR+ ) /\\ P = 0 ) -> ( u e. CC -> %s ) )' % (ph, F0))],
                                      'adantr', '( %s -> ( u e. CC -> %s ) )' % (Aus0, F0))], F0)
    all0u = w.s([pw0s], 'ralrimiva', '( %s -> A. u e. ( %s cseg %s ) %s )' % (At0, P0, Q0, F0))
    st3, _ = congr.wff_congruence(F0, {'u': 'z'}, Euz, {'u': iuz}, g)
    w.lines.extend(g.lines); g.lines = []
    all0 = w.s([all0u, w.s([st3], 'cbvralvw', '( A. u e. ( %s cseg %s ) %s <-> A. z e. ( %s cseg %s ) ( %s ` z ) = ( %s ` z ) )' % (P0, Q0, F0, P0, Q0, OM, PT_))], 'sylib',
               '( %s -> A. z e. ( %s cseg %s ) ( %s ` z ) = ( %s ` z ) )' % (At0, P0, Q0, OM, PT_))
    L0t = lambda st, f: w.s([st], 'adantr', '( %s -> %s )' % (At0, f))
    le0 = D(w, At0, 'syl', [w.s([w.s([w.s([L0t(p0c, '%s e. CC' % P0), L0t(q0c, '%s e. CC' % Q0)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (At0, P0, Q0)),
                                      w.s([cst(w, At0, 'mptex', '%s e. _V' % OM), cst(w, At0, 'mptex', '%s e. _V' % PT_)], 'jca', '( %s -> ( %s e. _V /\\ %s e. _V ) )' % (At0, OM, PT_))], 'jca',
                                     '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) ) )' % (At0, P0, Q0, OM, PT_)), all0], 'jca',
                                '( %s -> ( ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) ) /\\ A. z e. ( %s cseg %s ) ( %s ` z ) = ( %s ` z ) ) )' % (At0, P0, Q0, OM, PT_, P0, Q0, OM, PT_)),
                            w.inst('linteq')], '%s = %s' % (LOM, LPT))
    lpt0 = D(w, At0, 'syl', [w.s([w.s([L0t(p0c, '%s e. CC' % P0), L0t(q0c, '%s e. CC' % Q0)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (At0, P0, Q0)),
                                  w.s([w.s([ptc], 'ad2antrr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At0, PT_)), L0t(css, '( %s cseg %s ) C_ CC' % (P0, Q0))], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (At0, PT_, P0, Q0))],
                                 'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At0, P0, Q0, PT_, P0, Q0)), w.inst('lintcl')], '%s e. CC' % LPT)
    kp0 = D(w, At0, 'eqtrd', [D(w, At0, 'oveq2d', [w.s([], 'simpr', '( %s -> P = 0 )' % At0)], '( K ^ P ) = ( K ^ 0 )'), D(w, At0, 'exp0d', [w.s([kc], 'ad2antrr', '( %s -> K e. CC )' % At0)], '( K ^ 0 ) = 1')], '( K ^ P ) = 1')
    c0 = D(w, At0, 'eqtr4d', [le0, D(w, At0, 'eqtrd', [D(w, At0, 'oveq1d', [kp0], '( ( K ^ P ) x. %s ) = ( 1 x. %s )' % (LPT, LPT)), D(w, At0, 'mullidd', [lpt0], '( 1 x. %s ) = %s' % (LPT, LPT))], '( ( K ^ P ) x. %s ) = %s' % (LPT, LPT))],
           '%s = ( ( K ^ P ) x. %s )' % (LOM, LPT))
    cc_ = w.s([c1, c0, w.s([w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % ph)], 'adantr', '( %s -> ( P = 0 \\/ P = 1 ) )' % At) if False else
               w.s([w.s([w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % ph)], 'adantr', '( %s -> ( P = 0 \\/ P = 1 ) )' % At), w.inst('orcom') if False else None], 'IGNORE', 'x') if False else
               w.s([w.s([w.s([w.s([pp, w.inst('elpri')], 'syl', '( %s -> ( P = 0 \\/ P = 1 ) )' % ph)], 'adantr', '( %s -> ( P = 0 \\/ P = 1 ) )' % At)], 'orcomd', '( %s -> ( P = 1 \\/ P = 0 ) )' % At)], 'idi', '( %s -> ( P = 1 \\/ P = 0 ) )' % At)],
              'mpjaodan', '( %s -> %s = ( ( K ^ P ) x. %s ) )' % (At, LOM, LPT))
    ct = D(w, At, 'eqtrd', [cc_, D(w, At, 'oveq2d', [lpg], '( ( K ^ P ) x. %s ) = ( ( K ^ P ) x. %s )' % (LPT, LGL))], '%s = ( ( K ^ P ) x. %s )' % (LOM, LGL))
    meq = w.s([ct], 'mpteq2dva', '( %s -> ( t e. RR+ |-> %s ) = ( t e. RR+ |-> ( ( K ^ P ) x. %s ) ) )' % (ph, LOM, LGL))
    # zl3scl on PS1 with L = sqrt T
    Ab = '( %s /\\ b e. RR )' % ph
    br = w.s([], 'simpr', '( %s -> b e. RR )' % Ab); bc = D(w, Ab, 'recnd', [br], 'b e. CC')
    z0b = cst(w, Ab, '0cn', '0 e. CC'); icb = cst(w, Ab, 'ax-icn', '_i e. CC')
    ZB = CP('0', 'b'); zbc = D(w, Ab, 'addcld', [z0b, D(w, Ab, 'mulcld', [icb, bc], '( _i x. b ) e. CC')], '%s e. CC' % ZB)
    pvb = gfv(w, Ab, '-u 1', '0', '0', '0', ZB, zbc, g, 'x')
    U_ = '( %s + 0 )' % ZB
    uz = D(w, Ab, 'addcld', [zbc, z0b], '%s e. CC' % U_)
    ibz = D(w, Ab, 'eqtrd', [D(w, Ab, 'addridd', [zbc], '%s = %s' % (U_, ZB)), D(w, Ab, 'addlidd', [D(w, Ab, 'mulcld', [icb, bc], '( _i x. b ) e. CC')], '%s = ( _i x. b )' % ZB)], '%s = ( _i x. b )' % U_)
    sqz = D(w, Ab, 'eqtrd', [D(w, Ab, 'eqtrd', [D(w, Ab, 'oveq1d', [ibz], '( %s ^ 2 ) = ( ( _i x. b ) ^ 2 )' % U_), D(w, Ab, 'sqmuld', [icb, bc], '( ( _i x. b ) ^ 2 ) = ( ( _i ^ 2 ) x. ( b ^ 2 ) )')],
                                               '( %s ^ 2 ) = ( ( _i ^ 2 ) x. ( b ^ 2 ) )' % U_), D(w, Ab, 'oveq1d', [cst(w, Ab, 'i2', '( _i ^ 2 ) = -u 1')], '( ( _i ^ 2 ) x. ( b ^ 2 ) ) = ( -u 1 x. ( b ^ 2 ) )')],
            '( %s ^ 2 ) = ( -u 1 x. ( b ^ 2 ) )' % U_)
    b2 = D(w, Ab, 'sqcld', [bc], '( b ^ 2 ) e. CC'); picb = cst(w, Ab, 'picn', '_pi e. CC'); n1b = cst(w, Ab, 'neg1cn', '-u 1 e. CC')
    # ( pi x. -u 1 ) x. ( -u 1 x. ( b ^ 2 ) ) = ( pi x. 1 ) x. ( b ^ 2 )
    x1 = D(w, Ab, 'eqtrd', [D(w, Ab, 'oveq2d', [sqz], '( ( _pi x. -u 1 ) x. ( %s ^ 2 ) ) = ( ( _pi x. -u 1 ) x. ( -u 1 x. ( b ^ 2 ) ) )' % U_),
                            D(w, Ab, 'eqcomd', [D(w, Ab, 'mulassd', [D(w, Ab, 'mulcld', [picb, n1b], '( _pi x. -u 1 ) e. CC'), n1b, b2], '( ( ( _pi x. -u 1 ) x. -u 1 ) x. ( b ^ 2 ) ) = ( ( _pi x. -u 1 ) x. ( -u 1 x. ( b ^ 2 ) ) )')],
                              '( ( _pi x. -u 1 ) x. ( -u 1 x. ( b ^ 2 ) ) ) = ( ( ( _pi x. -u 1 ) x. -u 1 ) x. ( b ^ 2 ) )')], '( ( _pi x. -u 1 ) x. ( %s ^ 2 ) ) = ( ( ( _pi x. -u 1 ) x. -u 1 ) x. ( b ^ 2 ) )' % U_)
    x2 = D(w, Ab, 'eqtrd', [D(w, Ab, 'mulassd', [picb, n1b, n1b], '( ( _pi x. -u 1 ) x. -u 1 ) = ( _pi x. ( -u 1 x. -u 1 ) )'), D(w, Ab, 'oveq2d', [cst(w, Ab, 'neg1mulneg1e1', '( -u 1 x. -u 1 ) = 1')], '( _pi x. ( -u 1 x. -u 1 ) ) = ( _pi x. 1 )')],
           '( ( _pi x. -u 1 ) x. -u 1 ) = ( _pi x. 1 )')
    x3 = D(w, Ab, 'eqtrd', [x1, D(w, Ab, 'oveq1d', [x2], '( ( ( _pi x. -u 1 ) x. -u 1 ) x. ( b ^ 2 ) ) = ( ( _pi x. 1 ) x. ( b ^ 2 ) )')], '( ( _pi x. -u 1 ) x. ( %s ^ 2 ) ) = ( ( _pi x. 1 ) x. ( b ^ 2 ) )' % U_)
    EB = '( exp ` -u ( ( _pi x. 1 ) x. ( b ^ 2 ) ) )'
    ex3 = D(w, Ab, 'fveq2d', [D(w, Ab, 'negeqd', [x3], '-u ( ( _pi x. -u 1 ) x. ( %s ^ 2 ) ) = -u ( ( _pi x. 1 ) x. ( b ^ 2 ) )' % U_)], '( exp ` -u ( ( _pi x. -u 1 ) x. ( %s ^ 2 ) ) ) = %s' % (U_, EB))
    vb = D(w, Ab, 'eqtrd', [pvb, D(w, Ab, 'oveq2d', [ex3], '%s = ( ( %s ^ 0 ) x. %s )' % (gfbody('-u 1', '0', '0', '0', ZB), U_, EB))], '( %s ` %s ) = ( ( %s ^ 0 ) x. %s )' % (PS1, ZB, U_, EB))
    # zl3gcb at T = 1 , P = 0 , U = U_ , V = b , C = 0 , R = 0
    rb = D(w, Ab, 'rered', [br], '( Re ` b ) = b'); imb = D(w, Ab, 'reim0d', [br], '( Im ` b ) = 0')
    au = D(w, Ab, 'eqtrd', [D(w, Ab, 'fveq2d', [ibz], '( abs ` %s ) = ( abs ` ( _i x. b ) )' % U_),
                            D(w, Ab, 'eqtrd', [D(w, Ab, 'absmuld', [icb, bc], '( abs ` ( _i x. b ) ) = ( ( abs ` _i ) x. ( abs ` b ) )'),
                                               D(w, Ab, 'eqtrd', [D(w, Ab, 'oveq1d', [cst(w, Ab, 'absi', '( abs ` _i ) = 1')], '( ( abs ` _i ) x. ( abs ` b ) ) = ( 1 x. ( abs ` b ) )'),
                                                                  D(w, Ab, 'mullidd', [D(w, Ab, 'abscld', [bc], '( abs ` b ) e. RR') if False else D(w, Ab, 'recnd', [D(w, Ab, 'abscld', [bc], '( abs ` b ) e. RR')], '( abs ` b ) e. CC')], '( 1 x. ( abs ` b ) ) = ( abs ` b )')],
                                                 '( ( abs ` _i ) x. ( abs ` b ) ) = ( abs ` b )')], '( abs ` ( _i x. b ) ) = ( abs ` b )')], '( abs ` %s ) = ( abs ` b )' % U_)
    arb = D(w, Ab, 'fveq2d', [rb], '( abs ` ( Re ` b ) ) = ( abs ` b )')
    abr = D(w, Ab, 'abscld', [bc], '( abs ` b ) e. RR')
    ub_ = D(w, Ab, 'eqbrtrd', [au, D(w, Ab, 'breqtrrd', [D(w, Ab, 'leidd', [abr], '( abs ` b ) <_ ( abs ` b )'), D(w, Ab, 'eqtrd', [D(w, Ab, 'oveq1d', [arb], '( ( abs ` ( Re ` b ) ) + 0 ) = ( ( abs ` b ) + 0 )'), D(w, Ab, 'addridd', [D(w, Ab, 'recnd', [abr], '( abs ` b ) e. CC')], '( ( abs ` b ) + 0 ) = ( abs ` b )')],
                                                                 '( ( abs ` ( Re ` b ) ) + 0 ) = ( abs ` b )')], '( abs ` b ) <_ ( ( abs ` ( Re ` b ) ) + 0 )')],
               '( abs ` %s ) <_ ( ( abs ` ( Re ` b ) ) + 0 )' % U_)
    ib0 = D(w, Ab, 'eqbrtrd', [D(w, Ab, 'eqtrd', [D(w, Ab, 'fveq2d', [imb], '( abs ` ( Im ` b ) ) = ( abs ` 0 )'), cst(w, Ab, 'abs0', '( abs ` 0 ) = 0')], '( abs ` ( Im ` b ) ) = 0'), D(w, Ab, 'leidd', [cst(w, Ab, '0re', '0 e. RR')], '0 <_ 0')],
              '( abs ` ( Im ` b ) ) <_ 0')
    MB = '( ( 1 + 0 ) x. ( ( exp ` ( ( _pi x. 1 ) x. ( 0 ^ 2 ) ) ) x. ( exp ` ( 1 / ( _pi x. 1 ) ) ) ) )'
    gcb = D(w, Ab, 'syl', [w.s([w.s([cst(w, Ab, '1rp', '1 e. RR+'), w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }') if False else cst(w, Ab, 'c0ex', '0 e. _V') if False else w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }') if False else
                                     w.s([w.s([w.s([], 'c0ex', '0 e. _V')], 'prid1', '0 e. { 0 , 1 }')], 'a1i', '( %s -> 0 e. { 0 , 1 } )' % Ab)], 'jca', '( %s -> ( 1 e. RR+ /\\ 0 e. { 0 , 1 } ) )' % Ab),
                                w.s([uz, bc], 'jca', '( %s -> ( %s e. CC /\\ b e. CC ) )' % (Ab, U_)),
                                w.s([w.s([cst(w, Ab, '0re', '0 e. RR'), cst(w, Ab, '0re', '0 e. RR')], 'jca', '( %s -> ( 0 e. RR /\\ 0 e. RR ) )' % Ab),
                                     w.s([D(w, Ab, 'leidd', [cst(w, Ab, '0re', '0 e. RR')], '0 <_ 0'), ub_, ib0], '3jca', '( %s -> ( 0 <_ 0 /\\ ( abs ` %s ) <_ ( ( abs ` ( Re ` b ) ) + 0 ) /\\ ( abs ` ( Im ` b ) ) <_ 0 ) )' % (Ab, U_))], 'jca',
                                    '( %s -> ( ( 0 e. RR /\\ 0 e. RR ) /\\ ( 0 <_ 0 /\\ ( abs ` %s ) <_ ( ( abs ` ( Re ` b ) ) + 0 ) /\\ ( abs ` ( Im ` b ) ) <_ 0 ) ) )' % (Ab, U_))], '3jca',
                               '( %s -> ( ( 1 e. RR+ /\\ 0 e. { 0 , 1 } ) /\\ ( %s e. CC /\\ b e. CC ) /\\ ( ( 0 e. RR /\\ 0 e. RR ) /\\ ( 0 <_ 0 /\\ ( abs ` %s ) <_ ( ( abs ` ( Re ` b ) ) + 0 ) /\\ ( abs ` ( Im ` b ) ) <_ 0 ) ) ) )' % (Ab, U_, U_)),
                          w.inst('zl3gcb')], '( abs ` ( ( %s ^ 0 ) x. %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` b ) ) ) )' % (U_, EB, MB))
    blb = D(w, Ab, 'breqtrd', [D(w, Ab, 'eqbrtrd', [D(w, Ab, 'fveq2d', [vb], '( abs ` ( %s ` %s ) ) = ( abs ` ( ( %s ^ 0 ) x. %s ) )' % (PS1, ZB, U_, EB)), gcb], '( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` ( Re ` b ) ) ) )' % (PS1, ZB, MB)),
                               D(w, Ab, 'oveq2d', [D(w, Ab, 'oveq2d', [D(w, Ab, 'negeqd', [arb], '-u ( abs ` ( Re ` b ) ) = -u ( abs ` b )')], '( 2 ^c -u ( abs ` ( Re ` b ) ) ) = ( 2 ^c -u ( abs ` b ) )')],
                                 '( %s x. ( 2 ^c -u ( abs ` ( Re ` b ) ) ) ) = ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (MB, MB))], '( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (PS1, ZB, MB))
    BL0 = 'A. b e. RR ( abs ` ( %s ` %s ) ) <_ ( %s x. ( 2 ^c -u ( abs ` b ) ) )' % (PS1, ZB, MB)
    bl0 = w.s([blb], 'ralrimiva', '( %s -> %s )' % (ph, BL0))
    mbr = D(w, ph, 'remulcld', [D(w, ph, 'readdcld', [cst(w, ph, '1re', '1 e. RR'), cst(w, ph, '0re', '0 e. RR')], '( 1 + 0 ) e. RR'),
                                D(w, ph, 'remulcld', [D(w, ph, 'reefcld', [D(w, ph, 'remulcld', [D(w, ph, 'remulcld', [cst(w, ph, 'pire', '_pi e. RR'), cst(w, ph, '1re', '1 e. RR')], '( _pi x. 1 ) e. RR'),
                                                                                                  D(w, ph, 'resqcld', [cst(w, ph, '0re', '0 e. RR')], '( 0 ^ 2 ) e. RR')], '( ( _pi x. 1 ) x. ( 0 ^ 2 ) ) e. RR')], '( exp ` ( ( _pi x. 1 ) x. ( 0 ^ 2 ) ) ) e. RR'),
                                                      D(w, ph, 'reefcld', [D(w, ph, 'rerpdivcld', [cst(w, ph, '1re', '1 e. RR'), D(w, ph, 'rpmulcld', [cst(w, ph, 'pirp', '_pi e. RR+'), cst(w, ph, '1rp', '1 e. RR+')], '( _pi x. 1 ) e. RR+')],
                                                                                '( 1 / ( _pi x. 1 ) ) e. RR')], '( exp ` ( 1 / ( _pi x. 1 ) ) ) e. RR')],
                                  '( ( exp ` ( ( _pi x. 1 ) x. ( 0 ^ 2 ) ) ) x. ( exp ` ( 1 / ( _pi x. 1 ) ) ) ) e. RR')], '%s e. RR' % MB)
    scl = D(w, ph, 'syl', [w.s([sqp, w.s([w.s([ps1c, mbr], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ %s e. RR ) )' % (ph, PS1, MB)), bl0], 'jca', '( %s -> ( ( %s e. ( CC -cn-> CC ) /\\ %s e. RR ) /\\ %s ) )' % (ph, PS1, MB, BL0))],
                               'jca', '( %s -> ( %s e. RR+ /\\ ( ( %s e. ( CC -cn-> CC ) /\\ %s e. RR ) /\\ %s ) ) )' % (ph, SQ, PS1, MB, BL0)), w.inst('zl3scl')],
            '( ( t e. RR+ |-> %s ) ~~>r ( %s / %s ) /\\ %s e. CC )' % (LGL, C0, SQ, C0))
    c0c = w.s([scl], 'simprd', '( %s -> %s e. CC )' % (ph, C0))
    scl = w.s([scl], 'simpld', '( %s -> ( t e. RR+ |-> %s ) ~~>r ( %s / %s ) )' % (ph, LGL, C0, SQ))
    KP = '( K ^ P )'
    kpc = D(w, ph, 'expcld', [kc, pn], '%s e. CC' % KP)
    rc = D(w, ph, 'syl2anc', [cst(w, ph, 'rpssre', 'RR+ C_ RR'), kpc, w.inst('rlimconst')], '( t e. RR+ |-> %s ) ~~>r %s' % (KP, KP))
    At_ = '( %s /\\ t e. RR+ )' % ph
    glc = D(w, At_, 'syl', [seg_pre(w, At_, P0, Q0, p0c, q0c, D(w, At_, 'cnfn', [], 'x') if False else w.s([w.s([w.s([sqc], 'adantr', '( %s -> %s e. CC )' % (At_, SQ))], 'IGNORE', 'x')], 'IGNORE', 'x') if False else None), w.inst('lintcl')], 'x') if False else None
    lgl_c = D(w, At_, 'syl3anc', [cst(w, At_, 'mptex', '%s e. _V' % GL1), p0c, q0c, w.inst('lintval')], '%s = S. ( 0 (,) 1 ) ( ( %s ` ( %s + ( t x. ( %s - %s ) ) ) ) x. ( %s - %s ) ) _d t' % (LGL, GL1, P0, Q0, P0, Q0, P0)) if False else None
    lglc = D(w, At_, 'eqeltrrd', [lpg, D(w, At_, 'syl', [seg_pre(w, At_, P0, Q0, p0c, q0c, w.s([ptc], 'adantr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At_, PT_))) if False else
                                                         w.s([w.s([w.s([p0c, q0c], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (At_, P0, Q0)),
                                                                   w.s([w.s([ptc], 'adantr', '( %s -> %s e. ( CC -cn-> CC ) )' % (At_, PT_)), css], 'jca', '( %s -> ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) )' % (At_, PT_, P0, Q0))],
                                                                  'jca', '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At_, P0, Q0, PT_, P0, Q0))], 'idi',
                                                             '( %s -> ( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( CC -cn-> CC ) /\\ ( %s cseg %s ) C_ CC ) ) )' % (At_, P0, Q0, PT_, P0, Q0)), w.inst('lintcl')], '%s e. CC' % LPT)],
                  '%s e. CC' % LGL)
    LGLs = LI(GL1, CP('0', '-u s'), CP('0', 's'))
    Ets = 't = s'
    its = w.s([], 'id', '( %s -> %s )' % (Ets, Ets))
    stA, ntA = congr.congruence(LGL, {'t': 's'}, Ets, {'t': its}, g)
    w.lines.extend(g.lines); g.lines = []
    assert ntA == LGLs, ntA
    cb1 = w.s([stA], 'cbvmptv', '( t e. RR+ |-> %s ) = ( s e. RR+ |-> %s )' % (LGL, LGLs))
    scls = D(w, ph, 'eqbrtrrd', [w.s([cb1], 'a1i', '( %s -> ( t e. RR+ |-> %s ) = ( s e. RR+ |-> %s ) )' % (ph, LGL, LGLs)), scl], '( s e. RR+ |-> %s ) ~~>r ( %s / %s )' % (LGLs, C0, SQ))
    rcs = D(w, ph, 'syl2anc', [cst(w, ph, 'rpssre', 'RR+ C_ RR'), kpc, w.inst('rlimconst')], '( s e. RR+ |-> %s ) ~~>r %s' % (KP, KP))
    As_ = '( %s /\\ s e. RR+ )' % ph
    rms = D(w, ph, 'rlimmul', [cst(w, As_, 'ovex', '%s e. _V' % KP), cst(w, As_, 'ovex', '%s e. _V' % LGLs), rcs, scls], '( s e. RR+ |-> ( %s x. %s ) ) ~~>r ( %s x. ( %s / %s ) )' % (KP, LGLs, KP, C0, SQ))
    stB, ntB = congr.congruence('( %s x. %s )' % (KP, LGL), {'t': 's'}, Ets, {'t': its}, g)
    w.lines.extend(g.lines); g.lines = []
    cb2 = w.s([stB], 'cbvmptv', '( t e. RR+ |-> ( %s x. %s ) ) = ( s e. RR+ |-> ( %s x. %s ) )' % (KP, LGL, KP, LGLs))
    meq2 = D(w, ph, 'eqtrd', [meq, w.s([cb2], 'a1i', '( %s -> ( t e. RR+ |-> ( %s x. %s ) ) = ( s e. RR+ |-> ( %s x. %s ) ) )' % (ph, KP, LGL, KP, LGLs))],
             '( t e. RR+ |-> %s ) = ( s e. RR+ |-> ( %s x. %s ) )' % (LOM, KP, LGLs))
    w.qed([D(w, ph, 'eqbrtrd', [meq2, rms], '( t e. RR+ |-> %s ) ~~>r ( %s x. ( %s / %s ) )' % (LOM, KP, C0, SQ)), c0c], 'jca', S['zl3ftw'])
    go(w, only)
