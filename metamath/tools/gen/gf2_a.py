"""Sortie GF2, section A: the anchor identity on Re w = 1 (Lean Bgram_eq_integral_anchor,
bMaj_term_eq_integral, norm_Tanc_le, tsum_Tanc), generic in the window endpoints A <_ B, the
width L and a bounded coefficient function Q.
MM_DB=sorties/gf2.mm MM_ENGINE=mmatch python3 tools/gen/gf2_a.py LABEL..."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z5alib import *
from cl import Closure, lift, split_imp
import lin, num
lin.FASTPATH = True
import gf2lib as L
import gf1lib as G1L
from mvlib import ringeq, ringeqp
from gf1lib import tsub, proj
from gf2_f import DG, TPI, LIt, MYF, BND, fvd, S_ as _SF

S_ = L.S
E3 = lambda X: '( exp ` ( 3 x. %s ) )' % X
KH = '( K ^c -u ( 1 / 2 ) )'
S_['gf2ypow'] = ('( ( ( K e. RR /\\ 1 <_ K ) /\\ ( X e. RR /\\ 0 <_ X ) ) -> %s <_ ( ( ; ; 1 2 8 x. %s ) x. %s ) )'
                 % (MYF('( K x. ( exp ` -u X ) )'), E3('X'), KH))


def gf2ypow():
    w = W('gf2ypow', 'The Mellin tail constant at ` Y = K e ^ -u X ` , ` K >_ 1 ` , ` X >_ 0 ` : '
          '` 64 ( Y ^ -u ( 1 / 2 ) + Y ^ -u 3 ) <_ 128 e ^ ( 3 X ) K ^ -u ( 1 / 2 ) ` (~ mulcxpd , ~ efcxp , ~ cxplea ).')
    a = split_imp(S_['gf2ypow'])[0]
    st = mkst(w, a)
    kr = st([], 'simpll', 'K e. RR'); k1 = st([], 'simplr', '1 <_ K')
    xr = st([], 'simprl', 'X e. RR'); x0 = st([], 'simprr', '0 <_ X')
    k0 = lin.linarith(w, a, [k1], '0 <_ K', leaves={'K': kr})
    krp = st([kr, lin.linarith(w, a, [k1], '0 < K', leaves={'K': kr})], 'elrpd', 'K e. RR+')
    nx = st([xr], 'renegcld', '-u X e. RR')
    exr = st([st([nx], 'rpefcld', '( exp ` -u X ) e. RR+')], 'rpred', '( exp ` -u X ) e. RR')
    ex0 = st([st([nx], 'rpefcld', '( exp ` -u X ) e. RR+')], 'rpge0d', '0 <_ ( exp ` -u X )')
    Y = '( K x. ( exp ` -u X ) )'
    out = {}
    for c, cs in (('-u ( 1 / 2 )', 'h'), ('-u 3', 't')):
        cr = litr(w, a, c)
        m = st([kr, k0, exr, ex0, st([cr], 'recnd', '%s e. CC' % c)], 'mulcxpd', '( %s ^c %s ) = ( ( K ^c %s ) x. ( ( exp ` -u X ) ^c %s ) )' % (Y, c, c, c))
        e = st([nx, cr, w.inst('efcxp')], 'syl2anc', '( ( exp ` -u X ) ^c %s ) = ( exp ` ( %s x. -u X ) )' % (c, c))
        pr = st([cr, nx], 'remulcld', '( %s x. -u X ) e. RR' % c)
        e3r = st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), xr], 'remulcld', '( 3 x. X ) e. RR')
        le = lin.linarith(w, a, [x0], '( %s x. -u X ) <_ ( 3 x. X )' % c, leaves={'X': xr})
        el = st([le, st([pr, e3r, w.inst('efle')], 'syl2anc', '( ( %s x. -u X ) <_ ( 3 x. X ) <-> ( exp ` ( %s x. -u X ) ) <_ %s )' % (c, c, E3('X')))], 'mpbid',
                '( exp ` ( %s x. -u X ) ) <_ %s' % (c, E3('X')))
        kc = st([krp, cr], 'rpcxpcld', '( K ^c %s ) e. RR+' % c)
        out[cs] = dict(m=m, e=e, el=el, kc=kc, pr=pr, cr=cr)
    e3p = st([st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), xr], 'remulcld', '( 3 x. X ) e. RR')], 'rpefcld', '%s e. RR+' % E3('X'))
    khp = out['h']['kc']
    k3le = st([st([kr, k1], 'jca', '( K e. RR /\\ 1 <_ K )'), st([out['t']['cr'], out['h']['cr']], 'jca', '( -u 3 e. RR /\\ -u ( 1 / 2 ) e. RR )'),
               lin.linarith(w, a, [], '-u 3 <_ -u ( 1 / 2 )'), w.inst('cxplea')], 'syl3anc', '( K ^c -u 3 ) <_ %s' % KH)
    P = '( %s x. %s )' % (KH, E3('X'))
    pr = st([st([khp], 'rpred', '%s e. RR' % KH), st([e3p], 'rpred', '%s e. RR' % E3('X'))], 'remulcld', '%s e. RR' % P)
    bnds = []
    for cs, kle in (('h', None), ('t', k3le)):
        o = out[cs]; c = '-u ( 1 / 2 )' if cs == 'h' else '-u 3'
        Ec = '( exp ` ( %s x. -u X ) )' % c
        ecp = st([o['pr']], 'rpefcld', '%s e. RR+' % Ec)
        v = st([o['m'], st([o['e']], 'oveq2d', '( ( K ^c %s ) x. ( ( exp ` -u X ) ^c %s ) ) = ( ( K ^c %s ) x. %s )' % (c, c, c, Ec))], 'eqtrd',
               '( %s ^c %s ) = ( ( K ^c %s ) x. %s )' % (Y, c, c, Ec))
        # ( K ^c c ) Ec <_ ( K ^c c ) E3 <_ KH E3
        b1 = st([st([ecp], 'rpred', '%s e. RR' % Ec), st([e3p], 'rpred', '%s e. RR' % E3('X')), st([o['kc']], 'rpred', '( K ^c %s ) e. RR' % c),
                 st([o['kc']], 'rpge0d', '0 <_ ( K ^c %s )' % c), o['el']], 'lemul2ad', '( ( K ^c %s ) x. %s ) <_ ( ( K ^c %s ) x. %s )' % (c, Ec, c, E3('X')))
        if kle is not None:
            b2 = st([st([o['kc']], 'rpred', '( K ^c %s ) e. RR' % c), st([khp], 'rpred', '%s e. RR' % KH), st([e3p], 'rpred', '%s e. RR' % E3('X')),
                     st([e3p], 'rpge0d', '0 <_ %s' % E3('X')), kle], 'lemul1ad', '( ( K ^c %s ) x. %s ) <_ %s' % (c, E3('X'), P))
            b1 = st([b1, b2], 'letrd', '( ( K ^c %s ) x. %s ) <_ %s' % (c, Ec, P))
        bnds.append(st([v, b1], 'eqbrtrd', '( %s ^c %s ) <_ %s' % (Y, c, P)))
    yp = st([krp, st([nx], 'rpefcld', '( exp ` -u X ) e. RR+')], 'rpmulcld', '%s e. RR+' % Y)
    yh = st([st([yp, out['h']['cr']], 'rpcxpcld', '( %s ^c -u ( 1 / 2 ) ) e. RR+' % Y)], 'rpred', '( %s ^c -u ( 1 / 2 ) ) e. RR' % Y)
    yt = st([st([yp, out['t']['cr']], 'rpcxpcld', '( %s ^c -u 3 ) e. RR+' % Y)], 'rpred', '( %s ^c -u 3 ) e. RR' % Y)
    sb = st([yh, yt, pr, pr, bnds[0], bnds[1]], 'le2addd', '( ( %s ^c -u ( 1 / 2 ) ) + ( %s ^c -u 3 ) ) <_ ( %s + %s )' % (Y, Y, P, P))
    SY = '( ( %s ^c -u ( 1 / 2 ) ) + ( %s ^c -u 3 ) )' % (Y, Y)
    m64 = st([st([yh, yt], 'readdcld', '%s e. RR' % SY), st([pr, pr], 'readdcld', '( %s + %s ) e. RR' % (P, P)), a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'),
              a1(w, a, num.ge0_nat(w, 64), '0 <_ ; 6 4'), sb], 'lemul2ad', '( ; 6 4 x. %s ) <_ ( ; 6 4 x. ( %s + %s ) )' % (SY, P, P))
    cl = Closure(w, a, {KH: st([khp], 'rpred', '%s e. RR' % KH), E3('X'): st([e3p], 'rpred', '%s e. RR' % E3('X'))})
    rq = ringeq(w, a, '( ; 6 4 x. ( %s + %s ) )' % (P, P), '( ( ; ; 1 2 8 x. %s ) x. %s )' % (E3('X'), KH), cl)
    fin = st([m64, rq], 'breqtrd', split_imp(S_['gf2ypow'])[1])
    w.qed([fin], 'idi', S_['gf2ypow'])
    return w


# ---------------------------------------------------------------- the anchor objects
AH = ('( ( ( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) ) /\\ L e. RR+ ) /\\ ( ( Q : NN --> CC /\\ ( H e. RR /\\ '
      'A. j e. NN ( abs ` ( Q ` j ) ) <_ H ) ) /\\ ( S e. CC /\\ 0 <_ ( Re ` S ) ) ) )')
KKv = lambda v: G1L.KK('A', 'B', 'L', v)
AVT = lambda X, n: '( ( 1 / L ) x. S_ [ %s -> ( %s + L ) ] ( exp ` ( -u %s / ( exp ` t ) ) ) _d t )' % (X, X, n)
WN = lambda n: '( %s - %s )' % (AVT('B', n), AVT('A', n))
CN = lambda n: '( ( ( 1 / %s ) x. ( Q ` %s ) ) x. ( %s ^c -u S ) )' % (n, n, n)
KG = lambda n, v: '( ( ( _G ` %s ) x. ( %s ^c -u %s ) ) x. %s )' % (v, n, v, KKv(v))
FB = lambda n, v: '( %s x. %s )' % (CN(n), KG(n, v))
TN = lambda n: '( %s x. %s )' % (CN(n), WN(n))
SA = '( 1 + ( _i x. -u T ) )'; SB = '( 1 + ( _i x. T ) )'; SEG = '( %s cseg %s )' % (SA, SB)
FNS = '( n e. NN |-> ( v e. %s |-> %s ) )' % (SEG, FB('n', 'v'))
EE = '( ( exp ` ( B + L ) ) + ( exp ` ( A + L ) ) )'
K0 = '( ( ; ; 1 2 8 x. H ) x. %s )' % EE
N32 = lambda n: '( %s ^c -u ( 3 / 2 ) )' % n
S_['gf2anp'] = ('( ( %s /\\ ( T e. RR+ /\\ ( K e. NN /\\ V e. %s ) ) ) -> ( ( ( Re ` V ) = 1 /\\ V e. %s ) /\\ '
                '( ( ( %s ` K ) ` V ) = %s /\\ ( abs ` %s ) <_ ( %s x. %s ) ) ) )') % (AH, SEG, DG, FNS, FB('K', 'V'), FB('K', 'V'), K0, N32('K'))


def ahf(w, a, base):
    """facts of AH under a ( base: the AH part of a, as a projection route )"""
    from gf1lib import proj
    st = mkst(w, a)
    f = {}
    for x in ['A e. RR', 'B e. RR', '0 <_ A', '0 <_ B', 'L e. RR+', 'Q : NN --> CC', 'H e. RR', 'A. j e. NN ( abs ` ( Q ` j ) ) <_ H',
              'S e. CC', '0 <_ ( Re ` S )']:
        f[x] = proj(w, a, x)
    return f


def segf(w, a, tr):
    """SA, SB e. CC, Re = 1 on SEG"""
    st = mkst(w, a)
    one = st([], '1red', '1 e. RR')
    ntr = st([tr], 'renegcld', '-u T e. RR')
    ic = a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    sac = st([st([], '1cnd', '1 e. CC'), st([ic, st([ntr], 'recnd', '-u T e. CC')], 'mulcld', '( _i x. -u T ) e. CC')], 'addcld', '%s e. CC' % SA)
    sbc = st([st([], '1cnd', '1 e. CC'), st([ic, st([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SB)
    ra = st([one, ntr], 'crred', '( Re ` %s ) = 1' % SA); rb = st([one, tr], 'crred', '( Re ` %s ) = 1' % SB)
    segcc = st([sac, sbc, w.inst('csegcl')], 'syl2anc', '%s C_ CC' % SEG)
    vre = st([sac, sbc, st([ra, rb], 'eqtr4d', '( Re ` %s ) = ( Re ` %s )' % (SA, SB)), w.inst('csegvre')], 'syl3anc',
             'A. u e. %s ( Re ` u ) = ( Re ` %s )' % (SEG, SA))
    return dict(sac=sac, sbc=sbc, ra=ra, segcc=segcc, vre=vre, ic=ic)


def ptf(w, a, sf, vm, V):
    """( a -> Re V = 1 ), V e. CC, V e. DG"""
    st = mkst(w, a)
    rsp = w.s([w.s([], 'fveq2', '( u = %s -> ( Re ` u ) = ( Re ` %s ) )' % (V, V))], 'eqeq1d', '( u = %s -> ( ( Re ` u ) = ( Re ` %s ) <-> ( Re ` %s ) = ( Re ` %s ) ) )' % (V, SA, V, SA))
    r0 = st([rsp, sf['vre'], vm], 'rspcdva', '( Re ` %s ) = ( Re ` %s )' % (V, SA))
    rv = st([r0, sf['ra']], 'eqtrd', '( Re ` %s ) = 1' % V)
    vc = st([sf['segcc'], vm], 'sseldd', '%s e. CC' % V)
    rvr = st([vc], 'recld', '( Re ` %s ) e. RR' % V)
    m1 = lin.linarith(w, a, [rv], '-u 1 < ( Re ` %s )' % V, leaves={'( Re ` %s )' % V: rvr})
    A0 = '( %s /\\ %s = 0 )' % (a, V); t0 = mkst(w, A0)
    r00 = t0([t0([t0([], 'simpr', '%s = 0' % V)], 'fveq2d', '( Re ` %s ) = ( Re ` 0 )' % V), a1(w, A0, w.s([], 're0', '( Re ` 0 ) = 0'), '( Re ` 0 ) = 0')], 'eqtrd',
             '( Re ` %s ) = 0' % V)
    rne = st([st([rv, a1(w, a, w.s([], 'ax-1ne0', '1 =/= 0'), '1 =/= 0')], 'eqnetrd', '( Re ` %s ) =/= 0' % V)], 'neneqd', '-. ( Re ` %s ) = 0' % V)
    nv = w.s([r00, lift(w, rne, A0)], 'pm2.65da', '( %s -> -. %s = 0 )' % (a, V))
    vn = st([nv], 'neqned', '%s =/= 0' % V)
    vdg = st([st([vc, st([m1, vn], 'jca', '( -u 1 < ( Re ` %s ) /\\ %s =/= 0 )' % (V, V))], 'jca', '( %s e. CC /\\ ( -u 1 < ( Re ` %s ) /\\ %s =/= 0 ) )' % (V, V, V)),
              w.inst('z6rdg')], 'syl', '%s e. %s' % (V, DG))
    return rv, vc, vdg, rvr


def e4le1(w, a, vc, V):
    """( 2 ^c -u ( ( abs ` ( Im ` V ) ) / 4 ) ) e. RR, <_ 1"""
    st = mkst(w, a)
    E4 = '( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) )' % V
    iq = st([st([vc], 'imcld', '( Im ` %s ) e. RR' % V)], 'recnd', '( Im ` %s ) e. CC' % V)
    aiq = st([iq], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % V); aiq0 = st([iq], 'absge0d', '0 <_ ( abs ` ( Im ` %s ) )' % V)
    ng = st([st([aiq, a1(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, a, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')], 'redivcld', '( ( abs ` ( Im ` %s ) ) / 4 ) e. RR' % V)],
            'renegcld', '-u ( ( abs ` ( Im ` %s ) ) / 4 ) e. RR' % V)
    ng0 = lin.linarith(w, a, [aiq0], '-u ( ( abs ` ( Im ` %s ) ) / 4 ) <_ 0' % V, leaves={'( abs ` ( Im ` %s ) )' % V: aiq})
    c2 = st([st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), a1(w, a, w.s([], '1lt2', '1 < 2'), '1 < 2')], 'jca', '( 2 e. RR /\\ 1 < 2 )'),
             st([ng, st([], '0red', '0 e. RR')], 'jca', '( -u ( ( abs ` ( Im ` %s ) ) / 4 ) e. RR /\\ 0 e. RR )' % V), w.inst('cxple')], 'syl2anc',
            '( -u ( ( abs ` ( Im ` %s ) ) / 4 ) <_ 0 <-> %s <_ ( 2 ^c 0 ) )' % (V, E4))
    e41 = st([st([ng0, c2], 'mpbid', '%s <_ ( 2 ^c 0 )' % E4), a1(w, a, w.s([w.s([], '2cn', '2 e. CC'), w.inst('cxp0')], 'ax-mp', '( 2 ^c 0 ) = 1'), '( 2 ^c 0 ) = 1')],
             'breqtrd', '%s <_ 1' % E4)
    e4p = st([a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), ng], 'rpcxpcld', '%s e. RR+' % E4)
    return E4, e4p, e41


def cnb(w, a, f, kn, K):
    """( abs ` CN(K) ) <_ ( ( 1 / K ) x. H ), CN(K) e. CC"""
    st = mkst(w, a)
    krp = st([kn], 'nnrpd', '%s e. RR+' % K); kr = st([kn], 'nnred', '%s e. RR' % K); kc = st([kn], 'nncnd', '%s e. CC' % K)
    k1 = st([kn], 'nnge1d', '1 <_ %s' % K)
    ik = st([kn], 'nnrecred', '( 1 / %s ) e. RR' % K)
    ik0 = st([st([krp], 'rpreccld', '( 1 / %s ) e. RR+' % K)], 'rpge0d', '0 <_ ( 1 / %s )' % K)
    qkc = st([f['Q : NN --> CC'], kn], 'ffvelcdmd', '( Q ` %s ) e. CC' % K)
    rsp = w.s([w.s([w.s([], 'fveq2', '( j = %s -> ( Q ` j ) = ( Q ` %s ) )' % (K, K))], 'fveq2d', '( j = %s -> ( abs ` ( Q ` j ) ) = ( abs ` ( Q ` %s ) ) )' % (K, K))],
              'breq1d', '( j = %s -> ( ( abs ` ( Q ` j ) ) <_ H <-> ( abs ` ( Q ` %s ) ) <_ H ) )' % (K, K))
    qb = st([rsp, f['A. j e. NN ( abs ` ( Q ` j ) ) <_ H'], kn], 'rspcdva', '( abs ` ( Q ` %s ) ) <_ H' % K)
    sc = f['S e. CC']
    nsc = st([sc], 'negcld', '-u S e. CC')
    ksc = st([kc, nsc], 'cxpcld', '( %s ^c -u S ) e. CC' % K)
    # | K ^c -u S | = K ^c ( Re -u S ) <_ K ^c 0 = 1
    ab = st([krp, nsc, w.inst('abscxp')], 'syl2anc', '( abs ` ( %s ^c -u S ) ) = ( %s ^c ( Re ` -u S ) )' % (K, K))
    rn = st([sc], 'renegd', '( Re ` -u S ) = -u ( Re ` S )')
    rsr = st([sc], 'recld', '( Re ` S ) e. RR')
    le0 = lin.linarith(w, a, [f['0 <_ ( Re ` S )']], '-u ( Re ` S ) <_ 0', leaves={'( Re ` S )': rsr})
    cl = st([st([kr, k1], 'jca', '( %s e. RR /\\ 1 <_ %s )' % (K, K)), st([st([rsr], 'renegcld', '-u ( Re ` S ) e. RR'), st([], '0red', '0 e. RR')], 'jca',
                                                                            '( -u ( Re ` S ) e. RR /\\ 0 e. RR )'), le0, w.inst('cxplea')], 'syl3anc',
            '( %s ^c -u ( Re ` S ) ) <_ ( %s ^c 0 )' % (K, K))
    c0 = st([kc, w.inst('cxp0')], 'syl', '( %s ^c 0 ) = 1' % K)
    kb = st([st([ab, st([rn], 'oveq2d', '( %s ^c ( Re ` -u S ) ) = ( %s ^c -u ( Re ` S ) )' % (K, K))], 'eqtrd',
                '( abs ` ( %s ^c -u S ) ) = ( %s ^c -u ( Re ` S ) )' % (K, K)), st([cl, c0], 'breqtrd', '( %s ^c -u ( Re ` S ) ) <_ 1' % K)], 'eqbrtrd',
            '( abs ` ( %s ^c -u S ) ) <_ 1' % K)
    IQ = '( ( 1 / %s ) x. ( Q ` %s ) )' % (K, K)
    iqc = st([st([ik], 'recnd', '( 1 / %s ) e. CC' % K), qkc], 'mulcld', '%s e. CC' % IQ)
    a1_ = st([st([st([ik], 'recnd', '( 1 / %s ) e. CC' % K), qkc], 'absmuld', '( abs ` %s ) = ( ( abs ` ( 1 / %s ) ) x. ( abs ` ( Q ` %s ) ) )' % (IQ, K, K)),
              st([st([ik, ik0], 'absidd', '( abs ` ( 1 / %s ) ) = ( 1 / %s )' % (K, K))], 'oveq1d',
                 '( ( abs ` ( 1 / %s ) ) x. ( abs ` ( Q ` %s ) ) ) = ( ( 1 / %s ) x. ( abs ` ( Q ` %s ) ) )' % (K, K, K, K))], 'eqtrd',
             '( abs ` %s ) = ( ( 1 / %s ) x. ( abs ` ( Q ` %s ) ) )' % (IQ, K, K))
    aqr = st([qkc], 'abscld', '( abs ` ( Q ` %s ) ) e. RR' % K)
    b1 = st([a1_, st([aqr, f['H e. RR'], ik, ik0, qb], 'lemul2ad', '( ( 1 / %s ) x. ( abs ` ( Q ` %s ) ) ) <_ ( ( 1 / %s ) x. H )' % (K, K, K))], 'eqbrtrd',
            '( abs ` %s ) <_ ( ( 1 / %s ) x. H )' % (IQ, K))
    cnc = st([iqc, ksc], 'mulcld', '%s e. CC' % CN(K))
    IH = '( ( 1 / %s ) x. H )' % K
    ihr = st([ik, f['H e. RR']], 'remulcld', '%s e. RR' % IH)
    b2 = st([st([iqc], 'abscld', '( abs ` %s ) e. RR' % IQ), ihr, st([ksc], 'abscld', '( abs ` ( %s ^c -u S ) ) e. RR' % K), st([], '1red', '1 e. RR'),
             st([iqc], 'absge0d', '0 <_ ( abs ` %s )' % IQ), st([ksc], 'absge0d', '0 <_ ( abs ` ( %s ^c -u S ) )' % K), b1, kb], 'lemul12ad',
            '( ( abs ` %s ) x. ( abs ` ( %s ^c -u S ) ) ) <_ ( %s x. 1 )' % (IQ, K, IH))
    b3 = st([st([iqc, ksc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` ( %s ^c -u S ) ) )' % (CN(K), IQ, K)), b2], 'eqbrtrd',
            '( abs ` %s ) <_ ( %s x. 1 )' % (CN(K), IH))
    b4 = st([b3, st([st([ihr], 'recnd', '%s e. CC' % IH)], 'mulridd', '( %s x. 1 ) = %s' % (IH, IH))], 'breqtrd', '( abs ` %s ) <_ %s' % (CN(K), IH))
    return dict(cnc=cnc, cnb=b4, ihr=ihr, krp=krp, kr=kr, kc=kc, k1=k1, ik=ik, ik0=ik0, qkc=qkc, ksc=ksc)


def kgb(w, a, f, c, vc, rv, rvr, V):
    """( abs ` KG(K,V) ) <_ ( ( ; ; 1 2 8 x. KH ) x. EE ) and KG e. CC, for Re V = 1; c = cnb facts"""
    st = mkst(w, a)
    GY = '( ( _G ` %s ) x. ( K ^c -u %s ) )' % (V, V)
    h1 = st([a1(w, a, num.le_lit(w, '( 1 / 2 )', '1'), '( 1 / 2 ) <_ 1'), rv], 'breqtrrd', '( 1 / 2 ) <_ ( Re ` %s )' % V)
    h2 = st([rv, a1(w, a, num.le_lit(w, '1', '3'), '1 <_ 3')], 'eqbrtrd', '( Re ` %s ) <_ 3' % V)
    gy = st([c['krp'], st([vc, st([h1, h2], 'jca', '( ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 )' % (V, V))], 'jca',
                           '( %s e. CC /\\ ( ( 1 / 2 ) <_ ( Re ` %s ) /\\ ( Re ` %s ) <_ 3 ) )' % (V, V, V)), w.inst('z6gyr')], 'syl2anc',
            '( abs ` %s ) <_ ( %s x. ( 2 ^c -u ( ( abs ` ( Im ` %s ) ) / 4 ) ) )' % (GY, MYF('K'), V))
    E4, e4p, e41 = e4le1(w, a, vc, V)
    krp = c['krp']
    kh = st([krp, litr(w, a, '-u ( 1 / 2 )')], 'rpcxpcld', '%s e. RR+' % KH)
    k3 = st([krp, litr(w, a, '-u 3')], 'rpcxpcld', '( K ^c -u 3 ) e. RR+')
    myr = st([a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), st([st([kh, k3], 'rpaddcld', '( %s + ( K ^c -u 3 ) ) e. RR+' % KH)], 'rpred', '( %s + ( K ^c -u 3 ) ) e. RR' % KH)],
             'remulcld', '%s e. RR' % MYF('K'))
    my0 = st([a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), st([st([kh, k3], 'rpaddcld', '( %s + ( K ^c -u 3 ) ) e. RR+' % KH)], 'rpred', '( %s + ( K ^c -u 3 ) ) e. RR' % KH),
              a1(w, a, num.ge0_nat(w, 64), '0 <_ ; 6 4'), st([st([kh, k3], 'rpaddcld', '( %s + ( K ^c -u 3 ) ) e. RR+' % KH)], 'rpge0d', '0 <_ ( %s + ( K ^c -u 3 ) )' % KH)],
             'mulge0d', '0 <_ %s' % MYF('K'))
    m1 = st([st([e4p], 'rpred', '%s e. RR' % E4), st([], '1red', '1 e. RR'), myr, my0, e41], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 1 )' % (MYF('K'), E4, MYF('K')))
    m2 = st([m1, st([st([myr], 'recnd', '%s e. CC' % MYF('K'))], 'mulridd', '( %s x. 1 ) = %s' % (MYF('K'), MYF('K')))], 'breqtrd', '( %s x. %s ) <_ %s' % (MYF('K'), E4, MYF('K')))
    # MYF ( K ) <_ 128 KH
    k3le = st([st([c['kr'], c['k1']], 'jca', '( K e. RR /\\ 1 <_ K )'), st([litr(w, a, '-u 3'), litr(w, a, '-u ( 1 / 2 )')], 'jca', '( -u 3 e. RR /\\ -u ( 1 / 2 ) e. RR )'),
               lin.linarith(w, a, [], '-u 3 <_ -u ( 1 / 2 )'), w.inst('cxplea')], 'syl3anc', '( K ^c -u 3 ) <_ %s' % KH)
    khr = st([kh], 'rpred', '%s e. RR' % KH)
    sm = st([st([kh], 'rpred', '%s e. RR' % KH), st([k3], 'rpred', '( K ^c -u 3 ) e. RR'), khr, khr, st([khr], 'leidd', '%s <_ %s' % (KH, KH)), k3le], 'le2addd',
            '( %s + ( K ^c -u 3 ) ) <_ ( %s + %s )' % (KH, KH, KH))
    s64 = st([st([st([kh, k3], 'rpaddcld', '( %s + ( K ^c -u 3 ) ) e. RR+' % KH)], 'rpred', '( %s + ( K ^c -u 3 ) ) e. RR' % KH), st([khr, khr], 'readdcld', '( %s + %s ) e. RR' % (KH, KH)),
              a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), a1(w, a, num.ge0_nat(w, 64), '0 <_ ; 6 4'), sm], 'lemul2ad', '%s <_ ( ; 6 4 x. ( %s + %s ) )' % (MYF('K'), KH, KH))
    K128 = '( ; ; 1 2 8 x. %s )' % KH
    rq = ringeq(w, a, '( ; 6 4 x. ( %s + %s ) )' % (KH, KH), K128, Closure(w, a, {KH: khr}))
    myb = st([s64, rq], 'breqtrd', '%s <_ %s' % (MYF('K'), K128))
    k128r = st([a1(w, a, num.re_nat(w, 128), '; ; 1 2 8 e. RR'), khr], 'remulcld', '%s e. RR' % K128)
    gyc = st([gy, w.inst('z6absle')], 'syl', '%s e. CC' % GY)
    gyr = st([gyc], 'abscld', '( abs ` %s ) e. RR' % GY)
    gyb = st([gyr, st([myr, st([e4p], 'rpred', '%s e. RR' % E4)], 'remulcld', '( %s x. %s ) e. RR' % (MYF('K'), E4)), k128r, gy,
              st([st([myr, st([e4p], 'rpred', '%s e. RR' % E4)], 'remulcld', '( %s x. %s ) e. RR' % (MYF('K'), E4)), myr, k128r, m2, myb], 'letrd',
                 '( %s x. %s ) <_ %s' % (MYF('K'), E4, K128))], 'letrd', '( abs ` %s ) <_ %s' % (GY, K128))
    # | KK ( V ) | <_ EE
    kb = st([st([st([st([f['A e. RR'], f['B e. RR']], 'jca', '( A e. RR /\\ B e. RR )'), st([f['0 <_ A'], f['0 <_ B']], 'jca', '( 0 <_ A /\\ 0 <_ B )')], 'jca',
                    '( ( A e. RR /\\ B e. RR ) /\\ ( 0 <_ A /\\ 0 <_ B ) )'), f['L e. RR+'], vc, w.inst('gf1kb')], 'syl3anc',
                tsub(split_imp(G1L.S['gf1kb'])[1], {'W': V}))], 'simprd', '( ( Re ` %s ) <_ 1 -> ( abs ` %s ) <_ %s )' % (V, KKv(V), EE))
    kkb = st([st([rvr, rv], 'eqled', '( Re ` %s ) <_ 1' % V), kb], 'mpd', '( abs ` %s ) <_ %s' % (KKv(V), EE))
    return dict(gyb=gyb, gyc=gyc, kkb=kkb, k128r=k128r, K128=K128, GY=GY, khr=khr, kh=kh)


def fbb(w, a, f, c, g, V):
    """( abs ` FB(K,V) ) <_ ( K0 x. N32(K) ), FB e. CC"""
    st = mkst(w, a)
    kkc = st([g['kkb'], w.inst('z6absle')], 'syl', '%s e. CC' % KKv(V))
    kgc = st([g['gyc'], kkc], 'mulcld', '%s e. CC' % KG('K', V))
    eer = st([st([st([f['B e. RR'], st([f['L e. RR+']], 'rpred', 'L e. RR')], 'readdcld', '( B + L ) e. RR')], 'rpefcld', '( exp ` ( B + L ) ) e. RR+'),
              st([st([f['A e. RR'], st([f['L e. RR+']], 'rpred', 'L e. RR')], 'readdcld', '( A + L ) e. RR')], 'rpefcld', '( exp ` ( A + L ) ) e. RR+')], 'rpaddcld', '%s e. RR+' % EE)
    KB = '( %s x. %s )' % (g['K128'], EE)
    kbr = st([g['k128r'], st([eer], 'rpred', '%s e. RR' % EE)], 'remulcld', '%s e. RR' % KB)
    b1 = st([st([g['gyc'], kkc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (KG('K', V), g['GY'], KKv(V))),
             st([st([g['gyc']], 'abscld', '( abs ` %s ) e. RR' % g['GY']), g['k128r'], st([kkc], 'abscld', '( abs ` %s ) e. RR' % KKv(V)), st([eer], 'rpred', '%s e. RR' % EE),
                 st([g['gyc']], 'absge0d', '0 <_ ( abs ` %s )' % g['GY']), st([kkc], 'absge0d', '0 <_ ( abs ` %s )' % KKv(V)), g['gyb'], g['kkb']], 'lemul12ad',
                '( ( abs ` %s ) x. ( abs ` %s ) ) <_ %s' % (g['GY'], KKv(V), KB))], 'eqbrtrd', '( abs ` %s ) <_ %s' % (KG('K', V), KB))
    IH = '( ( 1 / K ) x. H )'
    b2 = st([st([c['cnc'], kgc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (FB('K', V), CN('K'), KG('K', V))),
             st([st([c['cnc']], 'abscld', '( abs ` %s ) e. RR' % CN('K')), c['ihr'], st([kgc], 'abscld', '( abs ` %s ) e. RR' % KG('K', V)), kbr,
                 st([c['cnc']], 'absge0d', '0 <_ ( abs ` %s )' % CN('K')), st([kgc], 'absge0d', '0 <_ ( abs ` %s )' % KG('K', V)), c['cnb'], b1], 'lemul12ad',
                '( ( abs ` %s ) x. ( abs ` %s ) ) <_ ( %s x. %s )' % (CN('K'), KG('K', V), IH, KB))], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. %s )' % (FB('K', V), IH, KB))
    # ( 1 / K ) KH = K ^c -u ( 3 / 2 )
    knz = st([c['krp']], 'rpne0d', 'K =/= 0')
    e1 = st([c['kc'], knz, st([], '1cnd', '1 e. CC')], 'cxpnegd', '( K ^c -u 1 ) = ( 1 / ( K ^c 1 ) )')
    e2 = st([e1, st([st([c['kc']], 'cxp1d', '( K ^c 1 ) = K')], 'oveq2d', '( 1 / ( K ^c 1 ) ) = ( 1 / K )')], 'eqtrd', '( K ^c -u 1 ) = ( 1 / K )')
    nh = a1(w, a, w.s([w.s([], 'halfcn', '( 1 / 2 ) e. CC')], 'negcli', '-u ( 1 / 2 ) e. CC'), '-u ( 1 / 2 ) e. CC')
    n1 = a1(w, a, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'negcli', '-u 1 e. CC'), '-u 1 e. CC')
    e3 = st([c['kc'], knz, n1, nh], 'cxpaddd', '( K ^c ( -u 1 + -u ( 1 / 2 ) ) ) = ( ( K ^c -u 1 ) x. %s )' % KH)
    n32 = ringeq(w, a, '( -u 1 + -u ( 1 / 2 ) )', '-u ( 3 / 2 )', Closure(w, a, {}))
    e4 = st([st([st([n32], 'oveq2d', '( K ^c ( -u 1 + -u ( 1 / 2 ) ) ) = %s' % N32('K'))], 'eqcomd', '%s = ( K ^c ( -u 1 + -u ( 1 / 2 ) ) )' % N32('K')),
             st([e3, st([e2], 'oveq1d', '( ( K ^c -u 1 ) x. %s ) = ( ( 1 / K ) x. %s )' % (KH, KH))], 'eqtrd', '( K ^c ( -u 1 + -u ( 1 / 2 ) ) ) = ( ( 1 / K ) x. %s )' % KH)],
            'eqtrd', '%s = ( ( 1 / K ) x. %s )' % (N32('K'), KH))
    cl = Closure(w, a, {'( 1 / K )': c['ik'], 'H': f['H e. RR'], KH: g['khr'], EE: st([eer], 'rpred', '%s e. RR' % EE)})
    rq = ringeq(w, a, '( %s x. %s )' % (IH, KB), '( %s x. ( ( 1 / K ) x. %s ) )' % (K0, KH), cl)
    fin = st([b2, st([rq, st([e4], 'oveq2d', '( %s x. %s ) = ( %s x. ( ( 1 / K ) x. %s ) )' % (K0, N32('K'), K0, KH))], 'eqtr4d',
                     '( %s x. %s ) = ( %s x. %s )' % (IH, KB, K0, N32('K')))], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (FB('K', V), K0, N32('K')))
    return fin, kgc


def gf2anp():
    w = W('gf2anp', 'The terms of the Mellin-expanded anchor series on the segment ` 1 - i T -- 1 + i T ` : its points have real part 1 and lie '
          'in the domain of Gamma; the value of the ` K ` -th term there and its majorant ` K0 K ^ -u ( 3 / 2 ) ` (Lean ` norm_Tanc_le ` ; '
          '~ z6gyr , ~ gf1kb , ~ abscxp ).')
    a = split_imp(S_['gf2anp'])[0]
    from gf1lib import proj
    st = mkst(w, a)
    f = ahf(w, a, None)
    tr = st([proj(w, a, 'T e. RR+')], 'rpred', 'T e. RR'); kn = proj(w, a, 'K e. NN'); vm = proj(w, a, 'V e. %s' % SEG)
    sf = segf(w, a, tr)
    rv, vc, vdg, rvr = ptf(w, a, sf, vm, 'V')
    c = cnb(w, a, f, kn, 'K')
    g = kgb(w, a, f, c, vc, rv, rvr, 'V')
    bnd, kgc = fbb(w, a, f, c, g, 'V')
    FK = '( v e. %s |-> %s )' % (SEG, FB('K', 'v'))
    segv = st([], 'ovexd', '%s e. _V' % SEG)
    v1, _ = mpv(w, a, 'n', 'NN', '( v e. %s |-> %s )' % (SEG, FB('n', 'v')), 'K', kn, exs=st([segv], 'mptexd', '%s e. _V' % FK))
    v2 = st([v1], 'fveq1d', '( ( %s ` K ) ` V ) = ( %s ` V )' % (FNS, FK))
    v3, _ = mpv(w, a, 'v', SEG, FB('K', 'v'), 'V', vm)
    val = st([v2, v3], 'eqtrd', '( ( %s ` K ) ` V ) = %s' % (FNS, FB('K', 'V')))
    fin = st([st([rv, vdg], 'jca', '( ( Re ` V ) = 1 /\\ V e. %s )' % DG),
              st([val, bnd], 'jca', '( ( ( %s ` K ) ` V ) = %s /\\ ( abs ` %s ) <_ ( %s x. %s ) )' % (FNS, FB('K', 'V'), FB('K', 'V'), K0, N32('K')))],
             'jca', split_imp(S_['gf2anp'])[1])
    w.qed([fin], 'idi', S_['gf2anp'])
    return w


ZS = lambda n, v: '( ( Q ` %s ) x. ( %s ^c -u ( ( 1 + S ) + %s ) ) )' % (n, n, v)
GAB = lambda v: '( ( ( _G ` %s ) x. %s ) x. sum_ n e. NN %s )' % (v, KKv(v), ZS('n', v))
GA = '( w e. %s |-> %s )' % (DG, GAB('w'))
MN = '( n e. NN |-> ( %s x. %s ) )' % (K0, N32('n'))
S_['gf2anl'] = '( ( %s /\\ T e. RR+ ) -> seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) ~~> %s )' % (AH, FNS, SA, SB, LIt(GA, '1', 'T'))


def k0real(w, a, f):
    st = mkst(w, a)
    lr = st([f['L e. RR+']], 'rpred', 'L e. RR')
    eer = st([st([st([f['B e. RR'], lr], 'readdcld', '( B + L ) e. RR')], 'rpefcld', '( exp ` ( B + L ) ) e. RR+'),
              st([st([f['A e. RR'], lr], 'readdcld', '( A + L ) e. RR')], 'rpefcld', '( exp ` ( A + L ) ) e. RR+')], 'rpaddcld', '%s e. RR+' % EE)
    c128 = a1(w, a, num.re_nat(w, 128), '; ; 1 2 8 e. RR')
    k0r = st([st([c128, f['H e. RR']], 'remulcld', '( ; ; 1 2 8 x. H ) e. RR'), st([eer], 'rpred', '%s e. RR' % EE)], 'remulcld', '%s e. RR' % K0)
    return k0r, eer


def n32f(w, a, kn, k):
    st = mkst(w, a)
    return st([st([kn], 'nnrpd', '%s e. RR+' % k), litr(w, a, '-u ( 3 / 2 )')], 'rpcxpcld', '%s e. RR+' % N32(k))


def zcv32(w, a):
    """( a -> seq 1 ( + , ( n e. NN |-> N32(n) ) ) e. dom ~~> )"""
    st = mkst(w, a)
    ak = '( %s /\\ k e. NN )' % a
    zv, _ = mpv(w, ak, 'n', 'NN', N32('n'), 'k', w.s([], 'simpr', '( %s -> k e. NN )' % ak))
    c32 = a1(w, a, w.s([w.s([], '3cn', '3 e. CC'), w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0')], 'divcli', '( 3 / 2 ) e. CC'), '( 3 / 2 ) e. CC')
    r32 = a1(w, a, w.s([num.real(w, '( 3 / 2 )'), w.inst('rere')], 'ax-mp', '( Re ` ( 3 / 2 ) ) = ( 3 / 2 )'), '( Re ` ( 3 / 2 ) ) = ( 3 / 2 )')
    lt = st([lin.linarith(w, a, [], '1 < ( 3 / 2 )'), r32], 'breqtrrd', '1 < ( Re ` ( 3 / 2 ) )')
    return st([c32, lt, zv], 'zetacvg', 'seq 1 ( + , ( n e. NN |-> %s ) ) e. dom ~~>' % N32('n'))


def liftd(w, d, ctx):
    return {k: lift(w, v, ctx) for k, v in d.items()}


def kkcc(w, a, f, vc, V):
    """KK ( V ) e. CC (gf1kq)"""
    st = mkst(w, a)
    kq = st([st([f['A e. RR'], f['B e. RR']], 'jca', '( A e. RR /\\ B e. RR )'), f['L e. RR+'], vc, w.inst('gf1kq')], 'syl3anc',
            tsub(split_imp(G1L.S['gf1kq'])[1], {'W': V}))
    KQV = G1L.KQ('A', 'B', 'L', V)
    return st([st([kq], 'simprd', '%s = ( %s x. %s )' % (KKv(V), V, KQV)), st([vc, st([kq], 'simpld', '%s e. CC' % KQV)], 'mulcld', '( %s x. %s ) e. CC' % (V, KQV))],
              'eqeltrd', '%s e. CC' % KKv(V))


def mk0ge(w, a, f, eer):
    """0 <_ H (from | Q ( 1 ) | <_ H) and 0 <_ K0"""
    st = mkst(w, a)
    one = a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    rsp = w.s([w.s([w.s([], 'fveq2', '( j = 1 -> ( Q ` j ) = ( Q ` 1 ) )')], 'fveq2d', '( j = 1 -> ( abs ` ( Q ` j ) ) = ( abs ` ( Q ` 1 ) ) )')],
              'breq1d', '( j = 1 -> ( ( abs ` ( Q ` j ) ) <_ H <-> ( abs ` ( Q ` 1 ) ) <_ H ) )')
    q1 = st([rsp, f['A. j e. NN ( abs ` ( Q ` j ) ) <_ H'], one], 'rspcdva', '( abs ` ( Q ` 1 ) ) <_ H')
    q1c = st([f['Q : NN --> CC'], one], 'ffvelcdmd', '( Q ` 1 ) e. CC')
    h0 = st([st([], '0red', '0 e. RR'), st([q1c], 'abscld', '( abs ` ( Q ` 1 ) ) e. RR'), f['H e. RR'], st([q1c], 'absge0d', '0 <_ ( abs ` ( Q ` 1 ) )'), q1],
            'letrd', '0 <_ H')
    c128 = a1(w, a, num.re_nat(w, 128), '; ; 1 2 8 e. RR')
    k0 = st([st([c128, f['H e. RR']], 'remulcld', '( ; ; 1 2 8 x. H ) e. RR'), st([eer], 'rpred', '%s e. RR' % EE),
             st([c128, f['H e. RR'], a1(w, a, num.ge0_nat(w, 128), '0 <_ ; ; 1 2 8'), h0], 'mulge0d', '0 <_ ( ; ; 1 2 8 x. H )'), st([eer], 'rpge0d', '0 <_ %s' % EE)],
            'mulge0d', '0 <_ %s' % K0)
    return k0


def fnscn(w, an, fn_, cn_, sf, sdg, n):
    """( an -> ( v e. SEG |-> FB(n,v) ) e. ( SEG -cn-> CC ) )"""
    tn = mkst(w, an)
    segcc = lift(w, sf['segcc'], an); sdgn = lift(w, sdg, an)
    dgcc = a1(w, an, w.s([], 'difss', '%s C_ CC' % DG), '%s C_ CC' % DG)
    ccss = a1(w, an, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    nf = w.s([], 'nfv', 'F/ v %s' % an)
    idm = tn([sdgn, dgcc, w.inst('cncfmptid')], 'syl2anc', '( v e. %s |-> v ) e. ( %s -cn-> %s )' % (SEG, SEG, DG))
    GZ = '( z e. %s |-> ( _G ` z ) )' % DG
    gam = a1(w, an, w.s([w.s([], 'z6gamhold', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (GZ, DG, DG, GZ))], 'simpli', '%s e. ( %s -cn-> CC )' % (GZ, DG)),
             '%s e. ( %s -cn-> CC )' % (GZ, DG))
    g1 = tn([nf, idm, gam, a1(w, an, w.s([], 'ssid', '%s C_ %s' % (DG, DG)), '%s C_ %s' % (DG, DG)), w.s([], 'fveq2', '( z = v -> ( _G ` z ) = ( _G ` v ) )')], 'cncfcompt2',
            '( v e. %s |-> ( _G ` v ) ) e. ( %s -cn-> CC )' % (SEG, SEG))
    NG = '( v e. %s |-> -u v )' % SEG
    ng = w.s([segcc, w.s([w.s([], 'eqid', '%s = %s' % (NG, NG))], 'negcncf', '( %s C_ CC -> %s e. ( %s -cn-> CC ) )' % (SEG, NG, SEG))], 'syl',
             '( %s -> %s e. ( %s -cn-> CC ) )' % (an, NG, SEG))
    cx = tn([cn_['krp'], ccss, w.inst('cxfcn')], 'syl2anc', '( z e. CC |-> ( %s ^c z ) ) e. ( CC -cn-> CC )' % n)
    g2 = tn([nf, ng, cx, ccss, w.s([], 'oveq2', '( z = -u v -> ( %s ^c z ) = ( %s ^c -u v ) )' % (n, n))], 'cncfcompt2', '( v e. %s |-> ( %s ^c -u v ) ) e. ( %s -cn-> CC )' % (SEG, n, SEG))
    g12 = w.s([g1, g2], 'mulcncf', '( %s -> ( v e. %s |-> ( ( _G ` v ) x. ( %s ^c -u v ) ) ) e. ( %s -cn-> CC ) )' % (an, SEG, n, SEG))
    KKF = '( w e. CC |-> %s )' % KKv('w')
    avh = tn([tn([fn_['A e. RR'], fn_['B e. RR']], 'jca', '( A e. RR /\\ B e. RR )'), fn_['L e. RR+'], w.inst('gf1avgh')], 'syl2anc',
             split_imp(G1L.S['gf1avgh'])[1])
    kkf = tn([tn([avh], 'simprd', G1L.HOL(KKF, 'CC'))], 'simpld', '%s e. ( CC -cn-> CC )' % KKF)
    idc = tn([segcc, ccss, w.inst('cncfmptid')], 'syl2anc', '( v e. %s |-> v ) e. ( %s -cn-> CC )' % (SEG, SEG))
    idwv = w.s([], 'id', '( w = v -> w = v )')
    kst, kval = w.congr(KKv('w'), {'w': 'v'}, 'w = v', {'w': idwv})
    g3 = tn([nf, idc, kkf, ccss, kst], 'cncfcompt2', '( v e. %s |-> %s ) e. ( %s -cn-> CC )' % (SEG, KKv('v'), SEG))
    g123 = w.s([g12, g3], 'mulcncf', '( %s -> ( v e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (an, SEG, KG(n, 'v'), SEG))
    cm = tn([cn_['cnc'], segcc, ccss, w.inst('cncfmptc')], 'syl3anc', '( v e. %s |-> %s ) e. ( %s -cn-> CC )' % (SEG, CN(n), SEG))
    fcn = w.s([cm, g123], 'mulcncf', '( %s -> ( v e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (an, SEG, FB(n, 'v'), SEG))
    return fcn


def gf2anl():
    w = W('gf2anl', 'At every height ` T ` the ` n ` -series of the Mellin terms, integrated termwise along ` 1 - i T -- 1 + i T ` , converges '
          'to the segment integral of the anchor integrand ` GA ` (Lean ` integral_tsum_of_summable_integral_norm ` , ` tsum_Tanc ` ; '
          '~ z6lsum with the majorant of ~ gf2anp , ~ zetacvg , ~ isummulc2 ).')
    a = split_imp(S_['gf2anl'])[0]; st = mkst(w, a); f = ahf(w, a, None)
    trp = proj(w, a, 'T e. RR+'); tr = st([trp], 'rpred', 'T e. RR')
    sf = segf(w, a, tr)
    au = '( %s /\\ q e. %s )' % (a, SEG)
    ru, uc, udg, urr = ptf(w, au, liftd(w, sf, au), w.s([], 'simpr', '( %s -> q e. %s )' % (au, SEG)), 'q')
    sdg = st([w.s([udg], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (a, SEG, DG))], 'ssrdv', '%s C_ %s' % (SEG, DG))
    # FNS : NN --> ( SEG -cn-> CC )
    an = '( %s /\\ n e. NN )' % a; tn = mkst(w, an)
    nn = tn([], 'simpr', 'n e. NN')
    fn_ = liftd(w, f, an)
    cn_ = cnb(w, an, fn_, nn, 'n')
    segcc = lift(w, sf['segcc'], an); sdgn = lift(w, sdg, an)
    dgcc = a1(w, an, w.s([], 'difss', '%s C_ CC' % DG), '%s C_ CC' % DG)
    ccss = a1(w, an, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    nf = w.s([], 'nfv', 'F/ v %s' % an)
    idm = tn([sdgn, dgcc, w.inst('cncfmptid')], 'syl2anc', '( v e. %s |-> v ) e. ( %s -cn-> %s )' % (SEG, SEG, DG))
    GZ = '( z e. %s |-> ( _G ` z ) )' % DG
    gam = a1(w, an, w.s([w.s([], 'z6gamhold', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (GZ, DG, DG, GZ))], 'simpli', '%s e. ( %s -cn-> CC )' % (GZ, DG)),
             '%s e. ( %s -cn-> CC )' % (GZ, DG))
    g1 = tn([nf, idm, gam, a1(w, an, w.s([], 'ssid', '%s C_ %s' % (DG, DG)), '%s C_ %s' % (DG, DG)), w.s([], 'fveq2', '( z = v -> ( _G ` z ) = ( _G ` v ) )')], 'cncfcompt2',
            '( v e. %s |-> ( _G ` v ) ) e. ( %s -cn-> CC )' % (SEG, SEG))
    NG = '( v e. %s |-> -u v )' % SEG
    ng = w.s([segcc, w.s([w.s([], 'eqid', '%s = %s' % (NG, NG))], 'negcncf', '( %s C_ CC -> %s e. ( %s -cn-> CC ) )' % (SEG, NG, SEG))], 'syl',
             '( %s -> %s e. ( %s -cn-> CC ) )' % (an, NG, SEG))
    cx = tn([cn_['krp'], ccss, w.inst('cxfcn')], 'syl2anc', '( z e. CC |-> ( n ^c z ) ) e. ( CC -cn-> CC )')
    g2 = tn([nf, ng, cx, ccss, w.s([], 'oveq2', '( z = -u v -> ( n ^c z ) = ( n ^c -u v ) )')], 'cncfcompt2', '( v e. %s |-> ( n ^c -u v ) ) e. ( %s -cn-> CC )' % (SEG, SEG))
    g12 = w.s([g1, g2], 'mulcncf', '( %s -> ( v e. %s |-> ( ( _G ` v ) x. ( n ^c -u v ) ) ) e. ( %s -cn-> CC ) )' % (an, SEG, SEG))
    KKF = '( w e. CC |-> %s )' % KKv('w')
    avh = tn([tn([fn_['A e. RR'], fn_['B e. RR']], 'jca', '( A e. RR /\\ B e. RR )'), fn_['L e. RR+'], w.inst('gf1avgh')], 'syl2anc',
             split_imp(G1L.S['gf1avgh'])[1])
    kkf = tn([tn([avh], 'simprd', G1L.HOL(KKF, 'CC'))], 'simpld', '%s e. ( CC -cn-> CC )' % KKF)
    idc = tn([segcc, ccss, w.inst('cncfmptid')], 'syl2anc', '( v e. %s |-> v ) e. ( %s -cn-> CC )' % (SEG, SEG))
    idwv = w.s([], 'id', '( w = v -> w = v )')
    kst, kval = w.congr(KKv('w'), {'w': 'v'}, 'w = v', {'w': idwv})
    g3 = tn([nf, idc, kkf, ccss, kst], 'cncfcompt2', '( v e. %s |-> %s ) e. ( %s -cn-> CC )' % (SEG, KKv('v'), SEG))
    g123 = w.s([g12, g3], 'mulcncf', '( %s -> ( v e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (an, SEG, KG('n', 'v'), SEG))
    cm = tn([cn_['cnc'], segcc, ccss, w.inst('cncfmptc')], 'syl3anc', '( v e. %s |-> %s ) e. ( %s -cn-> CC )' % (SEG, CN('n'), SEG))
    fcn = w.s([cm, g123], 'mulcncf', '( %s -> ( v e. %s |-> %s ) e. ( %s -cn-> CC ) )' % (an, SEG, FB('n', 'v'), SEG))
    CNS = '( %s -cn-> CC )' % SEG
    ffn = st([fcn, w.s([], 'eqid', '%s = %s' % (FNS, FNS))], 'fmptd', '%s : NN --> %s' % (FNS, CNS))
    # the majorant sequence
    k0r, eer = k0real(w, a, f)
    mnr = tn([lift(w, k0r, an), tn([n32f(w, an, nn, 'n')], 'rpred', '%s e. RR' % N32('n'))], 'remulcld', '( %s x. %s ) e. RR' % (K0, N32('n')))
    mf = st([mnr, w.s([], 'eqid', '%s = %s' % (MN, MN))], 'fmptd', '%s : NN --> RR' % MN)
    ZF = '( n e. NN |-> %s )' % N32('n')
    zc = zcv32(w, a)
    ak = '( %s /\\ k e. NN )' % a; tk = mkst(w, ak)
    kn = tk([], 'simpr', 'k e. NN')
    zv, _ = mpv(w, ak, 'n', 'NN', N32('n'), 'k', kn)
    k32 = n32f(w, ak, kn, 'k')
    zkre = tk([zv, tk([k32], 'rpred', '%s e. RR' % N32('k'))], 'eqeltrd', '( %s ` k ) e. RR' % ZF)
    mv, _ = mpv(w, ak, 'n', 'NN', '( %s x. %s )' % (K0, N32('n')), 'k', kn)
    mkr = tk([lift(w, k0r, ak), tk([k32], 'rpred', '%s e. RR' % N32('k'))], 'remulcld', '( %s x. %s ) e. RR' % (K0, N32('k')))
    mkc = tk([mv, tk([mkr], 'recnd', '( %s x. %s ) e. CC' % (K0, N32('k')))], 'eqeltrd', '( %s ` k ) e. CC' % MN)
    k0ge = mk0ge(w, a, f, eer)
    amk = tk([tk([mv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` ( %s x. %s ) )' % (MN, K0, N32('k'))),
              tk([mkr, tk([lift(w, k0r, ak), tk([k32], 'rpred', '%s e. RR' % N32('k')), lift(w, k0ge, ak), tk([k32], 'rpge0d', '0 <_ %s' % N32('k'))], 'mulge0d',
                          '0 <_ ( %s x. %s )' % (K0, N32('k')))], 'absidd', '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (K0, N32('k'), K0, N32('k')))], 'eqtrd',
             '( abs ` ( %s ` k ) ) = ( %s x. %s )' % (MN, K0, N32('k')))
    amk2 = tk([amk, tk([tk([zv], 'eqcomd', '%s = ( %s ` k )' % (N32('k'), ZF))], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s ` k ) )' % (K0, N32('k'), K0, ZF))], 'eqtrd',
              '( abs ` ( %s ` k ) ) = ( %s x. ( %s ` k ) )' % (MN, K0, ZF))
    le_ = tk([tk([mkc], 'abscld', '( abs ` ( %s ` k ) ) e. RR' % MN), amk2], 'eqled', '( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) )' % (MN, K0, ZF))
    ak1 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % a
    kn1 = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % ak1), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleq2i', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                     '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'syl', '( %s -> k e. NN )' % ak1)
    le_1 = w.s([w.s([w.s([le_], 'ex', '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) ) ) )' % (a, MN, K0, ZF))], 'adantr',
                    '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) ) ) )' % (ak1, MN, K0, ZF)), kn1], 'mpd',
               '( %s -> ( abs ` ( %s ` k ) ) <_ ( %s x. ( %s ` k ) ) )' % (ak1, MN, K0, ZF))
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')
    mcv = st([nnuz, a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN'), zkre, mkc, zc, k0r, le_1], 'cvgcmpce', 'seq 1 ( + , %s ) e. dom ~~>' % MN)
    # the bound for every h , y
    ajy = '( %s /\\ ( h e. NN /\\ y e. %s ) )' % (a, SEG); tj = mkst(w, ajy)
    hn = tj([], 'simprl', 'h e. NN')
    pj = tj([proj(w, ajy, tsub(split_imp(S_['gf2anp'])[0], {'K': 'h', 'V': 'y'})), w.inst('gf2anp')], 'syl', tsub(split_imp(S_['gf2anp'])[1], {'K': 'h', 'V': 'y'}))
    pv = tj([pj], 'simprld', '( ( %s ` h ) ` y ) = %s' % (FNS, FB('h', 'y')))
    pb = tj([pj], 'simprrd', '( abs ` %s ) <_ ( %s x. %s )' % (FB('h', 'y'), K0, N32('h')))
    mj, _ = mpv(w, ajy, 'n', 'NN', '( %s x. %s )' % (K0, N32('n')), 'h', hn)
    bj = tj([tj([tj([pv], 'fveq2d', '( abs ` ( ( %s ` h ) ` y ) ) = ( abs ` %s )' % (FNS, FB('h', 'y'))), pb], 'eqbrtrd',
                '( abs ` ( ( %s ` h ) ` y ) ) <_ ( %s x. %s )' % (FNS, K0, N32('h'))), mj], 'breqtrrd', '( abs ` ( ( %s ` h ) ` y ) ) <_ ( %s ` h )' % (FNS, MN))
    MBND = 'A. h e. NN A. y e. %s ( abs ` ( ( %s ` h ) ` y ) ) <_ ( %s ` h )' % (SEG, FNS, MN)
    mb = st([bj], 'ralrimivva', MBND)
    LSH = '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s C_ %s /\\ ( %s : NN --> %s /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s ) ) ) )' % (
        SA, SB, SEG, SEG, FNS, CNS, MN, MN, MBND)
    lsh = st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)),
              st([st([], 'ssidd', '%s C_ %s' % (SEG, SEG)), st([ffn, st([mf, mcv, mb], '3jca', '( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s )' % (MN, MN, MBND))], 'jca',
                                                                '( %s : NN --> %s /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s ) )' % (FNS, CNS, MN, MN, MBND))],
                 'jca', '( %s C_ %s /\\ ( %s : NN --> %s /\\ ( %s : NN --> RR /\\ seq 1 ( + , %s ) e. dom ~~> /\\ %s ) ) )' % (SEG, SEG, FNS, CNS, MN, MN, MBND))],
             'jca', LSH)
    SUMM = '( b e. %s |-> sum_ k e. NN ( ( %s ` k ) ` b ) )' % (SEG, FNS)
    ls = st([lsh, w.inst('z6lsum')], 'syl', 'seq 1 ( + , ( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) ) ) ~~> ( %s lint <. %s , %s >. )' % (FNS, SA, SB, SUMM, SA, SB))
    # linteq: SUMM and GA agree on the segment
    cu = '( %s /\\ q e. %s )' % (a, SEG); tu = mkst(w, cu)
    um = tu([], 'simpr', 'q e. %s' % SEG)
    fu = liftd(w, f, cu)
    ru, uc, udg, urr = ptf(w, cu, liftd(w, sf, cu), um, 'q')
    s1, _ = mpv(w, cu, 'b', SEG, 'sum_ k e. NN ( ( %s ` k ) ` b )' % FNS, 'q', um,
                exs=w.s([w.s([], 'sumex', 'sum_ k e. NN ( ( %s ` k ) ` q ) e. _V' % FNS)], 'a1i', '( %s -> sum_ k e. NN ( ( %s ` k ) ` q ) e. _V )' % (cu, FNS)))
    GK = '( ( _G ` q ) x. %s )' % KKv('q')
    gu = tu([udg, w.inst('gamcl')], 'syl', '( _G ` q ) e. CC')
    kku = kkcc(w, cu, fu, uc, 'q')
    gkc = tu([gu, kku], 'mulcld', '%s e. CC' % GK)
    ck = '( %s /\\ k e. NN )' % cu; tk2 = mkst(w, ck)
    kk = tk2([], 'simpr', 'k e. NN')
    fk = liftd(w, fu, ck)
    ck_ = cnb(w, ck, fk, kk, 'k')
    pk = tk2([proj(w, ck, tsub(split_imp(S_['gf2anp'])[0], {'K': 'k', 'V': 'q'})), w.inst('gf2anp')], 'syl', tsub(split_imp(S_['gf2anp'])[1], {'K': 'k', 'V': 'q'}))
    pvk = tk2([pk], 'simprld', '( ( %s ` k ) ` q ) = %s' % (FNS, FB('k', 'q')))
    ucc = lift(w, uc, ck); scc = fk['S e. CC']
    knz = tk2([kk], 'nnne0d', 'k =/= 0')
    Z_ = '( ( 1 + S ) + q )'
    ng = ringeq(w, ck, '-u %s' % Z_, '( ( -u 1 + -u S ) + -u q )', Closure(w, ck, {'S': scc, 'q': ucc}))
    n1 = a1(w, ck, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'negcli', '-u 1 e. CC'), '-u 1 e. CC')
    nsc = tk2([scc], 'negcld', '-u S e. CC'); nuc = tk2([ucc], 'negcld', '-u q e. CC')
    c1 = tk2([ck_['kc'], knz, tk2([n1, nsc], 'addcld', '( -u 1 + -u S ) e. CC'), nuc], 'cxpaddd',
             '( k ^c ( ( -u 1 + -u S ) + -u q ) ) = ( ( k ^c ( -u 1 + -u S ) ) x. ( k ^c -u q ) )')
    c2 = tk2([ck_['kc'], knz, n1, nsc], 'cxpaddd', '( k ^c ( -u 1 + -u S ) ) = ( ( k ^c -u 1 ) x. ( k ^c -u S ) )')
    e1 = tk2([ck_['kc'], knz, tk2([], '1cnd', '1 e. CC')], 'cxpnegd', '( k ^c -u 1 ) = ( 1 / ( k ^c 1 ) )')
    e2 = tk2([e1, tk2([tk2([ck_['kc']], 'cxp1d', '( k ^c 1 ) = k')], 'oveq2d', '( 1 / ( k ^c 1 ) ) = ( 1 / k )')], 'eqtrd', '( k ^c -u 1 ) = ( 1 / k )')
    KZ = '( ( ( 1 / k ) x. ( k ^c -u S ) ) x. ( k ^c -u q ) )'
    kz = tk2([tk2([tk2([ng], 'oveq2d', '( k ^c -u %s ) = ( k ^c ( ( -u 1 + -u S ) + -u q ) )' % Z_), c1], 'eqtrd',
                  '( k ^c -u %s ) = ( ( k ^c ( -u 1 + -u S ) ) x. ( k ^c -u q ) )' % Z_),
              tk2([tk2([c2, tk2([e2], 'oveq1d', '( ( k ^c -u 1 ) x. ( k ^c -u S ) ) = ( ( 1 / k ) x. ( k ^c -u S ) )')], 'eqtrd',
                       '( k ^c ( -u 1 + -u S ) ) = ( ( 1 / k ) x. ( k ^c -u S ) )')], 'oveq1d',
                  '( ( k ^c ( -u 1 + -u S ) ) x. ( k ^c -u q ) ) = %s' % KZ)], 'eqtrd', '( k ^c -u %s ) = %s' % (Z_, KZ))
    kuc = tk2([ck_['kc'], nuc], 'cxpcld', '( k ^c -u q ) e. CC')
    cl = Closure(w, ck, {'( 1 / k )': ck_['ik'], '( Q ` k )': ck_['qkc'], '( k ^c -u S )': ck_['ksc'], '( _G ` q )': lift(w, gu, ck), '( k ^c -u q )': kuc,
                         KKv('q'): lift(w, kku, ck)})
    rq = ringeq(w, ck, FB('k', 'q'), '( %s x. ( ( Q ` k ) x. %s ) )' % (GK, KZ), cl)
    fbz = tk2([rq, tk2([tk2([kz], 'oveq2d', '( ( Q ` k ) x. ( k ^c -u %s ) ) = ( ( Q ` k ) x. %s )' % (Z_, KZ))], 'oveq2d',
                       '( %s x. %s ) = ( %s x. ( ( Q ` k ) x. %s ) )' % (GK, ZS('k', 'q'), GK, KZ))], 'eqtr4d', '%s = ( %s x. %s )' % (FB('k', 'q'), GK, ZS('k', 'q')))
    tv = tk2([pvk, fbz], 'eqtrd', '( ( %s ` k ) ` q ) = ( %s x. %s )' % (FNS, GK, ZS('k', 'q')))
    se = tu([tv], 'sumeq2dv', 'sum_ k e. NN ( ( %s ` k ) ` q ) = sum_ k e. NN ( %s x. %s )' % (FNS, GK, ZS('k', 'q')))
    # the Dirichlet series at ( 1 + S ) + q converges: | ZS | <_ H k ^ -3/2
    zkc = tk2([ck_['qkc'], tk2([ck_['kc'], tk2([tk2([tk2([tk2([], '1cnd', '1 e. CC'), scc], 'addcld', '( 1 + S ) e. CC'), ucc], 'addcld', '%s e. CC' % Z_)], 'negcld',
                                                  '-u %s e. CC' % Z_)], 'cxpcld', '( k ^c -u %s ) e. CC' % Z_)], 'mulcld', '%s e. CC' % ZS('k', 'q'))
    zcc = tk2([tk2([tk2([], '1cnd', '1 e. CC'), scc], 'addcld', '( 1 + S ) e. CC'), ucc], 'addcld', '%s e. CC' % Z_)
    ab = tk2([ck_['krp'], tk2([zcc], 'negcld', '-u %s e. CC' % Z_), w.inst('abscxp')], 'syl2anc', '( abs ` ( k ^c -u %s ) ) = ( k ^c ( Re ` -u %s ) )' % (Z_, Z_))
    rn = tk2([zcc], 'renegd', '( Re ` -u %s ) = -u ( Re ` %s )' % (Z_, Z_))
    r1 = tk2([tk2([tk2([], '1cnd', '1 e. CC'), scc], 'addcld', '( 1 + S ) e. CC'), ucc], 'readdd', '( Re ` %s ) = ( ( Re ` ( 1 + S ) ) + ( Re ` q ) )' % Z_)
    r2 = tk2([tk2([], '1cnd', '1 e. CC'), scc], 'readdd', '( Re ` ( 1 + S ) ) = ( ( Re ` 1 ) + ( Re ` S ) )')
    re1 = a1(w, ck, w.s([w.s([], '1re', '1 e. RR'), w.inst('rere')], 'ax-mp', '( Re ` 1 ) = 1'), '( Re ` 1 ) = 1')
    rsr = tk2([scc], 'recld', '( Re ` S ) e. RR'); rur = lift(w, urr, ck)
    rz = tk2([r1, tk2([tk2([r2, tk2([re1], 'oveq1d', '( ( Re ` 1 ) + ( Re ` S ) ) = ( 1 + ( Re ` S ) )')], 'eqtrd', '( Re ` ( 1 + S ) ) = ( 1 + ( Re ` S ) )')], 'oveq1d',
                      '( ( Re ` ( 1 + S ) ) + ( Re ` q ) ) = ( ( 1 + ( Re ` S ) ) + ( Re ` q ) )')], 'eqtrd', '( Re ` %s ) = ( ( 1 + ( Re ` S ) ) + ( Re ` q ) )' % Z_)
    rzr = tk2([zcc], 'recld', '( Re ` %s ) e. RR' % Z_)
    le32 = lin.linarith(w, ck, [rz, lift(w, ru, ck), fk['0 <_ ( Re ` S )']], '-u ( Re ` %s ) <_ -u ( 3 / 2 )' % Z_,
                        leaves={'( Re ` S )': rsr, '( Re ` q )': rur, '( Re ` %s )' % Z_: rzr})
    cxl = tk2([tk2([ck_['kr'], ck_['k1']], 'jca', '( k e. RR /\\ 1 <_ k )'), tk2([tk2([rzr], 'renegcld', '-u ( Re ` %s ) e. RR' % Z_), litr(w, ck, '-u ( 3 / 2 )')], 'jca',
                                                                                  '( -u ( Re ` %s ) e. RR /\\ -u ( 3 / 2 ) e. RR )' % Z_), le32, w.inst('cxplea')], 'syl3anc',
              '( k ^c -u ( Re ` %s ) ) <_ %s' % (Z_, N32('k')))
    kzb = tk2([tk2([ab, tk2([rn], 'oveq2d', '( k ^c ( Re ` -u %s ) ) = ( k ^c -u ( Re ` %s ) )' % (Z_, Z_))], 'eqtrd',
                   '( abs ` ( k ^c -u %s ) ) = ( k ^c -u ( Re ` %s ) )' % (Z_, Z_)), cxl], 'eqbrtrd', '( abs ` ( k ^c -u %s ) ) <_ %s' % (Z_, N32('k')))
    KCZ = '( k ^c -u %s )' % Z_
    kczc = tk2([ck_['kc'], tk2([zcc], 'negcld', '-u %s e. CC' % Z_)], 'cxpcld', '%s e. CC' % KCZ)
    rsp = w.s([w.s([w.s([], 'fveq2', '( j = k -> ( Q ` j ) = ( Q ` k ) )')], 'fveq2d', '( j = k -> ( abs ` ( Q ` j ) ) = ( abs ` ( Q ` k ) ) )')],
              'breq1d', '( j = k -> ( ( abs ` ( Q ` j ) ) <_ H <-> ( abs ` ( Q ` k ) ) <_ H ) )')
    qb = tk2([rsp, fk['A. j e. NN ( abs ` ( Q ` j ) ) <_ H'], kk], 'rspcdva', '( abs ` ( Q ` k ) ) <_ H')
    k32k = n32f(w, ck, kk, 'k')
    zb = tk2([tk2([ck_['qkc'], kczc], 'absmuld', '( abs ` %s ) = ( ( abs ` ( Q ` k ) ) x. ( abs ` %s ) )' % (ZS('k', 'q'), KCZ)),
              tk2([tk2([ck_['qkc']], 'abscld', '( abs ` ( Q ` k ) ) e. RR'), fk['H e. RR'], tk2([kczc], 'abscld', '( abs ` %s ) e. RR' % KCZ), tk2([k32k], 'rpred', '%s e. RR' % N32('k')),
                   tk2([ck_['qkc']], 'absge0d', '0 <_ ( abs ` ( Q ` k ) )'), tk2([kczc], 'absge0d', '0 <_ ( abs ` %s )' % KCZ), qb, kzb], 'lemul12ad',
                  '( ( abs ` ( Q ` k ) ) x. ( abs ` %s ) ) <_ ( H x. %s )' % (KCZ, N32('k')))], 'eqbrtrd', '( abs ` %s ) <_ ( H x. %s )' % (ZS('k', 'q'), N32('k')))
    ZSF = '( n e. NN |-> %s )' % ZS('n', 'q')
    zsv, _ = mpv(w, ck, 'n', 'NN', ZS('n', 'q'), 'k', kk)
    zfv, _ = mpv(w, ck, 'n', 'NN', N32('n'), 'k', kk)
    zsb = tk2([tk2([zsv], 'fveq2d', '( abs ` ( %s ` k ) ) = ( abs ` %s )' % (ZSF, ZS('k', 'q'))), tk2([zb, tk2([tk2([zfv], 'eqcomd', '%s = ( %s ` k )' % (N32('k'), ZF))], 'oveq2d',
                                                                                                  '( H x. %s ) = ( H x. ( %s ` k ) )' % (N32('k'), ZF))], 'breqtrd',
                                                                                          '( abs ` %s ) <_ ( H x. ( %s ` k ) )' % (ZS('k', 'q'), ZF))], 'eqbrtrd',
              '( abs ` ( %s ` k ) ) <_ ( H x. ( %s ` k ) )' % (ZSF, ZF))
    ck1 = '( %s /\\ k e. ( ZZ>= ` 1 ) )' % cu
    kn1c = w.s([w.s([], 'simpr', '( %s -> k e. ( ZZ>= ` 1 ) )' % ck1), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleq2i', '( k e. NN <-> k e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                      '( k e. ( ZZ>= ` 1 ) -> k e. NN )')], 'syl', '( %s -> k e. NN )' % ck1)
    zsb1 = w.s([w.s([w.s([zsb], 'ex', '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( H x. ( %s ` k ) ) ) )' % (cu, ZSF, ZF))], 'adantr',
                    '( %s -> ( k e. NN -> ( abs ` ( %s ` k ) ) <_ ( H x. ( %s ` k ) ) ) )' % (ck1, ZSF, ZF)), kn1c], 'mpd',
               '( %s -> ( abs ` ( %s ` k ) ) <_ ( H x. ( %s ` k ) ) )' % (ck1, ZSF, ZF))
    zkre_u = tk2([zfv, tk2([k32k], 'rpred', '%s e. RR' % N32('k'))], 'eqeltrd', '( %s ` k ) e. RR' % ZF)
    zsc = tk2([zsv, zkc], 'eqeltrd', '( %s ` k ) e. CC' % ZSF)
    zscv = tu([nnuz, a1(w, cu, w.s([], '1nn', '1 e. NN'), '1 e. NN'), zkre_u, zsc, lift(w, zc, cu), fu['H e. RR'], zsb1], 'cvgcmpce', 'seq 1 ( + , %s ) e. dom ~~>' % ZSF)
    im = w.s([nnuz, a1(w, cu, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ'), zsv, zkc, zscv, gkc], 'isummulc2',
             '( %s -> ( %s x. sum_ k e. NN %s ) = sum_ k e. NN ( %s x. %s ) )' % (cu, GK, ZS('k', 'q'), GK, ZS('k', 'q')))
    idk = w.s([], 'id', '( k = n -> k = n )')
    cst, _ = w.congr(ZS('k', 'q'), {'k': 'n'}, 'k = n', {'k': idk})
    cbs = a1(w, cu, w.s([cst], 'cbvsumv', 'sum_ k e. NN %s = sum_ n e. NN %s' % (ZS('k', 'q'), ZS('n', 'q'))), 'sum_ k e. NN %s = sum_ n e. NN %s' % (ZS('k', 'q'), ZS('n', 'q')))
    gav, _ = mpv(w, cu, 'w', DG, GAB('w'), 'q', udg)
    SU_ = 'sum_ k e. NN ( ( %s ` k ) ` q )' % FNS
    ch = tu([tu([s1, se], 'eqtrd', '( %s ` q ) = sum_ k e. NN ( %s x. %s )' % (SUMM, GK, ZS('k', 'q'))),
             tu([tu([im], 'eqcomd', 'sum_ k e. NN ( %s x. %s ) = ( %s x. sum_ k e. NN %s )' % (GK, ZS('k', 'q'), GK, ZS('k', 'q'))),
                 tu([cbs], 'oveq2d', '( %s x. sum_ k e. NN %s ) = %s' % (GK, ZS('k', 'q'), GAB('q')))], 'eqtrd',
                'sum_ k e. NN ( %s x. %s ) = %s' % (GK, ZS('k', 'q'), GAB('q')))], 'eqtrd', '( %s ` q ) = %s' % (SUMM, GAB('q')))
    pw = tu([ch, gav], 'eqtr4d', '( %s ` q ) = ( %s ` q )' % (SUMM, GA))
    r1_ = st([pw], 'ralrimiva', 'A. q e. %s ( %s ` q ) = ( %s ` q )' % (SEG, SUMM, GA))
    zs_ = w.s([w.s([], 'fveq2', '( q = z -> ( %s ` q ) = ( %s ` z ) )' % (SUMM, SUMM)), w.s([], 'fveq2', '( q = z -> ( %s ` q ) = ( %s ` z ) )' % (GA, GA))], 'eqeq12d',
              '( q = z -> ( ( %s ` q ) = ( %s ` q ) <-> ( %s ` z ) = ( %s ` z ) ) )' % (SUMM, GA, SUMM, GA))
    rz_ = st([r1_, w.s([zs_], 'cbvralvw', '( A. q e. %s ( %s ` q ) = ( %s ` q ) <-> A. z e. %s ( %s ` z ) = ( %s ` z ) )' % (SEG, SUMM, GA, SEG, SUMM, GA))], 'sylib',
             'A. z e. %s ( %s ` z ) = ( %s ` z )' % (SEG, SUMM, GA))
    sv = st([st([], 'ovexd', '%s e. _V' % SEG)], 'mptexd', '%s e. _V' % SUMM)
    gv = st([a1(w, a, w.s([w.s([], 'cnex', 'CC e. _V')], 'difexi', '%s e. _V' % DG), '%s e. _V' % DG)], 'mptexd', '%s e. _V' % GA)
    le = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([sv, gv], 'jca', '( %s e. _V /\\ %s e. _V )' % (SUMM, GA))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. _V /\\ %s e. _V ) )' % (SA, SB, SUMM, GA)), rz_, w.inst('linteq')], 'syl2anc',
            '( %s lint <. %s , %s >. ) = %s' % (SUMM, SA, SB, LIt(GA, '1', 'T')))
    fin = st([ls, le], 'breqtrd', split_imp(S_['gf2anl'])[1])
    w.qed([fin], 'idi', S_['gf2anl'])
    return w


from gf2_f import GKF as _GKF, YM as _YM, WMH as _WMH
GKFX = lambda X: tsub(_GKF, {'A': X})
E4T = '( 2 ^c -u ( T / 4 ) )'
K1 = '( ( ( ; ; ; 1 0 2 4 x. H ) x. ( 1 / ( log ` 2 ) ) ) x. ( %s + %s ) )' % (E3('( B + L )'), E3('( A + L )'))
LFK = '( ( %s ` K ) lint <. %s , %s >. )' % (FNS, SA, SB)
S_['gf2aerr'] = ('( ( %s /\\ ( ( T e. RR /\\ 1 <_ T ) /\\ K e. NN ) ) -> ( abs ` ( %s - ( %s x. %s ) ) ) <_ ( ( %s x. %s ) x. %s ) )'
                 % (AH, LFK, TPI, TN('K'), K1, N32('K'), E4T))


def gkfcn(w, a, f, krp, X):
    """GKFX ( X ) e. ( DG -cn-> CC ) (z6gyhol, gf1avgh)"""
    st = mkst(w, a)
    GYK = '( w e. %s |-> ( ( _G ` w ) x. ( K ^c -u w ) ) )' % DG
    gyh = st([krp, w.inst('z6gyhol')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (GYK, DG, DG, GYK))
    gyc = st([gyh], 'simpld', '%s e. ( %s -cn-> CC )' % (GYK, DG))
    xr = f['%s e. RR' % X]
    avh = st([st([st([xr, xr], 'jca', '( %s e. RR /\\ %s e. RR )' % (X, X)), f['L e. RR+']], 'jca', '( ( %s e. RR /\\ %s e. RR ) /\\ L e. RR+ )' % (X, X)), w.inst('gf1avgh')],
             'syl', tsub(split_imp(G1L.S['gf1avgh'])[1], {'B': X, 'A': X}))
    AVW = '( w e. CC |-> %s )' % G1L.AVG(X, 'L', 'w')
    avc = st([st([avh], 'simpld', G1L.HOL(AVW, 'CC'))], 'simpld', '%s e. ( CC -cn-> CC )' % AVW)
    dgcc = a1(w, a, w.s([], 'difss', '%s C_ CC' % DG), '%s C_ CC' % DG)
    av0 = st([avc, st([dgcc, w.inst('rescncf')], 'syl', '( %s e. ( CC -cn-> CC ) -> ( %s |` %s ) e. ( %s -cn-> CC ) )' % (AVW, AVW, DG, DG))], 'mpd',
             '( %s |` %s ) e. ( %s -cn-> CC )' % (AVW, DG, DG))
    AVD = '( w e. %s |-> %s )' % (DG, G1L.AVG(X, 'L', 'w'))
    avd = st([av0, st([st([dgcc, w.inst('resmpt')], 'syl', '( %s |` %s ) = %s' % (AVW, DG, AVD))], 'eleq1d',
                      '( ( %s |` %s ) e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (AVW, DG, DG, AVD, DG))], 'mpbid', '%s e. ( %s -cn-> CC )' % (AVD, DG))
    return st([gyc, avd], 'mulcncf', '%s e. ( %s -cn-> CC )' % (GKFX(X), DG))


def n32eq(w, a, c):
    """( K ^c -u ( 3 / 2 ) ) = ( ( 1 / K ) x. KH )"""
    st = mkst(w, a)
    knz = st([c['krp']], 'rpne0d', 'K =/= 0')
    e1 = st([c['kc'], knz, st([], '1cnd', '1 e. CC')], 'cxpnegd', '( K ^c -u 1 ) = ( 1 / ( K ^c 1 ) )')
    e2 = st([e1, st([st([c['kc']], 'cxp1d', '( K ^c 1 ) = K')], 'oveq2d', '( 1 / ( K ^c 1 ) ) = ( 1 / K )')], 'eqtrd', '( K ^c -u 1 ) = ( 1 / K )')
    nh = a1(w, a, w.s([w.s([], 'halfcn', '( 1 / 2 ) e. CC')], 'negcli', '-u ( 1 / 2 ) e. CC'), '-u ( 1 / 2 ) e. CC')
    n1 = a1(w, a, w.s([w.s([], 'ax-1cn', '1 e. CC')], 'negcli', '-u 1 e. CC'), '-u 1 e. CC')
    e3 = st([c['kc'], knz, n1, nh], 'cxpaddd', '( K ^c ( -u 1 + -u ( 1 / 2 ) ) ) = ( ( K ^c -u 1 ) x. %s )' % KH)
    n32 = ringeq(w, a, '( -u 1 + -u ( 1 / 2 ) )', '-u ( 3 / 2 )', Closure(w, a, {}))
    return st([st([st([n32], 'oveq2d', '( K ^c ( -u 1 + -u ( 1 / 2 ) ) ) = %s' % N32('K'))], 'eqcomd', '%s = ( K ^c ( -u 1 + -u ( 1 / 2 ) ) )' % N32('K')),
               st([e3, st([e2], 'oveq1d', '( ( K ^c -u 1 ) x. %s ) = ( ( 1 / K ) x. %s )' % (KH, KH))], 'eqtrd', '( K ^c ( -u 1 + -u ( 1 / 2 ) ) ) = ( ( 1 / K ) x. %s )' % KH)],
              'eqtrd', '%s = ( ( 1 / K ) x. %s )' % (N32('K'), KH))


def avtre(w, a, f, X, kr, k0, K='K'):
    """AVT ( X , K ) e. RR (z5wavg, xrrege0)"""
    st = mkst(w, a)
    AV = AVT(X, K)
    lb = '( exp ` ( -u %s / ( exp ` %s ) ) )' % (K, X)
    ub = '( exp ` ( -u %s / ( exp ` ( %s + L ) ) ) )' % (K, X)
    wv = st([st([f['%s e. RR' % X], f['L e. RR+']], 'jca', '( %s e. RR /\\ L e. RR+ )' % X), st([kr, k0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (K, K)), w.inst('z5wavg')], 'syl2anc',
            '( %s <_ %s /\\ %s <_ %s )' % (lb, AV, AV, ub))
    c1 = st([wv], 'simpld', '%s <_ %s' % (lb, AV)); c2 = st([wv], 'simprd', '%s <_ %s' % (AV, ub))
    br = w.s([w.s([], 'lerelxr', '<_ C_ ( RR* X. RR* )')], 'brel', '( %s <_ %s -> ( %s e. RR* /\\ %s e. RR* ) )' % (AV, ub, AV, ub))
    avx = st([st([c2, br], 'syl', '( %s e. RR* /\\ %s e. RR* )' % (AV, ub))], 'simpld', '%s e. RR*' % AV)
    xr = f['%s e. RR' % X]
    lbp = st([st([st([kr], 'renegcld', '-u %s e. RR' % K), st([xr], 'rpefcld', '( exp ` %s ) e. RR+' % X)], 'rerpdivcld', '( -u %s / ( exp ` %s ) ) e. RR' % (K, X))], 'rpefcld', '%s e. RR+' % lb)
    ubr = st([st([st([kr], 'renegcld', '-u %s e. RR' % K), st([st([xr, st([f['L e. RR+']], 'rpred', 'L e. RR')], 'readdcld', '( %s + L ) e. RR' % X)], 'rpefcld',
                                                                                    '( exp ` ( %s + L ) ) e. RR+' % X)], 'rerpdivcld', '( -u %s / ( exp ` ( %s + L ) ) ) e. RR' % (K, X))],
             'reefcld', '%s e. RR' % ub)
    z0 = st([st([], '0red', '0 e. RR')], 'rexrd', '0 e. RR*')
    av0 = st([z0, st([st([lbp], 'rpred', '%s e. RR' % lb)], 'rexrd', '%s e. RR*' % lb), avx, st([lbp], 'rpge0d', '0 <_ %s' % lb), c1], 'xrletrd', '0 <_ %s' % AV)
    return st([st([avx, ubr], 'jca', '( %s e. RR* /\\ %s e. RR )' % (AV, ub)), st([av0, c2], 'jca', '( 0 <_ %s /\\ %s <_ %s )' % (AV, AV, ub)), w.inst('xrrege0')], 'syl2anc',
              '%s e. RR' % AV)


def gf2aerr():
    w = W('gf2aerr', 'Each Mellin term along ` 1 - i T -- 1 + i T ` minus ` 2 pi i ` times the anchor summand ` c_K W ( K ) ` is '
          '` O ( K ^ -u ( 3 / 2 ) 2 ^ ( - T / 4 ) ) ` for ` T >_ 1 ` : the two windows by ~ gf2wm , the constants by ~ gf2ypow '
          '(Lean ` bMaj_term_eq_integral ` , quantitative; ~ ef6ldf , ~ lintmulc2 , ~ linteq ).')
    a = split_imp(S_['gf2aerr'])[0]; st = mkst(w, a); f = ahf(w, a, None)
    tr = proj(w, a, 'T e. RR'); t1 = proj(w, a, '1 <_ T'); kn = proj(w, a, 'K e. NN')
    sf = segf(w, a, tr)
    aq = '( %s /\\ q e. %s )' % (a, SEG)
    rq, qc, qdg, qrr = ptf(w, aq, liftd(w, sf, aq), w.s([], 'simpr', '( %s -> q e. %s )' % (aq, SEG)), 'q')
    sdg = st([w.s([qdg], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (a, SEG, DG))], 'ssrdv', '%s C_ %s' % (SEG, DG))
    c = cnb(w, a, f, kn, 'K')
    lr = st([f['L e. RR+']], 'rpred', 'L e. RR')
    # the two windows
    E4 = E4T
    l2 = a1(w, a, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'),
                       w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('loggt0b')], 'ax-mp', '( 0 < ( log ` 2 ) <-> 1 < 2 )')], 'mpbir', '0 < ( log ` 2 )')],
                      'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    e4p = st([a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([st([tr, a1(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, a, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                    'redivcld', '( T / 4 ) e. RR')], 'renegcld', '-u ( T / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E4)
    c8 = a1(w, a, num.re_nat(w, 8), '8 e. RR'); c80 = a1(w, a, num.ge0_nat(w, 8), '0 <_ 8')
    W_ = {}
    for X in ('B', 'A'):
        XL = '( %s + L )' % X
        xlr = st([f['%s e. RR' % X], lr], 'readdcld', '%s e. RR' % XL)
        xl0 = st([f['%s e. RR' % X], lr, f['0 <_ %s' % X], st([f['L e. RR+']], 'rpge0d', '0 <_ L')], 'addge0d', '0 <_ %s' % XL)
        YMX = tsub(_YM, {'A': X})
        wm = st([st([st([kn, st([f['%s e. RR' % X], f['L e. RR+']], 'jca', '( %s e. RR /\\ L e. RR+ )' % X)], 'jca', '( K e. NN /\\ ( %s e. RR /\\ L e. RR+ ) )' % X),
                     st([tr, t1], 'jca', '( T e. RR /\\ 1 <_ T )')], 'jca', tsub(_WMH, {'A': X})), w.inst('gf2wm')], 'syl',
                tsub(split_imp(_SF['gf2wm'])[1], {'A': X}))
        yp = st([st([st([c['kr'], c['k1']], 'jca', '( K e. RR /\\ 1 <_ K )'), st([xlr, xl0], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (XL, XL))], 'jca',
                    '( ( K e. RR /\\ 1 <_ K ) /\\ ( %s e. RR /\\ 0 <_ %s ) )' % (XL, XL)), w.inst('gf2ypow')], 'syl',
                tsub(split_imp(S_['gf2ypow'])[1], {'X': XL}))
        M1 = MYF(YMX); M2 = '( ( ; ; 1 2 8 x. %s ) x. %s )' % (E3(XL), KH)
        ymp = st([c['krp'], st([st([xlr], 'renegcld', '-u %s e. RR' % XL)], 'rpefcld', '( exp ` -u %s ) e. RR+' % XL)], 'rpmulcld', '%s e. RR+' % YMX)
        m1r = st([a1(w, a, num.re_nat(w, 64), '; 6 4 e. RR'), st([st([st([ymp, litr(w, a, '-u ( 1 / 2 )')], 'rpcxpcld', '( %s ^c -u ( 1 / 2 ) ) e. RR+' % YMX),
                                                                   st([ymp, litr(w, a, '-u 3')], 'rpcxpcld', '( %s ^c -u 3 ) e. RR+' % YMX)], 'rpaddcld',
                                                                  '( ( %s ^c -u ( 1 / 2 ) ) + ( %s ^c -u 3 ) ) e. RR+' % (YMX, YMX))], 'rpred',
                                                              '( ( %s ^c -u ( 1 / 2 ) ) + ( %s ^c -u 3 ) ) e. RR' % (YMX, YMX))], 'remulcld', '%s e. RR' % M1)
        e3r = st([st([st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), xlr], 'remulcld', '( 3 x. %s ) e. RR' % XL)], 'rpefcld', '%s e. RR+' % E3(XL))], 'rpred', '%s e. RR' % E3(XL))
        khr = st([st([c['krp'], litr(w, a, '-u ( 1 / 2 )')], 'rpcxpcld', '%s e. RR+' % KH)], 'rpred', '%s e. RR' % KH)
        m2r = st([st([a1(w, a, num.re_nat(w, 128), '; ; 1 2 8 e. RR'), e3r], 'remulcld', '( ; ; 1 2 8 x. %s ) e. RR' % E3(XL)), khr], 'remulcld', '%s e. RR' % M2)
        s8 = st([m1r, m2r, c8, c80, yp], 'lemul2ad', '( 8 x. %s ) <_ ( 8 x. %s )' % (M1, M2))
        r81 = st([c8, m1r], 'remulcld', '( 8 x. %s ) e. RR' % M1); r82 = st([c8, m2r], 'remulcld', '( 8 x. %s ) e. RR' % M2)
        dv = st([s8, st([r81, r82, l2], 'lediv1d', '( ( 8 x. %s ) <_ ( 8 x. %s ) <-> ( ( 8 x. %s ) / ( log ` 2 ) ) <_ ( ( 8 x. %s ) / ( log ` 2 ) ) )' % (M1, M2, M1, M2))],
                'mpbid', '( ( 8 x. %s ) / ( log ` 2 ) ) <_ ( ( 8 x. %s ) / ( log ` 2 ) )' % (M1, M2))
        bb = st([st([r81, l2], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % M1), st([r82, l2], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % M2),
                 st([e4p], 'rpred', '%s e. RR' % E4), st([e4p], 'rpge0d', '0 <_ %s' % E4), dv], 'lemul1ad', '%s <_ %s' % (BND(M1, 'T'), BND(M2, 'T')))
        IX = LIt(GKFX(X), '1', 'T'); DX = '( %s - ( %s x. %s ) )' % (IX, TPI, AVT(X, 'K'))
        dxr = st([st([wm, w.inst('z6absle')], 'syl', '%s e. CC' % DX)], 'abscld', '( abs ` %s ) e. RR' % DX)
        b1r = st([st([st([r81, l2], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % M1), st([e4p], 'rpred', '%s e. RR' % E4)], 'remulcld', '%s e. RR' % BND(M1, 'T'))], 'idi',
                 '%s e. RR' % BND(M1, 'T'))
        b2r = st([st([r82, l2], 'rerpdivcld', '( ( 8 x. %s ) / ( log ` 2 ) ) e. RR' % M2), st([e4p], 'rpred', '%s e. RR' % E4)], 'remulcld', '%s e. RR' % BND(M2, 'T'))
        dxb = st([dxr, b1r, b2r, wm, bb], 'letrd', '( abs ` %s ) <_ %s' % (DX, BND(M2, 'T')))
        dr = st([st([c8, m2r], 'remulcld', '( 8 x. %s ) e. RR' % M2)], 'recnd', '( 8 x. %s ) e. CC' % M2)
        dre = st([dr, st([l2], 'rpcnd', '( log ` 2 ) e. CC'), st([l2], 'rpne0d', '( log ` 2 ) =/= 0')], 'divrecd',
                 '( ( 8 x. %s ) / ( log ` 2 ) ) = ( ( 8 x. %s ) x. ( 1 / ( log ` 2 ) ) )' % (M2, M2))
        BX = '( ( ( 8 x. %s ) x. ( 1 / ( log ` 2 ) ) ) x. %s )' % (M2, E4)
        dxb2 = st([dxb, st([dre], 'oveq1d', '%s = %s' % (BND(M2, 'T'), BX))], 'breqtrd', '( abs ` %s ) <_ %s' % (DX, BX))
        W_[X] = dict(IX=IX, DX=DX, dxb=dxb2, BX=BX, dxc=st([wm, w.inst('z6absle')], 'syl', '%s e. CC' % DX), e3r=e3r, khr=khr, m2r=m2r)
    # the lint identity: LFK = CN ( K ) ( I_B - I_A )
    trp = st([tr, lin.linarith(w, a, [t1], '0 < T', leaves={'T': tr})], 'elrpd', 'T e. RR+')
    DD = '( %s i^i %s )' % (DG, DG)
    dgcc = a1(w, a, w.s([], 'difss', '%s C_ CC' % DG), '%s C_ CC' % DG)
    ddcc = st([a1(w, a, w.s([], 'inss1', '%s C_ %s' % (DD, DG)), '%s C_ %s' % (DD, DG)), dgcc], 'sstrd', '%s C_ CC' % DD)
    sdd = st([sdg, sdg], 'ssind', '%s C_ %s' % (SEG, DD))
    gB = gkfcn(w, a, f, c['krp'], 'B'); gA = gkfcn(w, a, f, c['krp'], 'A')
    IB, IA = W_['B']['IX'], W_['A']['IX']
    DFn = '( b e. %s |-> ( ( %s ` b ) - ( %s ` b ) ) )' % (DD, GKFX('B'), GKFX('A'))
    ef = st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([gB, gA], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s e. ( %s -cn-> CC ) )' % (GKFX('B'), DG, GKFX('A'), DG)),
             sdd, w.inst('ef6ldf')], 'syl3anc',
            '( %s e. ( %s -cn-> CC ) /\\ ( %s lint <. %s , %s >. ) = ( %s - %s ) )' % (DFn, DD, DFn, SA, SB, IB, IA))
    dfc = st([ef], 'simpld', '%s e. ( %s -cn-> CC )' % (DFn, DD))
    dfl = st([ef], 'simprd', '( %s lint <. %s , %s >. ) = ( %s - %s )' % (DFn, SA, SB, IB, IA))
    CNK = CN('K')
    HK = '( b e. %s |-> ( %s x. ( ( %s ` b ) - ( %s ` b ) ) ) )' % (DD, CNK, GKFX('B'), GKFX('A'))
    ccss = a1(w, a, w.s([], 'ssid', 'CC C_ CC'), 'CC C_ CC')
    cm = st([c['cnc'], ddcc, ccss, w.inst('cncfmptc')], 'syl3anc', '( b e. %s |-> %s ) e. ( %s -cn-> CC )' % (DD, CNK, DD))
    hkc = st([cm, dfc], 'mulcncf', '%s e. ( %s -cn-> CC )' % (HK, DD))
    qdd = w.s([lift(w, sdd, aq), w.s([], 'simpr', '( %s -> q e. %s )' % (aq, SEG))], 'sseldd', '( %s -> q e. %s )' % (aq, DD))
    sq = mkst(w, aq)
    BODYH = '( %s x. ( ( %s ` b ) - ( %s ` b ) ) )' % (CNK, GKFX('B'), GKFX('A'))
    hv, _ = mpv(w, aq, 'b', DD, BODYH, 'q', qdd)
    dv, _ = mpv(w, aq, 'b', DD, '( ( %s ` b ) - ( %s ` b ) )' % (GKFX('B'), GKFX('A')), 'q', qdd)
    DQ = '( ( %s ` q ) - ( %s ` q ) )' % (GKFX('B'), GKFX('A'))
    pz = sq([hv, sq([dv], 'oveq2d', '( %s x. ( %s ` q ) ) = ( %s x. %s )' % (CNK, DFn, CNK, DQ))], 'eqtr4d', '( %s ` q ) = ( %s x. ( %s ` q ) )' % (HK, CNK, DFn))
    def ralz(stp, P):
        r1 = st([stp], 'ralrimiva', 'A. q e. %s %s' % (SEG, P('q')))
        idq = w.s([], 'id', '( q = z -> q = z )')
        sb, _ = w.wcongr(P('q'), {'q': 'z'}, 'q = z', {'q': idq})
        return st([r1, w.s([sb], 'cbvralvw', '( A. q e. %s %s <-> A. z e. %s %s )' % (SEG, P('q'), SEG, P('z')))], 'sylib', 'A. z e. %s %s' % (SEG, P('z')))
    rz = ralz(pz, lambda v: '( %s ` %s ) = ( %s x. ( %s ` %s ) )' % (HK, v, CNK, DFn, v))
    lk2 = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([hkc, sdd], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (HK, DD, SEG, DD))], 'jca',
                 '( ( %s e. CC /\\ %s e. CC ) /\\ ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (SA, SB, HK, DD, SEG, DD)),
              st([dfc, c['cnc']], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s e. CC )' % (DFn, DD, CNK)), rz, w.inst('lintmulc2')], 'syl3anc',
             '( %s lint <. %s , %s >. ) = ( %s x. ( %s lint <. %s , %s >. ) )' % (HK, SA, SB, CNK, DFn, SA, SB))
    # FNS ` K = HK on the segment
    qm = w.s([], 'simpr', '( %s -> q e. %s )' % (aq, SEG))
    pk = sq([sq([lift(w, proj(w, a, AH), aq), sq([lift(w, trp, aq), sq([lift(w, kn, aq), qm], 'jca', '( K e. NN /\\ q e. %s )' % SEG)], 'jca',
                                                  '( T e. RR+ /\\ ( K e. NN /\\ q e. %s ) )' % SEG)], 'jca', tsub(split_imp(S_['gf2anp'])[0], {'V': 'q'})),
             w.inst('gf2anp')], 'syl', tsub(split_imp(S_['gf2anp'])[1], {'V': 'q'}))
    pvq = sq([pk], 'simprld', '( ( %s ` K ) ` q ) = %s' % (FNS, FB('K', 'q')))
    gbv, _ = mpv(w, aq, 'w', DG, '( ( ( _G ` w ) x. ( K ^c -u w ) ) x. %s )' % G1L.AVG('B', 'L', 'w'), 'q', qdg)
    gav, _ = mpv(w, aq, 'w', DG, '( ( ( _G ` w ) x. ( K ^c -u w ) ) x. %s )' % G1L.AVG('A', 'L', 'w'), 'q', qdg)
    GQ = '( ( _G ` q ) x. ( K ^c -u q ) )'
    e_ = sq([sq([gbv, gav], 'oveq12d', '%s = ( ( %s x. %s ) - ( %s x. %s ) )' % (DQ, GQ, G1L.AVG('B', 'L', 'q'), GQ, G1L.AVG('A', 'L', 'q')))], 'oveq2d',
            '( %s x. %s ) = ( %s x. ( ( %s x. %s ) - ( %s x. %s ) ) )' % (CNK, DQ, CNK, GQ, G1L.AVG('B', 'L', 'q'), GQ, G1L.AVG('A', 'L', 'q')))
    fq = liftd(w, f, aq)
    gqc = sq([qdg, w.inst('gamcl')], 'syl', '( _G ` q ) e. CC')
    kqc = sq([lift(w, c['kc'], aq), sq([qc], 'negcld', '-u q e. CC')], 'cxpcld', '( K ^c -u q ) e. CC')
    lc = sq([fq['L e. RR+']], 'rpcnd', 'L e. CC'); lnz = sq([fq['L e. RR+']], 'rpne0d', 'L =/= 0')
    phc = sq([sq([lc, qc, w.inst('gf1phv')], 'syl2anc', tsub(split_imp(G1L.S['gf1phv'])[1], {'C': 'L', 'W': 'q'}))], 'simp1d', '%s e. CC' % G1L.PH('L', 'q'))
    avcs = {}
    for X in ('B', 'A'):
        avcs[X] = sq([sq([sq([sq([fq['%s e. RR' % X]], 'recnd', '%s e. CC' % X), qc], 'mulcld', '( %s x. q ) e. CC' % X)], 'efcld', '( exp ` ( %s x. q ) ) e. CC' % X),
                      sq([phc, lc, lnz], 'divcld', '( %s / L ) e. CC' % G1L.PH('L', 'q'))], 'mulcld', '%s e. CC' % G1L.AVG(X, 'L', 'q'))
    cl = Closure(w, aq, {CNK: lift(w, c['cnc'], aq), '( _G ` q )': gqc, '( K ^c -u q )': kqc, G1L.AVG('B', 'L', 'q'): avcs['B'], G1L.AVG('A', 'L', 'q'): avcs['A']})
    rq_ = ringeq(w, aq, '( %s x. ( ( %s x. %s ) - ( %s x. %s ) ) )' % (CNK, GQ, G1L.AVG('B', 'L', 'q'), GQ, G1L.AVG('A', 'L', 'q')), FB('K', 'q'), cl)
    hq = sq([hv, sq([e_, rq_], 'eqtrd', '( %s x. %s ) = %s' % (CNK, DQ, FB('K', 'q')))], 'eqtrd', '( %s ` q ) = %s' % (HK, FB('K', 'q')))
    fh = sq([pvq, hq], 'eqtr4d', '( ( %s ` K ) ` q ) = ( %s ` q )' % (FNS, HK))
    rz1 = ralz(fh, lambda v: '( ( %s ` K ) ` %s ) = ( %s ` %s )' % (FNS, v, HK, v))
    ddv = a1(w, a, w.s([w.s([w.s([], 'cnex', 'CC e. _V')], 'difexi', '%s e. _V' % DG)], 'inex1', '%s e. _V' % DD), '%s e. _V' % DD)
    lk1 = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([st([], 'fvexd', '( %s ` K ) e. _V' % FNS), st([ddv], 'mptexd', '%s e. _V' % HK)], 'jca',
                                                                                              '( ( %s ` K ) e. _V /\\ %s e. _V )' % (FNS, HK))], 'jca',
                 '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( %s ` K ) e. _V /\\ %s e. _V ) )' % (SA, SB, FNS, HK)), rz1, w.inst('linteq')], 'syl2anc',
             '%s = ( %s lint <. %s , %s >. )' % (LFK, HK, SA, SB))
    LFV = '( %s x. ( %s - %s ) )' % (CNK, IB, IA)
    lfe = st([st([lk1, lk2], 'eqtrd', '%s = ( %s x. ( %s lint <. %s , %s >. ) )' % (LFK, CNK, DFn, SA, SB)), st([dfl], 'oveq2d', '( %s x. ( %s lint <. %s , %s >. ) ) = %s' % (CNK, DFn, SA, SB, LFV))],
             'eqtrd', '%s = %s' % (LFK, LFV))
    # the algebra
    k0 = st([c['krp']], 'rpge0d', '0 <_ K')
    avr = {X: avtre(w, a, f, X, c['kr'], k0) for X in ('B', 'A')}
    tpic = st([st([], '2cnd', '2 e. CC'), st([sf['ic'], a1(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    ixc = {}
    for X, g in (('B', gB), ('A', gA)):
        ixc[X] = st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([g, sdg], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (GKFX(X), DG, SEG, DG)),
                     w.inst('lintcl')], 'syl2anc', '%s e. CC' % W_[X]['IX'])
    DB_, DA_ = W_['B']['DX'], W_['A']['DX']
    cl = Closure(w, a, {CNK: c['cnc'], IB: ixc['B'], IA: ixc['A'], TPI: tpic, AVT('B', 'K'): avr['B'], AVT('A', 'K'): avr['A']})
    D0 = '( %s - ( %s x. %s ) )' % (LFK, TPI, TN('K'))
    de = st([st([lfe], 'oveq1d', '%s = ( %s - ( %s x. %s ) )' % (D0, LFV, TPI, TN('K'))),
             ringeq(w, a, '( %s - ( %s x. %s ) )' % (LFV, TPI, TN('K')), '( %s x. ( %s - %s ) )' % (CNK, DB_, DA_), cl)], 'eqtrd',
            '%s = ( %s x. ( %s - %s ) )' % (D0, CNK, DB_, DA_))
    dbc = st([ixc['B'], st([tpic, st([avr['B']], 'recnd', '%s e. CC' % AVT('B', 'K'))], 'mulcld', '( %s x. %s ) e. CC' % (TPI, AVT('B', 'K')))], 'subcld', '%s e. CC' % DB_)
    dac = st([ixc['A'], st([tpic, st([avr['A']], 'recnd', '%s e. CC' % AVT('A', 'K'))], 'mulcld', '( %s x. %s ) e. CC' % (TPI, AVT('A', 'K')))], 'subcld', '%s e. CC' % DA_)
    ddc = st([dbc, dac], 'subcld', '( %s - %s ) e. CC' % (DB_, DA_))
    BB, BA = W_['B']['BX'], W_['A']['BX']
    ilr = st([st([l2], 'rpreccld', '( 1 / ( log ` 2 ) ) e. RR+')], 'rpred', '( 1 / ( log ` 2 ) ) e. RR')
    e4r = st([e4p], 'rpred', '%s e. RR' % E4)
    bxr = {X: st([st([st([c8, W_[X]['m2r']], 'remulcld', '( 8 x. %s ) e. RR' % ('( ( ; ; 1 2 8 x. %s ) x. %s )' % (E3('( %s + L )' % X), KH))), ilr], 'remulcld',
                     '( ( 8 x. %s ) x. ( 1 / ( log ` 2 ) ) ) e. RR' % ('( ( ; ; 1 2 8 x. %s ) x. %s )' % (E3('( %s + L )' % X), KH))), e4r], 'remulcld', '%s e. RR' % W_[X]['BX'])
           for X in ('B', 'A')}
    t2 = st([dbc, dac], 'abs2dif2d', '( abs ` ( %s - %s ) ) <_ ( ( abs ` %s ) + ( abs ` %s ) )' % (DB_, DA_, DB_, DA_))
    t3 = st([st([dbc], 'abscld', '( abs ` %s ) e. RR' % DB_), st([dac], 'abscld', '( abs ` %s ) e. RR' % DA_), bxr['B'], bxr['A'], W_['B']['dxb'], W_['A']['dxb']], 'le2addd',
            '( ( abs ` %s ) + ( abs ` %s ) ) <_ ( %s + %s )' % (DB_, DA_, BB, BA))
    sbr = st([bxr['B'], bxr['A']], 'readdcld', '( %s + %s ) e. RR' % (BB, BA))
    t4 = st([st([ddc], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (DB_, DA_)), st([st([dbc], 'abscld', '( abs ` %s ) e. RR' % DB_), st([dac], 'abscld', '( abs ` %s ) e. RR' % DA_)],
                                                                                   'readdcld', '( ( abs ` %s ) + ( abs ` %s ) ) e. RR' % (DB_, DA_)), sbr, t2, t3], 'letrd',
            '( abs ` ( %s - %s ) ) <_ ( %s + %s )' % (DB_, DA_, BB, BA))
    IH = '( ( 1 / K ) x. H )'
    t5 = st([st([c['cnc'], ddc], 'absmuld', '( abs ` ( %s x. ( %s - %s ) ) ) = ( ( abs ` %s ) x. ( abs ` ( %s - %s ) ) )' % (CNK, DB_, DA_, CNK, DB_, DA_)),
             st([st([c['cnc']], 'abscld', '( abs ` %s ) e. RR' % CNK), c['ihr'], st([ddc], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (DB_, DA_)), sbr,
                 st([c['cnc']], 'absge0d', '0 <_ ( abs ` %s )' % CNK), st([ddc], 'absge0d', '0 <_ ( abs ` ( %s - %s ) )' % (DB_, DA_)), c['cnb'], t4], 'lemul12ad',
                '( ( abs ` %s ) x. ( abs ` ( %s - %s ) ) ) <_ ( %s x. ( %s + %s ) )' % (CNK, DB_, DA_, IH, BB, BA))], 'eqbrtrd',
            '( abs ` ( %s x. ( %s - %s ) ) ) <_ ( %s x. ( %s + %s ) )' % (CNK, DB_, DA_, IH, BB, BA))
    t6 = st([st([de], 'fveq2d', '( abs ` %s ) = ( abs ` ( %s x. ( %s - %s ) ) )' % (D0, CNK, DB_, DA_)), t5], 'eqbrtrd', '( abs ` %s ) <_ ( %s x. ( %s + %s ) )' % (D0, IH, BB, BA))
    cl2 = Closure(w, a, {'( 1 / K )': c['ik'], 'H': f['H e. RR'], E3('( B + L )'): W_['B']['e3r'], E3('( A + L )'): W_['A']['e3r'], KH: W_['B']['khr'], '( 1 / ( log ` 2 ) )': ilr,
                         E4: e4r})
    rq2 = ringeq(w, a, '( %s x. ( %s + %s ) )' % (IH, BB, BA), '( ( %s x. ( ( 1 / K ) x. %s ) ) x. %s )' % (K1, KH, E4), cl2)
    ne = n32eq(w, a, c)
    fe = st([rq2, st([st([st([ne], 'eqcomd', '( ( 1 / K ) x. %s ) = %s' % (KH, N32('K')))], 'oveq2d', '( %s x. ( ( 1 / K ) x. %s ) ) = ( %s x. %s )' % (K1, KH, K1, N32('K')))],
                     'oveq1d', '( ( %s x. ( ( 1 / K ) x. %s ) ) x. %s ) = ( ( %s x. %s ) x. %s )' % (K1, KH, E4, K1, N32('K'), E4))], 'eqtrd',
            '( %s x. ( %s + %s ) ) = ( ( %s x. %s ) x. %s )' % (IH, BB, BA, K1, N32('K'), E4))
    fin = st([t6, fe], 'breqtrd', split_imp(S_['gf2aerr'])[1])
    w.qed([fin], 'idi', S_['gf2aerr'])
    return w


S_['gf2anb'] = '( ( %s /\\ ( T e. RR+ /\\ K e. NN ) ) -> ( abs ` %s ) <_ ( ( %s x. %s ) x. ( 2 x. T ) ) )' % (AH, LFK, K0, N32('K'))


def seglen(w, a, trp, sf):
    """( abs ` ( SB - SA ) ) = ( 2 x. T )"""
    st = mkst(w, a)
    tr = st([trp], 'rpred', 'T e. RR'); tc = st([tr], 'recnd', 'T e. CC')
    cl = Closure(w, a, {'_i': sf['ic'], 'T': tc})
    d = ringeq(w, a, '( %s - %s )' % (SB, SA), '( 2 x. ( _i x. T ) )', cl)
    itc = st([sf['ic'], tc], 'mulcld', '( _i x. T ) e. CC')
    a1_ = st([st([], '2cnd', '2 e. CC'), itc], 'absmuld', '( abs ` ( 2 x. ( _i x. T ) ) ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. T ) ) )')
    a2 = st([sf['ic'], tc], 'absmuld', '( abs ` ( _i x. T ) ) = ( ( abs ` _i ) x. ( abs ` T ) )')
    ai = a1(w, a, w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1')
    at = st([tr, st([trp], 'rpge0d', '0 <_ T')], 'absidd', '( abs ` T ) = T')
    a2v = st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), a1(w, a, w.s([], '0le2', '0 <_ 2'), '0 <_ 2')], 'absidd', '( abs ` 2 ) = 2')
    it = st([a2, st([ai, at], 'oveq12d', '( ( abs ` _i ) x. ( abs ` T ) ) = ( 1 x. T )')], 'eqtrd', '( abs ` ( _i x. T ) ) = ( 1 x. T )')
    it2 = st([it, st([tc], 'mullidd', '( 1 x. T ) = T')], 'eqtrd', '( abs ` ( _i x. T ) ) = T')
    tot = st([a1_, st([a2v, it2], 'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. T ) ) ) = ( 2 x. T )')], 'eqtrd', '( abs ` ( 2 x. ( _i x. T ) ) ) = ( 2 x. T )')
    return st([st([d], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( 2 x. ( _i x. T ) ) )' % (SB, SA)), tot], 'eqtrd', '( abs ` ( %s - %s ) ) = ( 2 x. T )' % (SB, SA))


def gf2anb():
    w = W('gf2anb', 'The ML bound of one Mellin term along ` 1 - i T -- 1 + i T ` (~ lintabs with ~ gf2anp ; the segment has length ` 2 T ` ).')
    a = split_imp(S_['gf2anb'])[0]; st = mkst(w, a); f = ahf(w, a, None)
    trp = proj(w, a, 'T e. RR+'); tr = st([trp], 'rpred', 'T e. RR'); kn = proj(w, a, 'K e. NN')
    sf = segf(w, a, tr)
    aq = '( %s /\\ q e. %s )' % (a, SEG)
    rq, qc, qdg, qrr = ptf(w, aq, liftd(w, sf, aq), w.s([], 'simpr', '( %s -> q e. %s )' % (aq, SEG)), 'q')
    sdg = st([w.s([qdg], 'ex', '( %s -> ( q e. %s -> q e. %s ) )' % (a, SEG, DG))], 'ssrdv', '%s C_ %s' % (SEG, DG))
    c = cnb(w, a, f, kn, 'K')
    fcn = fnscn(w, a, f, c, sf, sdg, 'K')
    FK = '( v e. %s |-> %s )' % (SEG, FB('K', 'v'))
    segv = st([], 'ovexd', '%s e. _V' % SEG)
    v1, _ = mpv(w, a, 'n', 'NN', '( v e. %s |-> %s )' % (SEG, FB('n', 'v')), 'K', kn, exs=st([segv], 'mptexd', '%s e. _V' % FK))
    fkc = st([fcn, st([v1], 'eleq1d', '( ( %s ` K ) e. ( %s -cn-> CC ) <-> %s e. ( %s -cn-> CC ) )' % (FNS, SEG, FK, SEG))], 'mpbird', '( %s ` K ) e. ( %s -cn-> CC )' % (FNS, SEG))
    sq = mkst(w, aq)
    qm = w.s([], 'simpr', '( %s -> q e. %s )' % (aq, SEG))
    pk = sq([sq([lift(w, proj(w, a, AH), aq), sq([lift(w, trp, aq), sq([lift(w, kn, aq), qm], 'jca', '( K e. NN /\\ q e. %s )' % SEG)], 'jca',
                                                     '( T e. RR+ /\\ ( K e. NN /\\ q e. %s ) )' % SEG)], 'jca', tsub(split_imp(S_['gf2anp'])[0], {'V': 'q'})),
             w.inst('gf2anp')], 'syl', tsub(split_imp(S_['gf2anp'])[1], {'V': 'q'}))
    pvq = sq([pk], 'simprld', '( ( %s ` K ) ` q ) = %s' % (FNS, FB('K', 'q')))
    pbq = sq([pk], 'simprrd', '( abs ` %s ) <_ ( %s x. %s )' % (FB('K', 'q'), K0, N32('K')))
    bq = sq([sq([pvq], 'fveq2d', '( abs ` ( ( %s ` K ) ` q ) ) = ( abs ` %s )' % (FNS, FB('K', 'q'))), pbq], 'eqbrtrd',
            '( abs ` ( ( %s ` K ) ` q ) ) <_ ( %s x. %s )' % (FNS, K0, N32('K')))
    M = '( %s x. %s )' % (K0, N32('K'))
    r1 = st([bq], 'ralrimiva', 'A. q e. %s ( abs ` ( ( %s ` K ) ` q ) ) <_ %s' % (SEG, FNS, M))
    idq = w.s([], 'id', '( q = z -> q = z )')
    sb, _ = w.wcongr('( abs ` ( ( %s ` K ) ` q ) ) <_ %s' % (FNS, M), {'q': 'z'}, 'q = z', {'q': idq})
    rz = st([r1, w.s([sb], 'cbvralvw', '( A. q e. %s ( abs ` ( ( %s ` K ) ` q ) ) <_ %s <-> A. z e. %s ( abs ` ( ( %s ` K ) ` z ) ) <_ %s )' % (SEG, FNS, M, SEG, FNS, M))],
            'sylib', 'A. z e. %s ( abs ` ( ( %s ` K ) ` z ) ) <_ %s' % (SEG, FNS, M))
    k0r, eer = k0real(w, a, f)
    mr = st([k0r, st([n32f(w, a, kn, 'K')], 'rpred', '%s e. RR' % N32('K'))], 'remulcld', '%s e. RR' % M)
    la = st([st([st([sf['sac'], sf['sbc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (SA, SB)), st([fkc, st([], 'ssidd', '%s C_ %s' % (SEG, SEG))], 'jca',
                                                                                          '( ( %s ` K ) e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (FNS, SEG, SEG, SEG))], 'jca',
                '( ( %s e. CC /\\ %s e. CC ) /\\ ( ( %s ` K ) e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (SA, SB, FNS, SEG, SEG, SEG)), mr, rz, w.inst('lintabs')], 'syl3anc',
            '( abs ` %s ) <_ ( %s x. ( abs ` ( %s - %s ) ) )' % (LFK, M, SB, SA))
    fin = st([la, st([seglen(w, a, trp, sf)], 'oveq2d', '( %s x. ( abs ` ( %s - %s ) ) ) = ( %s x. ( 2 x. T ) )' % (M, SB, SA, M))], 'breqtrd', split_imp(S_['gf2anb'])[1])
    w.qed([fin], 'idi', S_['gf2anb'])
    return w


ZF32 = '( n e. NN |-> %s )' % N32('n')


def cvg32(w, a, G, body, C, cr):
    """( a -> seq 1 ( + , G ) e. dom ~~> ) by cvgcmpce against C m ^ -3/2 ; body(am, mn) -> (eq, vc, vb, V) with
    eq: ( G ` m ) = V, vc: V e. CC, vb: ( abs ` V ) <_ ( C x. N32(m) )"""
    st = mkst(w, a)
    am = '( %s /\\ m e. NN )' % a; t = mkst(w, am)
    mn = t([], 'simpr', 'm e. NN')
    eq, vc, vb, V = body(am, mn)
    zv, _ = mpv(w, am, 'n', 'NN', N32('n'), 'm', mn)
    ZFm = '( %s ` m )' % ZF32
    gc = t([eq, vc], 'eqeltrd', '( %s ` m ) e. CC' % G)
    zre = t([zv, t([n32f(w, am, mn, 'm')], 'rpred', '%s e. RR' % N32('m'))], 'eqeltrd', '%s e. RR' % ZFm)
    b1 = t([t([t([eq], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` %s )' % (G, V)), vb], 'eqbrtrd', '( abs ` ( %s ` m ) ) <_ ( %s x. %s )' % (G, C, N32('m'))),
            t([t([zv], 'eqcomd', '%s = %s' % (N32('m'), ZFm))], 'oveq2d', '( %s x. %s ) = ( %s x. %s )' % (C, N32('m'), C, ZFm))], 'breqtrd',
           '( abs ` ( %s ` m ) ) <_ ( %s x. %s )' % (G, C, ZFm))
    am1 = '( %s /\\ m e. ( ZZ>= ` 1 ) )' % a
    mn1 = w.s([w.s([], 'simpr', '( %s -> m e. ( ZZ>= ` 1 ) )' % am1), w.s([w.s([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )')], 'eleq2i', '( m e. NN <-> m e. ( ZZ>= ` 1 ) )')], 'biimpri',
                                                                   '( m e. ( ZZ>= ` 1 ) -> m e. NN )')], 'syl', '( %s -> m e. NN )' % am1)
    b2 = w.s([w.s([w.s([b1], 'ex', '( %s -> ( m e. NN -> ( abs ` ( %s ` m ) ) <_ ( %s x. %s ) ) )' % (a, G, C, ZFm))], 'adantr',
                  '( %s -> ( m e. NN -> ( abs ` ( %s ` m ) ) <_ ( %s x. %s ) ) )' % (am1, G, C, ZFm)), mn1], 'mpd', '( %s -> ( abs ` ( %s ` m ) ) <_ ( %s x. %s ) )' % (am1, G, C, ZFm))
    return st([w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'), a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN'), zre, gc, zcv32(w, a), cr, b2], 'cvgcmpce', 'seq 1 ( + , %s ) e. dom ~~>' % G)


TNF = '( n e. NN |-> %s )' % TN('n')
S_['gf2ancv'] = '( %s -> seq 1 ( + , %s ) e. dom ~~> )' % (AH, TNF)


def tpifacts(w, a):
    st = mkst(w, a)
    ic = a1(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC'); pic = a1(w, a, w.s([], 'picn', '_pi e. CC'), '_pi e. CC')
    tpc = st([st([], '2cnd', '2 e. CC'), st([ic, pic], 'mulcld', '( _i x. _pi ) e. CC')], 'mulcld', '%s e. CC' % TPI)
    # | TPI | = 2 pi >_ 1
    a1_ = st([st([], '2cnd', '2 e. CC'), st([ic, pic], 'mulcld', '( _i x. _pi ) e. CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) )' % TPI)
    a2 = st([ic, pic], 'absmuld', '( abs ` ( _i x. _pi ) ) = ( ( abs ` _i ) x. ( abs ` _pi ) )')
    pir = a1(w, a, w.s([], 'pire', '_pi e. RR'), '_pi e. RR')
    pi3 = a1(w, a, w.s([], 'pigt3', '3 < _pi'), '3 < _pi')
    pi0 = lin.linarith(w, a, [pi3], '0 <_ _pi', leaves={'_pi': pir})
    ap = st([pir, pi0], 'absidd', '( abs ` _pi ) = _pi')
    a2v = st([a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR'), a1(w, a, w.s([], '0le2', '0 <_ 2'), '0 <_ 2')], 'absidd', '( abs ` 2 ) = 2')
    ai = a1(w, a, w.s([], 'absi', '( abs ` _i ) = 1'), '( abs ` _i ) = 1')
    v = st([a1_, st([a2v, st([a2, st([ai, ap], 'oveq12d', '( ( abs ` _i ) x. ( abs ` _pi ) ) = ( 1 x. _pi )')], 'eqtrd', '( abs ` ( _i x. _pi ) ) = ( 1 x. _pi )')],
                    'oveq12d', '( ( abs ` 2 ) x. ( abs ` ( _i x. _pi ) ) ) = ( 2 x. ( 1 x. _pi ) )')], 'eqtrd', '( abs ` %s ) = ( 2 x. ( 1 x. _pi ) )' % TPI)
    ge = lin.linarith(w, a, [pi3], '1 <_ ( 2 x. ( 1 x. _pi ) )', leaves={'_pi': pir})
    tge = st([ge, v], 'breqtrrd', '1 <_ ( abs ` %s )' % TPI)
    return tpc, tge


def avteq(w, X, n, m):
    """( n = m -> AVT ( X , n ) = AVT ( X , m ) )"""
    E = '%s = %s' % (n, m)
    at = '( %s /\\ t e. RR )' % E
    e1 = w.s([w.s([w.s([w.s([w.s([], 'simpl', '( %s -> %s )' % (at, E))], 'negeqd', '( %s -> -u %s = -u %s )' % (at, n, m))], 'oveq1d',
                        '( %s -> ( -u %s / ( exp ` t ) ) = ( -u %s / ( exp ` t ) ) )' % (at, n, m))], 'fveq2d',
                  '( %s -> ( exp ` ( -u %s / ( exp ` t ) ) ) = ( exp ` ( -u %s / ( exp ` t ) ) ) )' % (at, n, m))], 'idi',
             '( %s -> ( exp ` ( -u %s / ( exp ` t ) ) ) = ( exp ` ( -u %s / ( exp ` t ) ) ) )' % (at, n, m))
    D = lambda k: 'S_ [ %s -> ( %s + L ) ] ( exp ` ( -u %s / ( exp ` t ) ) ) _d t' % (X, X, k)
    e2 = w.s([e1], 'ditgeq3dv', '( %s -> %s = %s )' % (E, D(n), D(m)))
    return w.s([e2], 'oveq2d', '( %s -> %s = %s )' % (E, AVT(X, n), AVT(X, m)))


def tnval(w, am, mn, m):
    """( am -> ( TNF ` m ) = TN ( m ) ) by fvmptg with a hand congruence (the ditg is outside congr's grammar)"""
    E = 'n = %s' % m
    idn = w.s([], 'id', '( %s -> n = %s )' % (E, m))
    cst, _ = w.congr(CN('n'), {'n': m}, E, {'n': idn})
    wst = w.s([avteq(w, 'B', 'n', m), avteq(w, 'A', 'n', m)], 'oveq12d', '( %s -> %s = %s )' % (E, WN('n'), WN(m)))
    sub = w.s([cst, wst], 'oveq12d', '( %s -> %s = %s )' % (E, TN('n'), TN(m)))
    fv = w.s([sub, w.s([], 'eqid', '%s = %s' % (TNF, TNF))], 'fvmptg', '( ( %s e. NN /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (m, TN(m), TNF, m, TN(m)))
    return w.s([mn, w.s([], 'ovexd', '( %s -> %s e. _V )' % (am, TN(m))), fv], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (am, TNF, m, TN(m)))


def gf2ancv():
    w = W('gf2ancv', 'The anchor series converges absolutely: at height ` T = 1 ` , '
          '` | 2 pi i c_K W ( K ) | <_ | lint F_K | + | lint F_K - 2 pi i c_K W ( K ) | ` (~ gf2anb , ~ gf2aerr ) is ` O ( K ^ -u ( 3 / 2 ) ) ` , '
          'and ` | 2 pi i | >_ 1 ` (Lean ` summable_Tanc ` via ` hsummable ` ).')
    a = AH; st = mkst(w, a); f = ahf(w, a, None)
    tpc, tge = tpifacts(w, a)
    k0r, eer = k0real(w, a, f)
    E41 = '( 2 ^c -u ( 1 / 4 ) )'
    lr = st([f['L e. RR+']], 'rpred', 'L e. RR')
    l2 = a1(w, a, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'),
                       w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('loggt0b')], 'ax-mp', '( 0 < ( log ` 2 ) <-> 1 < 2 )')], 'mpbir', '0 < ( log ` 2 )')],
                      'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    ilr = st([st([l2], 'rpreccld', '( 1 / ( log ` 2 ) ) e. RR+')], 'rpred', '( 1 / ( log ` 2 ) ) e. RR')
    e3 = {}
    for X in ('B', 'A'):
        e3[X] = st([st([st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), st([f['%s e. RR' % X], lr], 'readdcld', '( %s + L ) e. RR' % X)], 'remulcld',
                           '( 3 x. ( %s + L ) ) e. RR' % X)], 'rpefcld', '%s e. RR+' % E3('( %s + L )' % X))], 'rpred', '%s e. RR' % E3('( %s + L )' % X))
    k1r = st([st([st([a1(w, a, num.re_nat(w, 1024), '; ; ; 1 0 2 4 e. RR'), f['H e. RR']], 'remulcld', '( ; ; ; 1 0 2 4 x. H ) e. RR'), ilr], 'remulcld',
                 '( ( ; ; ; 1 0 2 4 x. H ) x. ( 1 / ( log ` 2 ) ) ) e. RR'), st([e3['B'], e3['A']], 'readdcld', '( %s + %s ) e. RR' % (E3('( B + L )'), E3('( A + L )')))],
             'remulcld', '%s e. RR' % K1)
    e41 = st([st([a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), litr(w, a, '-u ( 1 / 4 )')], 'rpcxpcld', '%s e. RR+' % E41)], 'rpred', '%s e. RR' % E41)
    C3 = '( ( %s x. 2 ) + ( %s x. %s ) )' % (K0, K1, E41)
    c3r = st([st([k0r, a1(w, a, w.s([], '2re', '2 e. RR'), '2 e. RR')], 'remulcld', '( %s x. 2 ) e. RR' % K0), st([k1r, e41], 'remulcld', '( %s x. %s ) e. RR' % (K1, E41))],
             'readdcld', '%s e. RR' % C3)

    def body(am, mn):
        t = mkst(w, am)
        fm = liftd(w, f, am)
        one = a1(w, am, w.s([], '1rp', '1 e. RR+'), '1 e. RR+')
        sub1 = {'T': '1', 'K': 'm'}
        anb = t([t([proj(w, am, AH), t([one, mn], 'jca', '( 1 e. RR+ /\\ m e. NN )')], 'jca', tsub(split_imp(S_['gf2anb'])[0], sub1)), w.inst('gf2anb')], 'syl',
                tsub(split_imp(S_['gf2anb'])[1], sub1))
        aer = t([t([proj(w, am, AH), t([t([a1(w, am, w.s([], '1re', '1 e. RR'), '1 e. RR'), a1(w, am, w.s([w.s([], '1re', '1 e. RR')], 'leidi', '1 <_ 1'), '1 <_ 1')], 'jca',
                                          '( 1 e. RR /\\ 1 <_ 1 )'), mn], 'jca', '( ( 1 e. RR /\\ 1 <_ 1 ) /\\ m e. NN )')], 'jca', tsub(split_imp(S_['gf2aerr'])[0], sub1)),
                    w.inst('gf2aerr')], 'syl', tsub(split_imp(S_['gf2aerr'])[1], sub1))
        LF = tsub(LFK, sub1); TM = TN('m'); P = '( %s x. %s )' % (TPI, TM)
        cm = cnb(w, am, fm, mn, 'm')
        m0 = t([cm['krp']], 'rpge0d', '0 <_ m')
        avb = avtre(w, am, fm, 'B', cm['kr'], m0, 'm'); ava = avtre(w, am, fm, 'A', cm['kr'], m0, 'm')
        wnc = t([t([avb, ava], 'resubcld', '%s e. RR' % WN('m'))], 'recnd', '%s e. CC' % WN('m'))
        tmc = t([cm['cnc'], wnc], 'mulcld', '%s e. CC' % TM)
        pc = t([lift(w, tpc, am), tmc], 'mulcld', '%s e. CC' % P)
        lfc = t([anb, w.inst('z6absle')], 'syl', '%s e. CC' % LF)
        nn_ = t([lfc, pc], 'nncand', '( %s - ( %s - %s ) ) = %s' % (LF, LF, P, P))
        tri = t([lfc, t([lfc, pc], 'subcld', '( %s - %s ) e. CC' % (LF, P))], 'abs2dif2d', '( abs ` ( %s - ( %s - %s ) ) ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (LF, LF, P, LF, LF, P))
        b1 = t([t([nn_], 'fveq2d', '( abs ` ( %s - ( %s - %s ) ) ) = ( abs ` %s )' % (LF, LF, P, P)), tri], 'eqbrtrrd', '( abs ` %s ) <_ ( ( abs ` %s ) + ( abs ` ( %s - %s ) ) )' % (P, LF, LF, P))
        n32 = t([n32f(w, am, mn, 'm')], 'rpred', '%s e. RR' % N32('m'))
        B1 = '( ( %s x. %s ) x. ( 2 x. 1 ) )' % (K0, N32('m')); B2 = '( ( %s x. %s ) x. %s )' % (K1, N32('m'), E41)
        b1r = t([t([lift(w, k0r, am), n32], 'remulcld', '( %s x. %s ) e. RR' % (K0, N32('m'))), a1(w, am, w.s([w.s([], '2re', '2 e. RR'), w.s([], '1re', '1 e. RR')], 'remulcli', '( 2 x. 1 ) e. RR'),
                                                                                               '( 2 x. 1 ) e. RR')], 'remulcld', '%s e. RR' % B1)
        b2r = t([t([lift(w, k1r, am), n32], 'remulcld', '( %s x. %s ) e. RR' % (K1, N32('m'))), lift(w, e41, am)], 'remulcld', '%s e. RR' % B2)
        b2 = t([t([lfc], 'abscld', '( abs ` %s ) e. RR' % LF), t([t([lfc, pc], 'subcld', '( %s - %s ) e. CC' % (LF, P))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (LF, P)),
                b1r, b2r, anb, aer], 'le2addd', '( ( abs ` %s ) + ( abs ` ( %s - %s ) ) ) <_ ( %s + %s )' % (LF, LF, P, B1, B2))
        cl = Closure(w, am, {K0: lift(w, k0r, am), K1: lift(w, k1r, am), E41: lift(w, e41, am), N32('m'): n32})
        rq = ringeq(w, am, '( %s + %s )' % (B1, B2), '( %s x. %s )' % (C3, N32('m')), cl)
        pr = t([pc], 'abscld', '( abs ` %s ) e. RR' % P)
        sR = t([t([lfc], 'abscld', '( abs ` %s ) e. RR' % LF), t([t([lfc, pc], 'subcld', '( %s - %s ) e. CC' % (LF, P))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (LF, P))],
               'readdcld', '( ( abs ` %s ) + ( abs ` ( %s - %s ) ) ) e. RR' % (LF, LF, P))
        bR = t([b1r, b2r], 'readdcld', '( %s + %s ) e. RR' % (B1, B2))
        b3a = t([pr, sR, bR, b1, b2], 'letrd', '( abs ` %s ) <_ ( %s + %s )' % (P, B1, B2))
        b3 = t([b3a, rq], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (P, C3, N32('m')))
        tr_ = t([tmc], 'abscld', '( abs ` %s ) e. RR' % TM)
        tpr = t([lift(w, tpc, am)], 'abscld', '( abs ` %s ) e. RR' % TPI)
        l1 = t([a1(w, am, w.s([], '1re', '1 e. RR'), '1 e. RR'), tpr, tr_, t([tmc], 'absge0d', '0 <_ ( abs ` %s )' % TM), lift(w, tge, am)], 'lemul1ad',
               '( 1 x. ( abs ` %s ) ) <_ ( ( abs ` %s ) x. ( abs ` %s ) )' % (TM, TPI, TM))
        l2_ = t([l1, t([t([t([tr_], 'recnd', '( abs ` %s ) e. CC' % TM)], 'mullidd', '( 1 x. ( abs ` %s ) ) = ( abs ` %s )' % (TM, TM))], 'eqcomd',
                       '( abs ` %s ) = ( 1 x. ( abs ` %s ) )' % (TM, TM)),
                 t([lift(w, tpc, am), tmc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (P, TPI, TM))], '3brtr4d',
                '( abs ` %s ) <_ ( abs ` %s )' % (TM, P))
        vb = t([tr_, pr, t([lift(w, c3r, am), n32], 'remulcld', '( %s x. %s ) e. RR' % (C3, N32('m'))), l2_, b3], 'letrd', '( abs ` %s ) <_ ( %s x. %s )' % (TM, C3, N32('m')))
        eq = tnval(w, am, mn, 'm')
        return eq, tmc, vb, TM
    fin = cvg32(w, a, TNF, body, C3, c3r)
    w.qed([fin], 'idi', S_['gf2ancv'])
    return w


def tneq(w, n, m):
    """( n = m -> TN ( n ) = TN ( m ) )"""
    E = '%s = %s' % (n, m)
    idn = w.s([], 'id', '( %s -> %s )' % (E, E))
    cst, _ = w.congr(CN(n), {n: m}, E, {n: idn})
    wst = w.s([avteq(w, 'B', n, m), avteq(w, 'A', n, m)], 'oveq12d', '( %s -> %s = %s )' % (E, WN(n), WN(m)))
    return w.s([cst, wst], 'oveq12d', '( %s -> %s = %s )' % (E, TN(n), TN(m)))


def fvh(w, am, mn, x, m, F, bm, sub):
    """( am -> ( F ` m ) = bm ) by fvmptg from sub: ( x = m -> body = bm ); F = ( x e. NN |-> body )"""
    fv = w.s([sub, w.s([], 'eqid', '%s = %s' % (F, F))], 'fvmptg', '( ( %s e. NN /\\ %s e. _V ) -> ( %s ` %s ) = %s )' % (m, bm, F, m, bm))
    ex = w.s([], 'fvexd' if bm.split()[2] == '`' else 'ovexd', '( %s -> %s e. _V )' % (am, bm))
    return w.s([mn, ex, fv], 'syl2anc', '( %s -> ( %s ` %s ) = %s )' % (am, F, m, bm))


LFq = lambda q: tsub(LFK, {'K': q})
EQ = lambda q: '( %s - ( %s x. %s ) )' % (LFq(q), TPI, TN(q))
EFF = '( q e. NN |-> %s )' % EQ('q')
AEFF = '( q e. NN |-> ( abs ` %s ) )' % EQ('q')
CE = '( %s x. %s )' % (K1, E4T)
BFF = '( q e. NN |-> ( %s x. %s ) )' % (CE, N32('q'))
TSF = '( n e. NN |-> ( %s x. %s ) )' % (TPI, TN('n'))
Z32 = 'sum_ m e. NN %s' % N32('m')
S_['gf2anbd'] = ('( ( %s /\\ ( T e. RR /\\ 1 <_ T ) ) -> ( abs ` ( %s - ( %s x. sum_ m e. NN %s ) ) ) <_ ( ( %s x. %s ) x. %s ) )'
                 % (AH, LIt(GA, '1', 'T'), TPI, TN('m'), K1, Z32, E4T))


def eqsub(w, m):
    """( q = m -> EQ ( q ) = EQ ( m ) ) and the abs version"""
    E = 'q = %s' % m
    idq = w.s([], 'id', '( %s -> %s )' % (E, E))
    lst, _ = w.congr(LFq('q'), {'q': m}, E, {'q': idq})
    tst = w.s([tneq(w, 'q', m)], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. %s ) )' % (E, TPI, TN('q'), TPI, TN(m)))
    e = w.s([lst, tst], 'oveq12d', '( %s -> %s = %s )' % (E, EQ('q'), EQ(m)))
    return e, w.s([e], 'fveq2d', '( %s -> ( abs ` %s ) = ( abs ` %s ) )' % (E, EQ('q'), EQ(m)))


def gf2anbd():
    w = W('gf2anbd', 'At every height ` T >_ 1 ` the truncated anchor line integral is within ` K1 Z 2 ^ ( - T / 4 ) ` of ` 2 pi i ` times '
          'the anchor series, ` Z = sum_ m m ^ -u ( 3 / 2 ) ` (~ gf2anl , ~ gf2aerr , ~ gf2ancv , ~ isumadd , ~ iserabs , ~ isumle ).')
    a = split_imp(S_['gf2anbd'])[0]; st = mkst(w, a); f = ahf(w, a, None)
    tr = proj(w, a, 'T e. RR'); t1 = proj(w, a, '1 <_ T')
    trp = st([tr, lin.linarith(w, a, [t1], '0 < T', leaves={'T': tr})], 'elrpd', 'T e. RR+')
    ah = proj(w, a, AH)
    LIT = LIt(GA, '1', 'T')
    anl = st([st([ah, trp], 'jca', split_imp(S_['gf2anl'])[0]), w.inst('gf2anl')], 'syl', split_imp(S_['gf2anl'])[1])
    LFF = '( k e. NN |-> ( ( %s ` k ) lint <. %s , %s >. ) )' % (FNS, SA, SB)
    tncv = st([ah, w.inst('gf2ancv')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % TNF)
    tpc, tge = tpifacts(w, a)
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); z1 = a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')
    e4p = st([a1(w, a, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), st([st([tr, a1(w, a, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, a, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                    'redivcld', '( T / 4 ) e. RR')], 'renegcld', '-u ( T / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E4T)
    e4r = st([e4p], 'rpred', '%s e. RR' % E4T)
    lr = st([f['L e. RR+']], 'rpred', 'L e. RR')
    l2 = a1(w, a, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'),
                       w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('loggt0b')], 'ax-mp', '( 0 < ( log ` 2 ) <-> 1 < 2 )')], 'mpbir', '0 < ( log ` 2 )')],
                      'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    ilr = st([st([l2], 'rpreccld', '( 1 / ( log ` 2 ) ) e. RR+')], 'rpred', '( 1 / ( log ` 2 ) ) e. RR')
    e3 = {}
    for X in ('B', 'A'):
        e3[X] = st([st([st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), st([f['%s e. RR' % X], lr], 'readdcld', '( %s + L ) e. RR' % X)], 'remulcld',
                           '( 3 x. ( %s + L ) ) e. RR' % X)], 'rpefcld', '%s e. RR+' % E3('( %s + L )' % X))], 'rpred', '%s e. RR' % E3('( %s + L )' % X))
    k1r = st([st([st([a1(w, a, num.re_nat(w, 1024), '; ; ; 1 0 2 4 e. RR'), f['H e. RR']], 'remulcld', '( ; ; ; 1 0 2 4 x. H ) e. RR'), ilr], 'remulcld',
                 '( ( ; ; ; 1 0 2 4 x. H ) x. ( 1 / ( log ` 2 ) ) ) e. RR'), st([e3['B'], e3['A']], 'readdcld', '( %s + %s ) e. RR' % (E3('( B + L )'), E3('( A + L )')))],
             'remulcld', '%s e. RR' % K1)
    cer = st([k1r, e4r], 'remulcld', '%s e. RR' % CE)

    def err(am, mn, m):
        t = mkst(w, am)
        sub = {'K': m}
        return t([t([proj(w, am, AH), t([t([lift(w, tr, am), lift(w, t1, am)], 'jca', '( T e. RR /\\ 1 <_ T )'), mn], 'jca', '( ( T e. RR /\\ 1 <_ T ) /\\ %s e. NN )' % m)],
                    'jca', tsub(split_imp(S_['gf2aerr'])[0], sub)), w.inst('gf2aerr')], 'syl', tsub(split_imp(S_['gf2aerr'])[1], sub))

    def ceb(am, mn, m):
        """( abs ` EQ ( m ) ) <_ ( CE x. N32 ( m ) )"""
        t = mkst(w, am)
        b = err(am, mn, m)
        n32 = t([n32f(w, am, mn, m)], 'rpred', '%s e. RR' % N32(m))
        cl = Closure(w, am, {K1: lift(w, k1r, am), E4T: lift(w, e4r, am), N32(m): n32})
        rq = ringeq(w, am, '( ( %s x. %s ) x. %s )' % (K1, N32(m), E4T), '( %s x. %s )' % (CE, N32(m)), cl)
        return t([b, rq], 'breqtrd', '( abs ` %s ) <_ ( %s x. %s )' % (EQ(m), CE, N32(m)))

    def efb(am, mn):
        t = mkst(w, am)
        b = ceb(am, mn, 'm')
        eq = fvh(w, am, mn, 'q', 'm', EFF, EQ('m'), eqsub(w, 'm')[0])
        return eq, t([b, w.inst('z6absle')], 'syl', '%s e. CC' % EQ('m')), b, EQ('m')
    ecv = cvg32(w, a, EFF, efb, CE, cer)

    def aefb(am, mn):
        t = mkst(w, am)
        b = ceb(am, mn, 'm')
        emc = t([b, w.inst('z6absle')], 'syl', '%s e. CC' % EQ('m'))
        eq = fvh(w, am, mn, 'q', 'm', AEFF, '( abs ` %s )' % EQ('m'), eqsub(w, 'm')[1])
        aer = t([emc], 'abscld', '( abs ` %s ) e. RR' % EQ('m'))
        aa = t([aer, t([emc], 'absge0d', '0 <_ ( abs ` %s )' % EQ('m'))], 'absidd', '( abs ` ( abs ` %s ) ) = ( abs ` %s )' % (EQ('m'), EQ('m')))
        return eq, t([aer], 'recnd', '( abs ` %s ) e. CC' % EQ('m')), t([aa, b], 'eqbrtrd', '( abs ` ( abs ` %s ) ) <_ ( %s x. %s )' % (EQ('m'), CE, N32('m'))), '( abs ` %s )' % EQ('m')
    aecv = cvg32(w, a, AEFF, aefb, CE, cer)
    # CE >_ 0 from m = 1
    one = a1(w, a, w.s([], '1nn', '1 e. NN'), '1 e. NN')
    eb1 = ceb(a, one, '1')
    e1c = st([eb1, w.inst('z6absle')], 'syl', '%s e. CC' % EQ('1'))
    o32 = a1(w, a, w.s([w.s([w.s([w.s([], '3cn', '3 e. CC'), w.s([], '2cn', '2 e. CC'), w.s([], '2ne0', '2 =/= 0')], 'divcli', '( 3 / 2 ) e. CC')], 'negcli', '-u ( 3 / 2 ) e. CC'),
                        w.inst('1cxp')], 'ax-mp', '%s = 1' % N32('1')), '%s = 1' % N32('1'))
    cb1 = st([eb1, st([st([o32], 'oveq2d', '( %s x. %s ) = ( %s x. 1 )' % (CE, N32('1'), CE)), st([st([cer], 'recnd', '%s e. CC' % CE)], 'mulridd', '( %s x. 1 ) = %s' % (CE, CE))],
                      'eqtrd', '( %s x. %s ) = %s' % (CE, N32('1'), CE))], 'breqtrd', '( abs ` %s ) <_ %s' % (EQ('1'), CE))
    ce0 = lin.linarith(w, a, [st([e1c], 'absge0d', '0 <_ ( abs ` %s )' % EQ('1')), cb1], '0 <_ %s' % CE,
                       leaves={'( abs ` %s )' % EQ('1'): st([e1c], 'abscld', '( abs ` %s ) e. RR' % EQ('1')), CE: cer})

    def bfb(am, mn):
        t = mkst(w, am)
        idq = w.s([], 'id', '( q = m -> q = m )')
        sb, _ = w.congr('( %s x. %s )' % (CE, N32('q')), {'q': 'm'}, 'q = m', {'q': idq})
        eq = fvh(w, am, mn, 'q', 'm', BFF, '( %s x. %s )' % (CE, N32('m')), sb)
        n3p = n32f(w, am, mn, 'm'); n3r = t([n3p], 'rpred', '%s e. RR' % N32('m'))
        vr = t([lift(w, cer, am), n3r], 'remulcld', '( %s x. %s ) e. RR' % (CE, N32('m')))
        v0 = t([lift(w, cer, am), n3r, lift(w, ce0, am), t([n3p], 'rpge0d', '0 <_ %s' % N32('m'))], 'mulge0d', '0 <_ ( %s x. %s )' % (CE, N32('m')))
        vc = t([vr], 'recnd', '( %s x. %s ) e. CC' % (CE, N32('m')))
        return eq, vc, t([t([vc], 'abscld', '( abs ` ( %s x. %s ) ) e. RR' % (CE, N32('m'))), t([vr, v0], 'absidd', '( abs ` ( %s x. %s ) ) = ( %s x. %s )' % (CE, N32('m'), CE, N32('m')))],
                                                                           'eqled', '( abs ` ( %s x. %s ) ) <_ ( %s x. %s )' % (CE, N32('m'), CE, N32('m'))), '( %s x. %s )' % (CE, N32('m'))
    bcv = cvg32(w, a, BFF, bfb, CE, cer)
    # the sums over m
    am = '( %s /\\ m e. NN )' % a; t = mkst(w, am)
    mn = t([], 'simpr', 'm e. NN')
    fm = liftd(w, f, am)
    anbm = t([t([proj(w, am, AH), t([lift(w, trp, am), mn], 'jca', '( T e. RR+ /\\ m e. NN )')], 'jca', tsub(split_imp(S_['gf2anb'])[0], {'K': 'm'})), w.inst('gf2anb')],
             'syl', tsub(split_imp(S_['gf2anb'])[1], {'K': 'm'}))
    LFm = LFq('m')
    lfc = t([anbm, w.inst('z6absle')], 'syl', '%s e. CC' % LFm)
    lfv, _ = mpv(w, am, 'k', 'NN', '( ( %s ` k ) lint <. %s , %s >. )' % (FNS, SA, SB), 'm', mn)
    s1 = w.s([nnuz, z1, lfv, lfc, anl], 'isumclim', '( %s -> sum_ m e. NN %s = %s )' % (a, LFm, LIT))
    Em = EQ('m')
    emc = t([ceb(am, mn, 'm'), w.inst('z6absle')], 'syl', '%s e. CC' % Em)
    cm = cnb(w, am, fm, mn, 'm')
    m0 = t([cm['krp']], 'rpge0d', '0 <_ m')
    avb = avtre(w, am, fm, 'B', cm['kr'], m0, 'm'); ava = avtre(w, am, fm, 'A', cm['kr'], m0, 'm')
    tmc = t([cm['cnc'], t([t([avb, ava], 'resubcld', '%s e. RR' % WN('m'))], 'recnd', '%s e. CC' % WN('m'))], 'mulcld', '%s e. CC' % TN('m'))
    TSm = '( %s x. %s )' % (TPI, TN('m'))
    tsc = t([lift(w, tpc, am), tmc], 'mulcld', '%s e. CC' % TSm)
    dec = t([t([tsc, lfc], 'pncan3d', '( %s + %s ) = %s' % (TSm, Em, LFm))], 'eqcomd', '%s = ( %s + %s )' % (LFm, TSm, Em))
    s2 = st([dec], 'sumeq2dv', 'sum_ m e. NN %s = sum_ m e. NN ( %s + %s )' % (LFm, TSm, Em))
    tsv = fvh(w, am, mn, 'n', 'm', TSF, TSm, w.s([tneq(w, 'n', 'm')], 'oveq2d', '( n = m -> ( %s x. %s ) = %s )' % (TPI, TN('n'), TSm)))
    efv = fvh(w, am, mn, 'q', 'm', EFF, Em, eqsub(w, 'm')[0])
    tnv = tnval(w, am, mn, 'm')
    # seq TSF converges: TPI times seq TNF
    tnl = w.s([nnuz, z1, tnv, tmc, tncv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> sum_ m e. NN %s )' % (a, TNF, TN('m')))
    ai = '( %s /\\ i e. NN )' % a; ti = mkst(w, ai)
    inn = ti([], 'simpr', 'i e. NN')
    fi = liftd(w, f, ai)
    ci = cnb(w, ai, fi, inn, 'i')
    i0 = ti([ci['krp']], 'rpge0d', '0 <_ i')
    tic = ti([ci['cnc'], ti([ti([avtre(w, ai, fi, 'B', ci['kr'], i0, 'i'), avtre(w, ai, fi, 'A', ci['kr'], i0, 'i')], 'resubcld', '%s e. RR' % WN('i'))], 'recnd',
                            '%s e. CC' % WN('i'))], 'mulcld', '%s e. CC' % TN('i'))
    tnvi = tnval(w, ai, inn, 'i')
    tsvi = fvh(w, ai, inn, 'n', 'i', TSF, '( %s x. %s )' % (TPI, TN('i')), w.s([tneq(w, 'n', 'i')], 'oveq2d', '( n = i -> ( %s x. %s ) = ( %s x. %s ) )' % (TPI, TN('n'), TPI, TN('i'))))
    tnfc = ti([tnvi, tic], 'eqeltrd', '( %s ` i ) e. CC' % TNF)
    tsk = ti([tsvi, ti([tnvi], 'oveq2d', '( %s x. ( %s ` i ) ) = ( %s x. %s )' % (TPI, TNF, TPI, TN('i')))], 'eqtr4d', '( %s ` i ) = ( %s x. ( %s ` i ) )' % (TSF, TPI, TNF))
    tsl = w.s([nnuz, z1, tpc, tnl, tnfc, tsk], 'isermulc2', '( %s -> seq 1 ( + , %s ) ~~> ( %s x. sum_ m e. NN %s ) )' % (a, TSF, TPI, TN('m')))
    tscv = st([a1(w, a, w.s([], 'climrel', 'Rel ~~>'), 'Rel ~~>'), tsl, w.inst('releldm')], 'syl2anc', 'seq 1 ( + , %s ) e. dom ~~>' % TSF)
    s3 = w.s([nnuz, z1, tsv, tsc, efv, emc, tscv, ecv], 'isumadd', '( %s -> sum_ m e. NN ( %s + %s ) = ( sum_ m e. NN %s + sum_ m e. NN %s ) )' % (a, TSm, Em, TSm, Em))
    s4 = w.s([nnuz, z1, tnv, tmc, tncv, tpc], 'isummulc2', '( %s -> ( %s x. sum_ m e. NN %s ) = sum_ m e. NN %s )' % (a, TPI, TN('m'), TSm))
    SE = 'sum_ m e. NN %s' % Em; STS = 'sum_ m e. NN %s' % TN('m')
    lit = st([st([st([s1], 'eqcomd', '%s = sum_ m e. NN %s' % (LIT, LFm)), s2], 'eqtrd', '%s = sum_ m e. NN ( %s + %s )' % (LIT, TSm, Em)),
              st([s3, st([st([s4], 'eqcomd', 'sum_ m e. NN %s = ( %s x. %s )' % (TSm, TPI, STS))], 'oveq1d', '( sum_ m e. NN %s + %s ) = ( ( %s x. %s ) + %s )' % (TSm, SE, TPI, STS, SE))],
                 'eqtrd', 'sum_ m e. NN ( %s + %s ) = ( ( %s x. %s ) + %s )' % (TSm, Em, TPI, STS, SE))], 'eqtrd', '%s = ( ( %s x. %s ) + %s )' % (LIT, TPI, STS, SE))
    stsc = w.s([nnuz, z1, tnv, tmc, tncv], 'isumcl', '( %s -> %s e. CC )' % (a, STS))
    sec = w.s([nnuz, z1, efv, emc, ecv], 'isumcl', '( %s -> %s e. CC )' % (a, SE))
    tstc = st([tpc, stsc], 'mulcld', '( %s x. %s ) e. CC' % (TPI, STS))
    df = st([st([lit], 'oveq1d', '( %s - ( %s x. %s ) ) = ( ( ( %s x. %s ) + %s ) - ( %s x. %s ) )' % (LIT, TPI, STS, TPI, STS, SE, TPI, STS)),
             st([tstc, sec], 'pncan2d', '( ( ( %s x. %s ) + %s ) - ( %s x. %s ) ) = %s' % (TPI, STS, SE, TPI, STS, SE))], 'eqtrd', '( %s - ( %s x. %s ) ) = %s' % (LIT, TPI, STS, SE))
    # | SE | <_ sum | E | <_ CE Z32
    ASE = 'sum_ m e. NN ( abs ` %s )' % Em
    aefv = fvh(w, am, mn, 'q', 'm', AEFF, '( abs ` %s )' % Em, eqsub(w, 'm')[1])
    ec1 = w.s([nnuz, z1, efv, emc, ecv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (a, EFF, SE))
    aemc = t([t([emc], 'abscld', '( abs ` %s ) e. RR' % Em)], 'recnd', '( abs ` %s ) e. CC' % Em)
    ec2 = w.s([nnuz, z1, aefv, aemc, aecv], 'isumclim2', '( %s -> seq 1 ( + , %s ) ~~> %s )' % (a, AEFF, ASE))
    efc = t([efv, emc], 'eqeltrd', '( %s ` m ) e. CC' % EFF)
    ga = t([aefv, t([efv], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` %s )' % (EFF, Em))], 'eqtr4d', '( %s ` m ) = ( abs ` ( %s ` m ) )' % (AEFF, EFF))
    ia = w.s([nnuz, ec1, ec2, z1, efc, ga], 'iserabs', '( %s -> ( abs ` %s ) <_ %s )' % (a, SE, ASE))
    idq = w.s([], 'id', '( q = m -> q = m )')
    sbf, _ = w.congr('( %s x. %s )' % (CE, N32('q')), {'q': 'm'}, 'q = m', {'q': idq})
    bfv = fvh(w, am, mn, 'q', 'm', BFF, '( %s x. %s )' % (CE, N32('m')), sbf)
    n3r = t([n32f(w, am, mn, 'm')], 'rpred', '%s e. RR' % N32('m'))
    il = w.s([nnuz, z1, aefv, t([emc], 'abscld', '( abs ` %s ) e. RR' % Em), bfv, t([lift(w, cer, am), n3r], 'remulcld', '( %s x. %s ) e. RR' % (CE, N32('m'))),
              ceb(am, mn, 'm'), aecv, bcv], 'isumle', '( %s -> %s <_ sum_ m e. NN ( %s x. %s ) )' % (a, ASE, CE, N32('m')))
    zv, _ = mpv(w, am, 'n', 'NN', N32('n'), 'm', mn)
    zc = zcv32(w, a)
    im2 = w.s([nnuz, z1, zv, t([n3r], 'recnd', '%s e. CC' % N32('m')), zc, st([cer], 'recnd', '%s e. CC' % CE)], 'isummulc2',
              '( %s -> ( %s x. %s ) = sum_ m e. NN ( %s x. %s ) )' % (a, CE, Z32, CE, N32('m')))
    b2 = st([il, st([im2], 'eqcomd', 'sum_ m e. NN ( %s x. %s ) = ( %s x. %s )' % (CE, N32('m'), CE, Z32))], 'breqtrd', '%s <_ ( %s x. %s )' % (ASE, CE, Z32))
    z2r = w.s([nnuz, z1, zv, n3r, zc], 'isumrecl', '( %s -> %s e. RR )' % (a, Z32))
    ser = st([sec], 'abscld', '( abs ` %s ) e. RR' % SE)
    aser = w.s([nnuz, z1, aefv, t([emc], 'abscld', '( abs ` %s ) e. RR' % Em), aecv], 'isumrecl', '( %s -> %s e. RR )' % (a, ASE))
    b3 = st([ser, aser, st([cer, z2r], 'remulcld', '( %s x. %s ) e. RR' % (CE, Z32)), ia, b2], 'letrd', '( abs ` %s ) <_ ( %s x. %s )' % (SE, CE, Z32))
    m32 = st([st([k1r], 'recnd', '%s e. CC' % K1), st([e4r], 'recnd', '%s e. CC' % E4T), st([z2r], 'recnd', '%s e. CC' % Z32)], 'mul32d',
             '( ( %s x. %s ) x. %s ) = ( ( %s x. %s ) x. %s )' % (K1, E4T, Z32, K1, Z32, E4T))
    b4 = st([b3, m32], 'breqtrd', '( abs ` %s ) <_ ( ( %s x. %s ) x. %s )' % (SE, K1, Z32, E4T))
    w.qed([st([df], 'fveq2d', '( abs ` ( %s - ( %s x. %s ) ) ) = ( abs ` %s )' % (LIT, TPI, STS, SE)), b4], 'eqbrtrd', S_['gf2anbd'])
    return w


LIt_ = lambda G, c, t: '( %s lint <. ( %s + ( _i x. -u %s ) ) , ( %s + ( _i x. %s ) ) >. )' % (G, c, t, c, t)
VLF = lambda G, c: '( t e. RR+ |-> %s )' % LIt_(G, c, 't')
VL = lambda G, c: '( ~~>r ` %s )' % VLF(G, c)
S_['gf2anchor'] = '( %s -> ( seq 1 ( + , %s ) e. dom ~~> /\\ ( %s x. sum_ n e. NN %s ) = %s ) )' % (AH, TNF, TPI, TN('n'), VL(GA, '1'))


def gf2anchor():
    w = W('gf2anchor', 'The anchor identity (Lean ` Bgram_eq_integral_anchor ` , generic in the windows and the coefficients): the series '
          '` sum_n c_n W ( n ) ` converges and ` 2 pi i ` times its sum is the vertical line integral of ` GA ` on ` Re w = 1 ` '
          '(~ gf2ancv , ~ gf2anbd , ~ z6e4lim , ~ rlimsqzlem , ~ rlimuni ).')
    a = AH; st = mkst(w, a); f = ahf(w, a, None)
    stcv = w.s([], 'gf2ancv', S_['gf2ancv'])
    STS = 'sum_ m e. NN %s' % TN('m'); VV = '( %s x. %s )' % (TPI, STS)
    nnuz = w.s([], 'nnuz', 'NN = ( ZZ>= ` 1 )'); z1 = a1(w, a, w.s([], '1z', '1 e. ZZ'), '1 e. ZZ')
    am = '( %s /\\ m e. NN )' % a; t_ = mkst(w, am)
    mn = t_([], 'simpr', 'm e. NN')
    fm = liftd(w, f, am)
    cm = cnb(w, am, fm, mn, 'm')
    m0 = t_([cm['krp']], 'rpge0d', '0 <_ m')
    tmc = t_([cm['cnc'], t_([t_([avtre(w, am, fm, 'B', cm['kr'], m0, 'm'), avtre(w, am, fm, 'A', cm['kr'], m0, 'm')], 'resubcld', '%s e. RR' % WN('m'))], 'recnd',
                            '%s e. CC' % WN('m'))], 'mulcld', '%s e. CC' % TN('m'))
    tnv = tnval(w, am, mn, 'm')
    stsc = w.s([nnuz, z1, tnv, tmc, stcv], 'isumcl', '( %s -> %s e. CC )' % (a, STS))
    tpc, tge = tpifacts(w, a)
    vvc = st([tpc, stsc], 'mulcld', '%s e. CC' % VV)
    # K1 Z32 e. RR
    lr = st([f['L e. RR+']], 'rpred', 'L e. RR')
    l2 = a1(w, a, w.s([w.s([w.s([], '2rp', '2 e. RR+'), w.inst('relogcl')], 'ax-mp', '( log ` 2 ) e. RR'),
                       w.s([w.s([], '1lt2', '1 < 2'), w.s([w.s([], '2rp', '2 e. RR+'), w.inst('loggt0b')], 'ax-mp', '( 0 < ( log ` 2 ) <-> 1 < 2 )')], 'mpbir', '0 < ( log ` 2 )')],
                      'elrpii', '( log ` 2 ) e. RR+'), '( log ` 2 ) e. RR+')
    ilr = st([st([l2], 'rpreccld', '( 1 / ( log ` 2 ) ) e. RR+')], 'rpred', '( 1 / ( log ` 2 ) ) e. RR')
    e3 = {}
    for X in ('B', 'A'):
        e3[X] = st([st([st([a1(w, a, w.s([], '3re', '3 e. RR'), '3 e. RR'), st([f['%s e. RR' % X], lr], 'readdcld', '( %s + L ) e. RR' % X)], 'remulcld',
                           '( 3 x. ( %s + L ) ) e. RR' % X)], 'rpefcld', '%s e. RR+' % E3('( %s + L )' % X))], 'rpred', '%s e. RR' % E3('( %s + L )' % X))
    k1r = st([st([st([a1(w, a, num.re_nat(w, 1024), '; ; ; 1 0 2 4 e. RR'), f['H e. RR']], 'remulcld', '( ; ; ; 1 0 2 4 x. H ) e. RR'), ilr], 'remulcld',
                 '( ( ; ; ; 1 0 2 4 x. H ) x. ( 1 / ( log ` 2 ) ) ) e. RR'), st([e3['B'], e3['A']], 'readdcld', '( %s + %s ) e. RR' % (E3('( B + L )'), E3('( A + L )')))],
             'remulcld', '%s e. RR' % K1)
    zv, _ = mpv(w, am, 'n', 'NN', N32('n'), 'm', mn)
    n3r = t_([n32f(w, am, mn, 'm')], 'rpred', '%s e. RR' % N32('m'))
    z2r = w.s([nnuz, z1, zv, n3r, zcv32(w, a)], 'isumrecl', '( %s -> %s e. RR )' % (a, Z32))
    KZ = '( %s x. %s )' % (K1, Z32)
    kzr = st([k1r, z2r], 'remulcld', '%s e. RR' % KZ)
    E4t = '( 2 ^c -u ( r / 4 ) )'
    B_ = '( %s x. %s )' % (KZ, E4t)
    at = '( %s /\\ r e. RR+ )' % a; tt = mkst(w, at)
    trp = tt([], 'simpr', 'r e. RR+'); tr = tt([trp], 'rpred', 'r e. RR')
    e4r = tt([tt([a1(w, at, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), tt([tt([tr, a1(w, at, w.s([], '4re', '4 e. RR'), '4 e. RR'), a1(w, at, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                         'redivcld', '( r / 4 ) e. RR')], 'renegcld', '-u ( r / 4 ) e. RR')], 'rpcxpcld', '%s e. RR+' % E4t)],
             'rpred', '%s e. RR' % E4t)
    br = tt([lift(w, kzr, at), e4r], 'remulcld', '%s e. RR' % B_)
    kzc = st([kzr], 'recnd', '%s e. CC' % KZ)
    rc = st([a1(w, a, w.s([], 'rpssre', 'RR+ C_ RR'), 'RR+ C_ RR'), kzc, w.inst('rlimconst')], 'syl2anc', '( r e. RR+ |-> %s ) ~~>r %s' % (KZ, KZ))
    E4L = '( r e. RR+ |-> %s ) ~~>r 0' % E4t
    e4l = a1(w, a, w.s([], 'z6e4lim', E4L), E4L)
    rm = w.s([w.s([lift(w, kzc, at)], 'elexd', '( %s -> %s e. _V )' % (at, KZ)), w.s([], 'ovexd', '( %s -> %s e. _V )' % (at, E4t)), rc, e4l], 'rlimmul',
             '( %s -> ( r e. RR+ |-> %s ) ~~>r ( %s x. 0 ) )' % (a, B_, KZ))
    rm0 = st([rm, st([kzc], 'mul01d', '( %s x. 0 ) = 0' % KZ)], 'breqtrd', '( r e. RR+ |-> %s ) ~~>r 0' % B_)
    LIT = LIt_(GA, '1', 'r')
    anl = tt([tt([proj(w, at, AH), trp], 'jca', tsub(split_imp(S_['gf2anl'])[0], {'T': 'r'})), w.inst('gf2anl')], 'syl',
             tsub(split_imp(S_['gf2anl'])[1], {'T': 'r'}))
    lic = tt([anl, w.inst('climcl')], 'syl', '%s e. CC' % LIT)
    at0 = '( %s /\\ ( r e. RR+ /\\ 1 <_ r ) )' % a; t0 = mkst(w, at0)
    trp0 = t0([], 'simprl', 'r e. RR+'); tr0 = t0([trp0], 'rpred', 'r e. RR'); t10 = t0([], 'simprr', '1 <_ r')
    bd0 = t0([t0([proj(w, at0, AH), t0([tr0, t10], 'jca', '( r e. RR /\\ 1 <_ r )')], 'jca', tsub(split_imp(S_['gf2anbd'])[0], {'T': 'r'})), w.inst('gf2anbd')], 'syl',
             tsub(split_imp(S_['gf2anbd'])[1], {'T': 'r'}))
    STn = 'sum_ m e. NN %s' % TN('m')
    br0 = t0([lift(w, kzr, at0), t0([t0([a1(w, at0, w.s([], '2rp', '2 e. RR+'), '2 e. RR+'), t0([t0([tr0, a1(w, at0, w.s([], '4re', '4 e. RR'), '4 e. RR'),
                                                                                                                                  a1(w, at0, w.s([], '4ne0', '4 =/= 0'), '4 =/= 0')],
                                                                                                                                 'redivcld', '( r / 4 ) e. RR')], 'renegcld', '-u ( r / 4 ) e. RR')],
                                                                                   'rpcxpcld', '%s e. RR+' % E4t)], 'rpred', '%s e. RR' % E4t)], 'remulcld', '%s e. RR' % B_)
    bb = t0([t0([br0], 'leabsd', '%s <_ ( abs ` %s )' % (B_, B_)), t0([t0([t0([br0], 'recnd', '%s e. CC' % B_)], 'subid1d', '( %s - 0 ) = %s' % (B_, B_))], 'fveq2d',
                                                                  '( abs ` ( %s - 0 ) ) = ( abs ` %s )' % (B_, B_))], 'breqtrrd', '%s <_ ( abs ` ( %s - 0 ) )' % (B_, B_))
    lic0 = t0([t0([t0([proj(w, at0, AH), trp0], 'jca', tsub(split_imp(S_['gf2anl'])[0], {'T': 'r'})), w.inst('gf2anl')], 'syl', tsub(split_imp(S_['gf2anl'])[1], {'T': 'r'})),
               w.inst('climcl')], 'syl', '%s e. CC' % LIT)
    dr = t0([t0([lic0, lift(w, vvc, at0)], 'subcld', '( %s - %s ) e. CC' % (LIT, VV))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (LIT, VV))
    abr = t0([t0([t0([br0], 'recnd', '%s e. CC' % B_), a1(w, at0, w.s([], '0cn', '0 e. CC'), '0 e. CC')], 'subcld', '( %s - 0 ) e. CC' % B_)], 'abscld', '( abs ` ( %s - 0 ) ) e. RR' % B_)
    h4 = t0([dr, br0, abr, bd0, bb], 'letrd', '( abs ` ( %s - %s ) ) <_ ( abs ` ( %s - 0 ) )' % (LIT, VV, B_))
    VF = '( r e. RR+ |-> %s )' % LIT
    sq = w.s([a1(w, a, w.s([], '1re', '1 e. RR'), '1 e. RR'), vvc, rm0, tt([br], 'recnd', '%s e. CC' % B_), lic, h4], 'rlimsqzlem', '( %s -> %s ~~>r %s )' % (a, VF, VV))
    ff = st([lic, w.s([], 'eqid', '%s = %s' % (VF, VF))], 'fmptd', '%s : RR+ --> CC' % VF)
    sp = a1(w, a, w.s([], 'rpsup', 'sup ( RR+ , RR* , < ) = +oo'), 'sup ( RR+ , RR* , < ) = +oo')
    dm = st([a1(w, a, w.s([], 'rlimrel', 'Rel ~~>r'), 'Rel ~~>r'), sq, w.inst('releldm')], 'syl2anc', '%s e. dom ~~>r' % VF)
    rd = st([dm, w.s([ff, sp], 'rlimdm', '( %s -> ( %s e. dom ~~>r <-> %s ~~>r ( ~~>r ` %s ) ) )' % (a, VF, VF, VF))], 'mpbid', '%s ~~>r ( ~~>r ` %s )' % (VF, VF))
    un = w.s([ff, sp, rd, sq], 'rlimuni', '( %s -> ( ~~>r ` %s ) = %s )' % (a, VF, VV))
    idr = w.s([], 'id', '( r = t -> r = t )')
    cst, _ = w.congr(LIT, {'r': 't'}, 'r = t', {'r': idr})
    cbr = a1(w, a, w.s([cst], 'cbvmptv', '%s = %s' % (VF, VLF(GA, '1'))), '%s = %s' % (VF, VLF(GA, '1')))
    cb = a1(w, a, w.s([tneq(w, 'm', 'n')], 'cbvsumv', '%s = sum_ n e. NN %s' % (STS, TN('n'))), '%s = sum_ n e. NN %s' % (STS, TN('n')))
    fin = st([st([st([cb], 'oveq2d', '%s = ( %s x. sum_ n e. NN %s )' % (VV, TPI, TN('n')))], 'eqcomd', '( %s x. sum_ n e. NN %s ) = %s' % (TPI, TN('n'), VV)),
              st([un, st([cbr], 'fveq2d', '( ~~>r ` %s ) = %s' % (VF, VL(GA, '1')))], 'eqtr3d', '%s = %s' % (VV, VL(GA, '1')))], 'eqtrd', '( %s x. sum_ n e. NN %s ) = %s' % (TPI, TN('n'), VL(GA, '1')))
    stcv2 = st([proj(w, a, AH), w.inst('gf2ancv')], 'syl', 'seq 1 ( + , %s ) e. dom ~~>' % TNF)
    w.qed([stcv2, fin], 'jca', S_['gf2anchor'])
    return w


S_['gf2wnre'] = '( ( ( ( A e. RR /\\ B e. RR ) /\\ L e. RR+ ) /\\ K e. NN ) -> %s e. RR )' % WN('K')


def gf2wnre():
    w = W('gf2wnre', 'The two-window weight ` W ( K ) ` is real (~ z5wavg , ~ xrrege0 ).')
    a = split_imp(S_['gf2wnre'])[0]; st = mkst(w, a)
    f = {'A e. RR': proj(w, a, 'A e. RR'), 'B e. RR': proj(w, a, 'B e. RR'), 'L e. RR+': proj(w, a, 'L e. RR+')}
    kn = proj(w, a, 'K e. NN')
    kr = st([kn], 'nnred', 'K e. RR'); k0 = st([st([kn], 'nnrpd', 'K e. RR+')], 'rpge0d', '0 <_ K')
    fin = st([avtre(w, a, f, 'B', kr, k0), avtre(w, a, f, 'A', kr, k0)], 'resubcld', '%s e. RR' % WN('K'))
    w.qed([fin], 'idi', S_['gf2wnre'])
    return w


if __name__ == '__main__':
    for f in sys.argv[1:]:
        globals()[f]().run()
