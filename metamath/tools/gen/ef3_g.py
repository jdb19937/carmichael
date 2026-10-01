"""Sortie EF3: the left edge (Lean integral_inv_dist_le, stripInt_norm_le, edge_interval_bound, left_edge_le):
ef3vle (vertical lint bounded by a real integral)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
from c10_f import crfacts
import lin
lin.FASTPATH = True
import ef3_a, ef3_c, ef3_e, ef3_f

PQ = '( P [,] Q )'
GL = lambda v: '( abs ` ( G ` ( S + ( _i x. %s ) ) ) )' % v
HM = '( l e. %s |-> %s )' % (PQ, GL('l'))


def vcont(w, A, gc, sr, pr, qr, alx):
    """( A -> HM e. ( PQ -cn-> CC ) ) from G e. ( D -cn-> CC ), S, P, Q reals and alx : A. x e. PQ ( S + i x ) e. D"""
    sA = St(w, A)
    iccc = sA([sA([pr, qr], 'iccssred', '%s C_ RR' % PQ), sA([w.s([], 'ax-resscn', 'RR C_ CC')], 'a1i', 'RR C_ CC')], 'sstrd', '%s C_ CC' % PQ)
    ccss = sA([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC')
    c1 = sA([sA([sr], 'recnd', 'S e. CC'), iccc, ccss, w.inst('cncfmptc')], 'syl3anc', '( l e. %s |-> S ) e. ( %s -cn-> CC )' % (PQ, PQ))
    c2 = sA([sA([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), iccc, ccss, w.inst('cncfmptc')], 'syl3anc', '( l e. %s |-> _i ) e. ( %s -cn-> CC )' % (PQ, PQ))
    c3 = sA([iccc, ccss, w.inst('cncfmptid')], 'syl2anc', '( l e. %s |-> l ) e. ( %s -cn-> CC )' % (PQ, PQ))
    c4 = sA([c2, c3], 'mulcncf', '( l e. %s |-> ( _i x. l ) ) e. ( %s -cn-> CC )' % (PQ, PQ))
    c5 = sA([c1, c4], 'addcncf', '( l e. %s |-> ( S + ( _i x. l ) ) ) e. ( %s -cn-> CC )' % (PQ, PQ))
    # into D
    Al = '( %s /\\ l e. %s )' % (A, PQ)
    eqx, _ = w.wcongr('( S + ( _i x. x ) ) e. D', {'x': 'l'}, 'x = l', {'x': w.s([], 'id', '( x = l -> x = l )')})
    ld = St(w, Al)([eqx, lift(w, alx, Al), St(w, Al)([], 'simpr', 'l e. %s' % PQ)], 'rspcdva', '( S + ( _i x. l ) ) e. D')
    fm = sA([ld], 'fmpttd', '( l e. %s |-> ( S + ( _i x. l ) ) ) : %s --> D' % (PQ, PQ))
    dss = sA([gc, w.inst('cncfrss')], 'syl', 'D C_ CC')
    c6 = sA([fm, sA([dss, c5, w.inst('cncfcdm')], 'syl2anc', '( ( l e. %s |-> ( S + ( _i x. l ) ) ) e. ( %s -cn-> D ) <-> ( l e. %s |-> ( S + ( _i x. l ) ) ) : %s --> D )' % (PQ, PQ, PQ, PQ))],
            'mpbird', '( l e. %s |-> ( S + ( _i x. l ) ) ) e. ( %s -cn-> D )' % (PQ, PQ))
    geq = sA([sA([gc, w.inst('cncff')], 'syl', 'G : D --> CC')], 'feqmptd', 'G = ( y e. D |-> ( G ` y ) )')
    gm = sA([geq, gc], 'eqeltrrd', '( y e. D |-> ( G ` y ) ) e. ( D -cn-> CC )')
    st = w.s([], 'fveq2', '( y = ( S + ( _i x. l ) ) -> ( G ` y ) = ( G ` ( S + ( _i x. l ) ) ) )')
    c7 = sA([w.s([], 'nfv', 'F/ l %s' % A), c6, gm, sA([w.s([], 'ssid', 'D C_ D')], 'a1i', 'D C_ D'), st], 'cncfcompt2', '( l e. %s |-> ( G ` ( S + ( _i x. l ) ) ) ) e. ( %s -cn-> CC )' % (PQ, PQ))
    ssc = w.s([w.s([w.s([], 'ax-resscn', 'RR C_ CC'), w.s([], 'ssid', 'CC C_ CC')], 'pm3.2i', '( RR C_ CC /\\ CC C_ CC )'), w.inst('cncfss')], 'ax-mp', '( CC -cn-> RR ) C_ ( CC -cn-> CC )')
    ab = sA([sA([ssc], 'a1i', '( CC -cn-> RR ) C_ ( CC -cn-> CC )'), sA([w.s([], 'abscncf', 'abs e. ( CC -cn-> RR )')], 'a1i', 'abs e. ( CC -cn-> RR )')], 'sseldd', 'abs e. ( CC -cn-> CC )')
    return sA([ab, c7], 'cncfmpt1f', '%s e. ( %s -cn-> CC )' % (HM, PQ))


def gen_vle():
    w = W('ef3vle', 'A vertical segment integral is bounded by the real integral of the absolute value of the integrand along the height ( ~ lintle , ~ z6aff ).')
    A0, G = ante_of(S['ef3vle'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    gc, sr = conj_split(w, A0, s([], 'simp1', H1))
    pq, plq = conj_split(w, A0, s([], 'simp2', H2))
    pr, qr = conj_split(w, A0, pq)
    alx = s([], 'simp3', H3)
    hc = vcont(w, A0, gc, sr, pr, qr, alx)
    hib = s([pr, qr, hc, w.inst('cniccibl')], 'syl3anc', '%s e. L^1' % HM)
    IOO = '( P (,) Q )'
    ioo = s([w.s([], 'ioossicc', '%s C_ %s' % (IOO, PQ))], 'a1i', '%s C_ %s' % (IOO, PQ))
    Al = '( %s /\\ l e. %s )' % (A0, PQ)
    sl = St(w, Al)
    hf = s([hc, w.inst('cncff')], 'syl', '%s : %s --> CC' % (HM, PQ))
    # pointwise value real: abs is real
    eqx, _ = w.wcongr('( S + ( _i x. x ) ) e. D', {'x': 'l'}, 'x = l', {'x': w.s([], 'id', '( x = l -> x = l )')})
    ldl = sl([eqx, lift(w, alx, Al), sl([], 'simpr', 'l e. %s' % PQ)], 'rspcdva', '( S + ( _i x. l ) ) e. D')
    gcl = sl([sl([lift(w, gc, Al), w.inst('cncff')], 'syl', 'G : D --> CC'), ldl], 'ffvelcdmd', '( G ` ( S + ( _i x. l ) ) ) e. CC')
    glr = sl([gcl], 'abscld', '%s e. RR' % GL('l'))
    ib = s([ioo, s([w.s([], 'ioombl', '%s e. dom vol' % IOO)], 'a1i', '%s e. dom vol' % IOO), sl([glr], 'recnd', '%s e. CC' % GL('l')), hib], 'iblss', '( l e. %s |-> %s ) e. L^1' % (IOO, GL('l')))
    # z6aff
    AF = tsub(ante_of(stmt('z6aff'))[0], {'A': 'P', 'B': 'Q', 'H': HM})
    AFC = tsub(ante_of(stmt('z6aff'))[1], {'A': 'P', 'B': 'Q', 'H': HM})
    za = s([s([s([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )'), plq], 'jca', top_and(AF)[0]), hc], 'jca', AF)
    zf = s([za, w.inst('z6aff')], 'syl', AFC)
    # left side of z6aff: S. IOO ( HM ` u ) _d u = S. IOO GL ( l ) _d l
    Au = '( %s /\\ u e. %s )' % (A0, IOO)
    su = St(w, Au)
    uin = su([su([lift(w, ioo, Au), su([], 'simpr', 'u e. %s' % IOO)], 'sseldd', 'u e. %s' % PQ)], 'id', 'x') if False else su([lift(w, ioo, Au), su([], 'simpr', 'u e. %s' % IOO)], 'sseldd', 'u e. %s' % PQ)
    gcu = w.s([w.s([w.s([w.s([w.s([], 'id', '( l = u -> l = u )')], 'oveq2d', '( l = u -> ( _i x. l ) = ( _i x. u ) )')], 'oveq2d', '( l = u -> ( S + ( _i x. l ) ) = ( S + ( _i x. u ) ) )')], 'fveq2d',
                     '( l = u -> ( G ` ( S + ( _i x. l ) ) ) = ( G ` ( S + ( _i x. u ) ) ) )')], 'fveq2d', '( l = u -> %s = %s )' % (GL('l'), GL('u')))
    eqxu, _ = w.wcongr('( S + ( _i x. x ) ) e. D', {'x': 'u'}, 'x = u', {'x': w.s([], 'id', '( x = u -> x = u )')})
    ldu = su([eqxu, lift(w, alx, Au), uin], 'rspcdva', '( S + ( _i x. u ) ) e. D')
    gur = su([su([su([su([lift(w, gc, Au), w.inst('cncff')], 'syl', 'G : D --> CC'), ldu], 'ffvelcdmd', '( G ` ( S + ( _i x. u ) ) ) e. CC')], 'abscld', '%s e. RR' % GL('u'))], 'id', 'x') if False else \
        su([su([su([lift(w, gc, Au), w.inst('cncff')], 'syl', 'G : D --> CC'), ldu], 'ffvelcdmd', '( G ` ( S + ( _i x. u ) ) ) e. CC')], 'abscld', '%s e. RR' % GL('u'))
    fvu = su([gcu, uin, gur], 'fvmptd3' if False else 'id', 'x') if False else None
    fvu = su([w.s([], 'eqidd', '( %s -> %s = %s )' % (Au, HM, HM)) if False else su([w.s([], 'eqid', '%s = %s' % (HM, HM))], 'a1i', '%s = %s' % (HM, HM)), w.s([gcu], 'adantl', '( ( %s /\\ l = u ) -> %s = %s )' % (Au, GL('l'), GL('u'))), uin, gur], 'fvmptd',
             '( %s ` u ) = %s' % (HM, GL('u')))
    i1 = s([fvu], 'itgeq2dv', 'S. %s ( %s ` u ) _d u = S. %s %s _d u' % (IOO, HM, IOO, GL('u')))
    gul = w.s([w.s([w.s([w.s([w.s([], 'id', '( u = l -> u = l )')], 'oveq2d', '( u = l -> ( _i x. u ) = ( _i x. l ) )')], 'oveq2d', '( u = l -> ( S + ( _i x. u ) ) = ( S + ( _i x. l ) ) )')], 'fveq2d',
                     '( u = l -> ( G ` ( S + ( _i x. u ) ) ) = ( G ` ( S + ( _i x. l ) ) ) )')], 'fveq2d', '( u = l -> %s = %s )' % (GL('u'), GL('l')))
    i2 = s([w.s([gul], 'cbvitgv', 'S. %s %s _d u = S. %s %s _d l' % (IOO, GL('u'), IOO, GL('l')))], 'a1i', 'S. %s %s _d u = S. %s %s _d l' % (IOO, GL('u'), IOO, GL('l')))
    # lintle
    A_, B_ = '( S + ( _i x. P ) )', '( S + ( _i x. Q ) )'
    ac = crfacts(w, A0, 'S', 'P', sr, pr)[0]
    bc = crfacts(w, A0, 'S', 'Q', sr, qr)[0]
    eqt, _ = w.wcongr('( S + ( _i x. x ) ) e. D', {'x': 't'}, 'x = t', {'x': w.s([], 'id', '( x = t -> x = t )')})
    alt = s([alx, w.s([eqt], 'cbvralvw', '( A. x e. %s ( S + ( _i x. x ) ) e. D <-> A. t e. %s ( S + ( _i x. t ) ) e. D )' % (PQ, PQ))], 'sylib', 'A. t e. %s ( S + ( _i x. t ) ) e. D' % PQ)
    from ef3_a import icc_mem
    lv0 = {'P': pr, 'Q': qr}
    pin = icc_mem(w, A0, 'P', 'P', 'Q', pr, pr, qr, lin8(w, A0, [], 'P <_ P', lv0), lin8(w, A0, [plq], 'P <_ Q', lv0))
    qin = icc_mem(w, A0, 'Q', 'P', 'Q', qr, pr, qr, lin8(w, A0, [plq], 'P <_ Q', lv0), lin8(w, A0, [], 'Q <_ Q', lv0))
    VA = tsub(ante_of(S['ef3vseg'])[0], {'P': 'S', 'L': 'P', 'H': 'Q', 'E': 'P', 'K': 'Q'})
    va1, va2 = top_and(VA)
    seg = s([s([s([sr, s([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )')], 'jca', va1), s([s([pin, qin], 'jca', top_and(va2)[0]), alt], 'jca', va2)], 'jca', VA), w.inst('ef3vseg')], 'syl', '( %s cseg %s ) C_ D' % (A_, B_))
    At = '( %s /\\ t e. ( 0 (,) 1 ) )' % A0
    st_ = St(w, At)
    Lt = lambda x: lift(w, x, At)
    tb = st_([st_([], 'simpr', 't e. ( 0 (,) 1 )'), w.inst('eliooord')], 'syl', '( 0 < t /\\ t < 1 )')
    t0, t1 = conj_split(w, At, tb)
    tr = st_([st_([w.s([], 'ioossre', '( 0 (,) 1 ) C_ RR')], 'a1i', '( 0 (,) 1 ) C_ RR'), st_([], 'simpr', 't e. ( 0 (,) 1 )')], 'sseldd', 't e. RR')
    V = '( P + ( t x. ( Q - P ) ) )'
    qpr = st_([Lt(qr), Lt(pr)], 'resubcld', '( Q - P ) e. RR')
    qp0 = lin8(w, At, [Lt(plq)], '0 <_ ( Q - P )', {'P': Lt(pr), 'Q': Lt(qr)})
    tq0 = st_([tr, qpr, lin8(w, At, [t0], '0 <_ t', {'t': tr}), qp0], 'mulge0d', '0 <_ ( t x. ( Q - P ) )')
    tq1 = st_([tr, numst(w, At, '1', 'RR'), qpr, qp0, lin8(w, At, [t1], 't <_ 1', {'t': tr})], 'lemul1ad', '( t x. ( Q - P ) ) <_ ( 1 x. ( Q - P ) )')
    tqr = st_([tr, qpr], 'remulcld', '( t x. ( Q - P ) ) e. RR')
    vr = st_([Lt(pr), tqr], 'readdcld', '%s e. RR' % V)
    lvt = {'P': Lt(pr), 'Q': Lt(qr), '( t x. ( Q - P ) )': tqr}
    vin = icc_mem(w, At, V, 'P', 'Q', vr, Lt(pr), Lt(qr), lin8(w, At, [tq0], 'P <_ %s' % V, lvt), lin8(w, At, [tq1], '%s <_ Q' % V, lvt))
    glv = st_([st_([st_([Lt(gc), w.inst('cncff')], 'syl', 'G : D --> CC'), inst_all_(w, At, Lt(alx), 'x', V, vin, '( S + ( _i x. x ) ) e. D')], 'ffvelcdmd', '( G ` ( S + ( _i x. %s ) ) ) e. CC' % V)], 'abscld', '%s e. RR' % GL(V))
    glc = st_([st_([Lt(gc), w.inst('cncff')], 'syl', 'G : D --> CC'), inst_all_(w, At, Lt(alx), 'x', V, vin, '( S + ( _i x. x ) ) e. D')], 'ffvelcdmd', '( G ` ( S + ( _i x. %s ) ) ) e. CC' % V)
    glv2 = w.s([w.s([w.s([w.s([w.s([], 'id', '( l = %s -> l = %s )' % (V, V))], 'oveq2d', '( l = %s -> ( _i x. l ) = ( _i x. %s ) )' % (V, V))], 'oveq2d', '( l = %s -> ( S + ( _i x. l ) ) = ( S + ( _i x. %s ) ) )' % (V, V))], 'fveq2d',
                      '( l = %s -> ( G ` ( S + ( _i x. l ) ) ) = ( G ` ( S + ( _i x. %s ) ) ) )' % (V, V))], 'fveq2d', '( l = %s -> %s = %s )' % (V, GL('l'), GL(V)))
    fvv = st_([st_([w.s([], 'eqid', '%s = %s' % (HM, HM))], 'a1i', '%s = %s' % (HM, HM)), w.s([glv2], 'adantl', '( ( %s /\\ l = %s ) -> %s = %s )' % (At, V, GL('l'), GL(V))), vin, glv], 'fvmptd', '( %s ` %s ) = %s' % (HM, V, GL(V)))
    HL = '( ( %s ` %s ) x. ( Q - P ) )' % (HM, V)
    cl = Closure(w, At, {'S': ('RR', Lt(sr)), 'P': ('RR', Lt(pr)), 'Q': ('RR', Lt(qr)), 't': ('RR', tr), '_i': ('CC', st_([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'))})
    for k in ('S', 'P', 'Q', 't', '_i'):
        cl.atom(k)
    ptq = ringeq(w, At, '( %s + ( t x. ( %s - %s ) ) )' % (A_, B_, A_), '( S + ( _i x. %s ) )' % V, cl)
    bma = ringeq(w, At, '( %s - %s )' % (B_, A_), '( _i x. ( Q - P ) )', cl)
    LI = '( ( G ` ( %s + ( t x. ( %s - %s ) ) ) ) x. ( %s - %s ) )' % (A_, B_, A_, B_, A_)
    LI2 = '( ( G ` ( S + ( _i x. %s ) ) ) x. ( _i x. ( Q - P ) ) )' % V
    e1 = st_([st_([st_([ptq], 'fveq2d', '( G ` ( %s + ( t x. ( %s - %s ) ) ) ) = ( G ` ( S + ( _i x. %s ) ) )' % (A_, B_, A_, V)), bma], 'oveq12d', '%s = %s' % (LI, LI2))], 'fveq2d', '( abs ` %s ) = ( abs ` %s )' % (LI, LI2))
    qpc = st_([qpr], 'recnd', '( Q - P ) e. CC')
    icq = st_([st_([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), qpc], 'mulcld', '( _i x. ( Q - P ) ) e. CC')
    e2 = st_([glc, icq, w.inst('absmul')], 'syl2anc', '( abs ` %s ) = ( %s x. ( abs ` ( _i x. ( Q - P ) ) ) )' % (LI2, GL(V)))
    e3 = st_([st_([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), qpc, w.inst('absmul')], 'syl2anc', '( abs ` ( _i x. ( Q - P ) ) ) = ( ( abs ` _i ) x. ( abs ` ( Q - P ) ) )')
    e4 = st_([st_([w.s([], 'absi', '( abs ` _i ) = 1')], 'a1i', '( abs ` _i ) = 1'), st_([qpr, qp0, w.inst('absid')], 'syl2anc', '( abs ` ( Q - P ) ) = ( Q - P )')], 'oveq12d', '( ( abs ` _i ) x. ( abs ` ( Q - P ) ) ) = ( 1 x. ( Q - P ) )')
    e5 = st_([e3, st_([e4, st_([qpc], 'mullidd', '( 1 x. ( Q - P ) ) = ( Q - P )')], 'eqtrd', '( ( abs ` _i ) x. ( abs ` ( Q - P ) ) ) = ( Q - P )')], 'eqtrd', '( abs ` ( _i x. ( Q - P ) ) ) = ( Q - P )')
    e6 = st_([e2, st_([e5], 'oveq2d', '( %s x. ( abs ` ( _i x. ( Q - P ) ) ) ) = ( %s x. ( Q - P ) )' % (GL(V), GL(V)))], 'eqtrd', '( abs ` %s ) = ( %s x. ( Q - P ) )' % (LI2, GL(V)))
    e7 = st_([st_([e1, e6], 'eqtrd', '( abs ` %s ) = ( %s x. ( Q - P ) )' % (LI, GL(V))), st_([fvv], 'oveq1d', '%s = ( %s x. ( Q - P ) )' % (HL, GL(V)))], 'eqtr4d', '( abs ` %s ) = %s' % (LI, HL))
    hlr = st_([st_([fvv, glv], 'eqeltrd', '( %s ` %s ) e. RR' % (HM, V)), qpr], 'remulcld', '%s e. RR' % HL)
    lle = st_([e7, st_([hlr], 'leidd', '%s <_ %s' % (HL, HL))], 'eqbrtrd', '( abs ` %s ) <_ %s' % (LI, HL))
    # integrability of the ( 0 , 1 ) side
    ibA = s([s([s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), s([gc, seg], 'jca', '( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (A_, B_))], 'jca',
               '( ( %s e. CC /\\ %s e. CC ) /\\ ( G e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (A_, B_, A_, B_)), w.inst('lintibl')], 'syl', '( t e. ( 0 (,) 1 ) |-> %s ) e. L^1' % LI)
    lic = st_([st_([e1, e6], 'eqtrd', '( abs ` %s ) = ( %s x. ( Q - P ) )' % (LI, GL(V)))], 'id', 'x') if False else None
    lic = st_([st_([st_([Lt(gc), w.inst('cncff')], 'syl', 'G : D --> CC'), st_([Lt(seg), st_([Lt(ac), Lt(bc), st_([], 'simpr', 't e. ( 0 (,) 1 )') if False else st_([st_([w.s([], 'ioossicc', '( 0 (,) 1 ) C_ ( 0 [,] 1 )')], 'a1i', '( 0 (,) 1 ) C_ ( 0 [,] 1 )'), st_([], 'simpr', 't e. ( 0 (,) 1 )')], 'sseldd', 't e. ( 0 [,] 1 )'), w.inst('cseglin')], 'syl3anc',
                                                                                                                                  '( %s + ( t x. ( %s - %s ) ) ) e. ( %s cseg %s )' % (A_, B_, A_, A_, B_))], 'sseldd', '( %s + ( t x. ( %s - %s ) ) ) e. D' % (A_, B_, A_))], 'ffvelcdmd',
                   '( G ` ( %s + ( t x. ( %s - %s ) ) ) ) e. CC' % (A_, B_, A_)), st_([Lt(bc), Lt(ac)], 'subcld', '( %s - %s ) e. CC' % (B_, A_))], 'mulcld', '%s e. CC' % LI)
    iba = s([lic, ibA], 'iblabs', '( t e. ( 0 (,) 1 ) |-> ( abs ` %s ) ) e. L^1' % LI)
    meq = s([e7], 'mpteq2dva', '( t e. ( 0 (,) 1 ) |-> ( abs ` %s ) ) = ( t e. ( 0 (,) 1 ) |-> %s )' % (LI, HL))
    ibH = s([meq, iba], 'eqeltrrd' if False else 'id', 'x') if False else s([meq, iba], 'eqeltrrd', '( t e. ( 0 (,) 1 ) |-> %s ) e. L^1' % HL)
    lt = s([ac, bc, gc, seg, ibH, hlr, lle], 'lintle', '( abs ` ( G lint <. %s , %s >. ) ) <_ S. ( 0 (,) 1 ) %s _d t' % (A_, B_, HL))
    r1 = s([zf, i1], 'eqtr3d', 'S. ( 0 (,) 1 ) %s _d t = S. %s %s _d u' % (HL, IOO, GL('u')))
    r2 = s([r1, i2], 'eqtrd', 'S. ( 0 (,) 1 ) %s _d t = S. %s %s _d l' % (HL, IOO, GL('l')))
    bnd = s([lt, r2], 'breqtrd', '( abs ` ( G lint <. %s , %s >. ) ) <_ S. %s %s _d l' % (A_, B_, IOO, GL('l')))
    w.qed([ib, bnd], 'jca', S['ef3vle'])
    return run8(w)


AZ, BZ_ = '( abs ` ( Re ` Z ) )', '( abs ` ( Im ` Z ) )'
S['ef3dis'] = ('( ( Z e. CC /\\ ( Re ` Z ) =/= 0 ) -> ( 1 / ( abs ` Z ) ) <_ ( ( 5 / 4 ) x. ( ( %s ^c -u ( 1 / 2 ) ) x. ( ( %s + %s ) ^c -u ( 1 / 2 ) ) ) ) )') % (AZ, BZ_, AZ)


def gen_dis():
    from ef3_f import negcxp
    w = W('ef3dis', 'Lean ` integral_inv_dist_le ` , pointwise part: ` 1 / abs Z <_ ( 5 / 4 ) abs ( Re Z ) ^ ( -1/2 ) ( abs ( Im Z ) + abs ( Re Z ) ) ^ ( -1/2 ) ` (from ` a ^ 2 + b ^ 2 >_ ( 16 / 25 ) a ( a + b ) ` ).')
    A0, G = ante_of(S['ef3dis'])
    s = St(w, A0)
    zc = s([], 'simpl', 'Z e. CC'); rn = s([], 'simpr', '( Re ` Z ) =/= 0')
    rr = s([zc], 'recld', '( Re ` Z ) e. RR'); ir = s([zc], 'imcld', '( Im ` Z ) e. RR')
    ar = s([s([rr], 'recnd', '( Re ` Z ) e. CC')], 'abscld', '%s e. RR' % AZ)
    ap = s([ar, s([s([s([rr], 'recnd', '( Re ` Z ) e. CC'), rn], 'absne0d' if False else 'id', 'x') if False else s([s([rr], 'recnd', '( Re ` Z ) e. CC'), rn], 'absrpcld', '%s e. RR+' % AZ)], 'rpgt0d', '0 < %s' % AZ)], 'elrpd', '%s e. RR+' % AZ)
    br = s([s([ir], 'recnd', '( Im ` Z ) e. CC')], 'abscld', '%s e. RR' % BZ_)
    b0 = s([s([ir], 'recnd', '( Im ` Z ) e. CC')], 'absge0d', '0 <_ %s' % BZ_)
    AB = '( %s + %s )' % (BZ_, AZ)
    abp = s([s([br, ar], 'readdcld', '%s e. RR' % AB), lin8(w, A0, [b0, s([ap], 'rpgt0d', '0 < %s' % AZ)], '0 < %s' % AB, {AZ: ar, BZ_: br})], 'elrpd', '%s e. RR+' % AB)
    sa, sb = '( sqrt ` %s )' % AZ, '( sqrt ` %s )' % AB
    sar = s([ar, s([ap], 'rpge0d', '0 <_ %s' % AZ)], 'resqrtcld', '%s e. RR' % sa)
    sap = s([sar, s([ap], 'sqrtgt0d', '0 < %s' % sa)], 'elrpd', '%s e. RR+' % sa)
    sbr = s([s([abp], 'rpred', '%s e. RR' % AB), s([abp], 'rpge0d', '0 <_ %s' % AB)], 'resqrtcld', '%s e. RR' % sb)
    sbp = s([sbr, s([abp], 'sqrtgt0d', '0 < %s' % sb)], 'elrpd', '%s e. RR+' % sb)
    # ( ( 4 / 5 ) sa sb ) ^ 2 <_ ( abs Z ) ^ 2
    LZ = '( ( 4 / 5 ) x. ( %s x. %s ) )' % (sa, sb)
    lzr = s([numst(w, A0, '( 4 / 5 )', 'RR'), s([sar, sbr], 'remulcld', '( %s x. %s ) e. RR' % (sa, sb))], 'remulcld', '%s e. RR' % LZ)
    zab = s([zc], 'abscld', '( abs ` Z ) e. RR')
    e1 = s([numst(w, A0, '( 4 / 5 )', 'CC'), s([s([sar, sbr], 'remulcld', '( %s x. %s ) e. RR' % (sa, sb))], 'recnd', '( %s x. %s ) e. CC' % (sa, sb))], 'sqmuld', '( %s ^ 2 ) = ( ( ( 4 / 5 ) ^ 2 ) x. ( ( %s x. %s ) ^ 2 ) )' % (LZ, sa, sb))
    e2 = s([s([sar], 'recnd', '%s e. CC' % sa), s([sbr], 'recnd', '%s e. CC' % sb)], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (sa, sb, sa, sb))
    e3 = s([s([ar, s([ap], 'rpge0d', '0 <_ %s' % AZ)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (AZ, AZ)), w.inst('resqrtth')], 'syl', '( %s ^ 2 ) = %s' % (sa, AZ))
    e4 = s([s([s([abp], 'rpred', '%s e. RR' % AB), s([abp], 'rpge0d', '0 <_ %s' % AB)], 'jca', '( %s e. RR /\\ 0 <_ %s )' % (AB, AB)), w.inst('resqrtth')], 'syl', '( %s ^ 2 ) = %s' % (sb, AB))
    e5 = s([e2, s([e3, e4], 'oveq12d', '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) = ( %s x. %s )' % (sa, sb, AZ, AB))], 'eqtrd', '( ( %s x. %s ) ^ 2 ) = ( %s x. %s )' % (sa, sb, AZ, AB))
    e6 = s([e1, s([e5], 'oveq2d', '( ( ( 4 / 5 ) ^ 2 ) x. ( ( %s x. %s ) ^ 2 ) ) = ( ( ( 4 / 5 ) ^ 2 ) x. ( %s x. %s ) )' % (sa, sb, AZ, AB))], 'eqtrd', '( %s ^ 2 ) = ( ( ( 4 / 5 ) ^ 2 ) x. ( %s x. %s ) )' % (LZ, AZ, AB))
    z2 = s([zc, w.inst('absvalsq2')], 'syl', '( ( abs ` Z ) ^ 2 ) = ( ( ( Re ` Z ) ^ 2 ) + ( ( Im ` Z ) ^ 2 ) )')
    ra2 = s([rr, w.inst('absresq')], 'syl', '( %s ^ 2 ) = ( ( Re ` Z ) ^ 2 )' % AZ)
    ib2 = s([ir, w.inst('absresq')], 'syl', '( %s ^ 2 ) = ( ( Im ` Z ) ^ 2 )' % BZ_)
    z3 = s([z2, s([ra2, ib2], 'oveq12d', '( ( %s ^ 2 ) + ( %s ^ 2 ) ) = ( ( ( Re ` Z ) ^ 2 ) + ( ( Im ` Z ) ^ 2 ) )' % (AZ, BZ_))], 'eqtr4d', '( ( abs ` Z ) ^ 2 ) = ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (AZ, BZ_))
    cl = Closure(w, A0, {AZ: ('RR', ar), BZ_: ('RR', br)}); cl.atom(AZ); cl.atom(BZ_)
    sq0 = s([s([br, s([numst(w, A0, '( 8 / ; 2 5 )', 'RR'), ar], 'remulcld', '( ( 8 / ; 2 5 ) x. %s ) e. RR' % AZ)], 'resubcld', '( %s - ( ( 8 / ; 2 5 ) x. %s ) ) e. RR' % (BZ_, AZ))], 'sqge0d', '0 <_ ( ( %s - ( ( 8 / ; 2 5 ) x. %s ) ) ^ 2 )' % (BZ_, AZ))
    a20 = s([ar], 'sqge0d', '0 <_ ( %s ^ 2 )' % AZ)
    ineq = lin.nlinarith(w, A0, [sq0, a20], '( ( ( 4 / 5 ) ^ 2 ) x. ( %s x. %s ) ) <_ ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (AZ, AB, AZ, BZ_), closure=cl)
    sqle = s([s([e6, ineq], 'eqbrtrd', '( %s ^ 2 ) <_ ( ( %s ^ 2 ) + ( %s ^ 2 ) )' % (LZ, AZ, BZ_)), z3], 'breqtrrd', '( %s ^ 2 ) <_ ( ( abs ` Z ) ^ 2 )' % LZ)
    lz0 = s([numst(w, A0, '( 4 / 5 )', 'RR'), s([sar, sbr], 'remulcld', '( %s x. %s ) e. RR' % (sa, sb)), numst(w, A0, '( 4 / 5 )', 'ge0'), s([sar, sbr, s([sap], 'rpge0d', '0 <_ %s' % sa), s([sbp], 'rpge0d', '0 <_ %s' % sb)], 'mulge0d', '0 <_ ( %s x. %s )' % (sa, sb))], 'mulge0d', '0 <_ %s' % LZ)
    le1 = s([sqle, s([lzr, zab, lz0, s([zc], 'absge0d', '0 <_ ( abs ` Z )'), w.inst('id') if False else None], 'le2sqd', '( %s <_ ( abs ` Z ) <-> ( %s ^ 2 ) <_ ( ( abs ` Z ) ^ 2 ) )' % (LZ, LZ)) if False else
               s([lzr, zab, lz0, s([zc], 'absge0d', '0 <_ ( abs ` Z )')], 'le2sqd', '( %s <_ ( abs ` Z ) <-> ( %s ^ 2 ) <_ ( ( abs ` Z ) ^ 2 ) )' % (LZ, LZ))], 'mpbird', '%s <_ ( abs ` Z )' % LZ)
    # 1 / abs Z <_ R  <->  1 <_ ( abs Z ) R
    X_, Y_ = '( 1 / %s )' % sa, '( 1 / %s )' % sb
    na = negcxp(w, A0, AZ, ap); nb = negcxp(w, A0, AB, abp)
    R = '( ( 5 / 4 ) x. ( ( %s ^c -u ( 1 / 2 ) ) x. ( %s ^c -u ( 1 / 2 ) ) ) )' % (AZ, AB)
    R2 = '( ( 5 / 4 ) x. ( %s x. %s ) )' % (X_, Y_)
    req = s([s([na, nb], 'oveq12d', '( ( %s ^c -u ( 1 / 2 ) ) x. ( %s ^c -u ( 1 / 2 ) ) ) = ( %s x. %s )' % (AZ, AB, X_, Y_))], 'oveq2d', '%s = %s' % (R, R2))
    xr = s([sap], 'rpreccld', '%s e. RR+' % X_); yr = s([sbp], 'rpreccld', '%s e. RR+' % Y_)
    r2r = s([numst(w, A0, '( 5 / 4 )', 'RR'), s([s([xr], 'rpred', '%s e. RR' % X_), s([yr], 'rpred', '%s e. RR' % Y_)], 'remulcld', '( %s x. %s ) e. RR' % (X_, Y_))], 'remulcld', '%s e. RR' % R2)
    r20 = s([r2r, lin.linarith(w, A0, [s([xr], 'rpgt0d', '0 < %s' % X_), s([yr], 'rpgt0d', '0 < %s' % Y_)], '0 <_ %s' % R2, closure=Closure(w, A0, {X_: ('RR', s([xr], 'rpred', '%s e. RR' % X_)), Y_: ('RR', s([yr], 'rpred', '%s e. RR' % Y_))}), products=True)], 'id', 'x') if False else \
        lin.linarith(w, A0, [s([xr], 'rpgt0d', '0 < %s' % X_), s([yr], 'rpgt0d', '0 < %s' % Y_)], '0 <_ %s' % R2, closure=Closure(w, A0, {X_: ('RR', s([xr], 'rpred', '%s e. RR' % X_)), Y_: ('RR', s([yr], 'rpred', '%s e. RR' % Y_))}), products=True)
    m1 = s([lzr, zab, r2r, r20, le1], 'lemul1ad', '( %s x. %s ) <_ ( ( abs ` Z ) x. %s )' % (LZ, R2, R2))
    cl2 = Closure(w, A0, {sa: ('RR', sar), sb: ('RR', sbr), X_: ('RR', s([xr], 'rpred', '%s e. RR' % X_)), Y_: ('RR', s([yr], 'rpred', '%s e. RR' % Y_))})
    for k in (sa, sb, X_, Y_):
        cl2.atom(k)
    m2 = ringeq(w, A0, '( %s x. %s )' % (LZ, R2), '( ( %s x. %s ) x. ( %s x. %s ) )' % (sa, X_, sb, Y_), cl2)
    ra = s([s([sar], 'recnd', '%s e. CC' % sa), s([sap], 'rpne0d', '%s =/= 0' % sa)], 'recidd', '( %s x. %s ) = 1' % (sa, X_))
    rb = s([s([sbr], 'recnd', '%s e. CC' % sb), s([sbp], 'rpne0d', '%s =/= 0' % sb)], 'recidd', '( %s x. %s ) = 1' % (sb, Y_))
    m3 = s([m2, s([s([ra, rb], 'oveq12d', '( ( %s x. %s ) x. ( %s x. %s ) ) = ( 1 x. 1 )' % (sa, X_, sb, Y_)), s([w.s([], '1t1e1', '( 1 x. 1 ) = 1')], 'a1i', '( 1 x. 1 ) = 1')], 'eqtrd', '( ( %s x. %s ) x. ( %s x. %s ) ) = 1' % (sa, X_, sb, Y_))], 'eqtrd', '( %s x. %s ) = 1' % (LZ, R2))
    m4 = s([m3, m1], 'eqbrtrrd', '1 <_ ( ( abs ` Z ) x. %s )' % R2)
    zp = s([zab, s([s([zc, s([rn, w.s([w.s([w.s([], 'fveq2', '( Z = 0 -> ( Re ` Z ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( Z = 0 -> ( Re ` Z ) = 0 )')], 'necon3i', '( ( Re ` Z ) =/= 0 -> Z =/= 0 )')], 'syl', 'Z =/= 0')], 'jca', '( Z e. CC /\\ Z =/= 0 )'), w.inst('absgt0')], 'syl', '( Z =/= 0 <-> 0 < ( abs ` Z ) )')], 'id', 'x') if False else None
    zn = s([rn, w.s([w.s([w.s([], 'fveq2', '( Z = 0 -> ( Re ` Z ) = ( Re ` 0 ) )'), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( Z = 0 -> ( Re ` Z ) = 0 )')], 'necon3i', '( ( Re ` Z ) =/= 0 -> Z =/= 0 )')], 'syl', 'Z =/= 0')
    zp = s([zc, zn], 'absrpcld', '( abs ` Z ) e. RR+')
    m5 = s([m4, s([numst(w, A0, '1', 'RR'), r2r, zp], 'ledivmuld', '( ( 1 / ( abs ` Z ) ) <_ %s <-> 1 <_ ( ( abs ` Z ) x. %s ) )' % (R2, R2))], 'mpbird', '( 1 / ( abs ` Z ) ) <_ %s' % R2)
    w.qed([m5, req], 'breqtrrd', S['ef3dis'])
    return run8(w)


LD_ = '( ( ( CC _D F ) ` Z ) / ( F ` Z ) )'
MZ = lambda q='q': '( ( F holord %s ) x. ( 1 / ( abs ` ( Z - %s ) ) ) )' % (q, q)
S['ef3ldb'] = ('( ( ( %s /\\ V e. RR ) /\\ ( Z e. CC /\\ ( abs ` ( Z - %s ) ) <_ ( 3 / 2 ) /\\ ( F ` Z ) =/= 0 ) ) -> ( abs ` %s ) <_ ( ( %s x. ( log ` %s ) ) + sum_ q e. %s %s ) )') % (
    DD(), CT('V'), LD_, KNUM, XA('V'), ZS('F', 'V'), MZ())


def gen_ldb():
    w = W('ef3ldb', 'Lean ` stripInt_norm_le ` ( ` hLL ` ): ` abs ( F \' / F ) ( Z ) <_ 17500000 log X + sum m_q / abs ( Z - q ) ` on the ` 3 / 2 ` -disc about ` 2 + i V ` ( ~ ef2lnd and the triangle inequality).')
    A0, G = ante_of(S['ef3ldb'])
    s = St(w, A0)
    dv = s([], 'simpl', '( %s /\\ V e. RR )' % DD())
    dd, vr = conj_split(w, A0, dv)
    zc, zle, fz = conj_split(w, A0, s([], 'simpr', '( Z e. CC /\\ ( abs ` ( Z - %s ) ) <_ ( 3 / 2 ) /\\ ( F ` Z ) =/= 0 )' % CT('V')))
    lnd = s([s([dv, s([zc, zle, fz], '3jca', '( Z e. CC /\\ ( abs ` ( Z - %s ) ) <_ ( 3 / 2 ) /\\ ( F ` Z ) =/= 0 )' % CT('V'))], 'jca', tsub(ante_of(stmt('ef2lnd'))[0], {'T': 'V', 'S': 'Z'})), w.inst('ef2lnd')], 'syl', tsub(ante_of(stmt('ef2lnd'))[1], {'T': 'V', 'S': 'Z'}))
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    # Z e. HP0
    ct = crfacts(w, A0, '2', 'V', numst(w, A0, '2', 'RR'), vr)
    wz = '( Z - %s )' % CT('V')
    wzc = s([zc, ct[0]], 'subcld', '%s e. CC' % wz)
    rw = s([wzc, w.inst('absrele')], 'syl', '( abs ` ( Re ` %s ) ) <_ ( abs ` %s )' % (wz, wz))
    rwe = s([zc, ct[0]], 'resubd', '( Re ` %s ) = ( ( Re ` Z ) - ( Re ` %s ) )' % (wz, CT('V')))
    rwr = s([wzc], 'recld', '( Re ` %s ) e. RR' % wz)
    lr1 = s([rwr, w.inst('leabs') if False else w.inst('neglem') if False else None], 'id', 'x') if False else None
    nre = s([s([s([rwr], 'renegcld', '-u ( Re ` %s ) e. RR' % wz), w.inst('leabs')], 'syl', '-u ( Re ` %s ) <_ ( abs ` -u ( Re ` %s ) )' % (wz, wz)), s([s([rwr], 'recnd', '( Re ` %s ) e. CC' % wz)], 'absnegd', '( abs ` -u ( Re ` %s ) ) = ( abs ` ( Re ` %s ) )' % (wz, wz))], 'breqtrd', '-u ( Re ` %s ) <_ ( abs ` ( Re ` %s ) )' % (wz, wz))
    lvz = {'( Re ` %s )' % wz: rwr, '( abs ` ( Re ` %s ) )' % wz: s([s([rwr], 'recnd', '( Re ` %s ) e. CC' % wz)], 'abscld', '( abs ` ( Re ` %s ) ) e. RR' % wz), '( abs ` %s )' % wz: s([wzc], 'abscld', '( abs ` %s ) e. RR' % wz),
           '( Re ` Z )': s([zc], 'recld', '( Re ` Z ) e. RR'), '( Re ` %s )' % CT('V'): s([ct[0]], 'recld', '( Re ` %s ) e. RR' % CT('V'))}
    rz = lin8(w, A0, [nre, rw, zle, rwe, ct[1]], '0 < ( Re ` Z )', lvz)
    e2 = s([s([w.s([], '0re', '0 e. RR')], 'a1i', '0 e. RR'), w.inst('elhp2')], 'syl', '( Z e. %s <-> ( Z e. CC /\\ 0 < ( Re ` Z ) ) )' % HP0)
    zh = s([s([zc, rz], 'jca', '( Z e. CC /\\ 0 < ( Re ` Z ) )'), e2], 'mpbird', 'Z e. %s' % HP0)
    fzc = s([s([s([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), zh], 'ffvelcdmd', '( F ` Z ) e. CC')
    dvh = s([hol, w.inst('ef2dvh')], 'syl', HOLF('( CC _D F )', HP0))
    dzc = s([s([s([dvh, w.inst('simpl')], 'syl', '( CC _D F ) e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', '( CC _D F ) : %s --> CC' % HP0), zh], 'ffvelcdmd', '( ( CC _D F ) ` Z ) e. CC')
    ac = s([dzc, fzc, fz], 'divcld', '%s e. CC' % LD_)
    # the zero sum
    Z_ = ZS('F', 'V')
    zs = s([dv, w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': 'V'}))
    zf, zo, _ = conj_split(w, A0, zs)
    Aq = '( %s /\\ q e. %s )' % (A0, Z_)
    sq = St(w, Aq)
    Lq = lambda x: lift(w, x, Aq)
    qin = sq([], 'simpr', 'q e. %s' % Z_)
    z = zs_unpack(w, Aq, 'F', 'V', Lq(vr), 'q', qin)
    on = sq([Lq(zo), qin, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
    qn = sq([sq([Lq(fz), sq([z['fz']], 'eqcomd', '0 = ( F ` q )') if False else None], 'id', 'x') if False else None], 'id', 'x') if False else None
    # Z =/= q because F Z =/= 0 = F q
    zq = sq([sq([Lq(fz), sq([sq([], 'id', 'x') if False else z['fz']], 'id', 'x') if False else z['fz']], 'id', 'x') if False else None], 'id', 'x') if False else None
    fzq = sq([sq([z['fz']], 'eqcomd', '0 = ( F ` q )'), Lq(fz)], 'id', 'x') if False else None
    neq = sq([Lq(fz), sq([sq([], 'id', 'x') if False else None], 'id', 'x') if False else None], 'id', 'x') if False else None
    ne1 = sq([Lq(fz), sq([z['fz']], 'eqcomd', '0 = ( F ` q )')], 'neeqtrd' if False else 'id', 'x') if False else None
    fzne = sq([Lq(fz), z['fz']], 'neeqtrrd', '( F ` Z ) =/= ( F ` q )')
    zneq = sq([fzne, w.s([w.s([], 'fveq2', '( Z = q -> ( F ` Z ) = ( F ` q ) )')], 'necon3i', '( ( F ` Z ) =/= ( F ` q ) -> Z =/= q )')], 'syl', 'Z =/= q')
    dzq = sq([Lq(zc), z['cc']], 'subcld', '( Z - q ) e. CC')
    dq0 = sq([Lq(zc), z['cc'], zneq], 'subne0d', '( Z - q ) =/= 0')
    mc = sq([on], 'nncnd', '( F holord q ) e. CC')
    tc = sq([mc, dzq, dq0], 'divcld', '( ( F holord q ) / ( Z - q ) ) e. CC')
    B_ = 'sum_ q e. %s ( ( F holord q ) / ( Z - q ) )' % Z_
    bc = s([zf, tc], 'fsumcl', '%s e. CC' % B_)
    fa = s([zf, tc], 'fsumabs', '( abs ` %s ) <_ sum_ q e. %s ( abs ` ( ( F holord q ) / ( Z - q ) ) )' % (B_, Z_))
    t1 = sq([mc, dzq, dq0, w.inst('absdiv')], 'syl3anc', '( abs ` ( ( F holord q ) / ( Z - q ) ) ) = ( ( abs ` ( F holord q ) ) / ( abs ` ( Z - q ) ) )')
    t2 = sq([sq([sq([on], 'nnred', '( F holord q ) e. RR'), sq([on], 'nnge0d' if False else 'id', 'x') if False else lin8(w, Aq, [sq([on], 'nnge1d', '1 <_ ( F holord q )')], '0 <_ ( F holord q )', {'( F holord q )': sq([on], 'nnred', '( F holord q ) e. RR')})], 'jca', '( ( F holord q ) e. RR /\\ 0 <_ ( F holord q ) )'), w.inst('absid')], 'syl', '( abs ` ( F holord q ) ) = ( F holord q )')
    adq = sq([dzq], 'abscld', '( abs ` ( Z - q ) ) e. RR')
    t3 = sq([mc, sq([adq], 'recnd', '( abs ` ( Z - q ) ) e. CC'), sq([dzq, dq0], 'absne0d', '( abs ` ( Z - q ) ) =/= 0')], 'divrecd', '( ( F holord q ) / ( abs ` ( Z - q ) ) ) = %s' % MZ())
    t4 = sq([t1, sq([sq([t2], 'oveq1d', '( ( abs ` ( F holord q ) ) / ( abs ` ( Z - q ) ) ) = ( ( F holord q ) / ( abs ` ( Z - q ) ) )'), t3], 'eqtrd', '( ( abs ` ( F holord q ) ) / ( abs ` ( Z - q ) ) ) = %s' % MZ())], 'eqtrd',
            '( abs ` ( ( F holord q ) / ( Z - q ) ) ) = %s' % MZ())
    se = s([t4], 'sumeq2dv', 'sum_ q e. %s ( abs ` ( ( F holord q ) / ( Z - q ) ) ) = sum_ q e. %s %s' % (Z_, Z_, MZ()))
    fb = s([fa, se], 'breqtrd', '( abs ` %s ) <_ sum_ q e. %s %s' % (B_, Z_, MZ()))
    tri = s([s([ac, bc], 'subcld', '( %s - %s ) e. CC' % (LD_, B_)), bc, w.inst('abstri')], 'syl2anc', '( abs ` ( ( %s - %s ) + %s ) ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` %s ) )' % (LD_, B_, B_, LD_, B_, B_))
    npc = s([ac, bc], 'npcand', '( ( %s - %s ) + %s ) = %s' % (LD_, B_, B_, LD_))
    tri2 = s([s([npc], 'fveq2d', '( abs ` ( ( %s - %s ) + %s ) ) = ( abs ` %s )' % (LD_, B_, B_, LD_)), tri], 'eqbrtrrd', '( abs ` %s ) <_ ( ( abs ` ( %s - %s ) ) + ( abs ` %s ) )' % (LD_, LD_, B_, B_))
    xr = s([ar, s([s([vr], 'recnd', 'V e. CC'), w.inst('abscl') if False else None], 'id', 'x') if False else s([s([s([vr], 'recnd', 'V e. CC')], 'abscld', '( abs ` V ) e. RR'), numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` V ) + 2 ) e. RR')], 'remulcld', '%s e. RR' % XA('V'))
    x2 = s([dv, w.inst('ef2x2')], 'syl', '2 <_ %s' % XA('V'))
    xp = s([xr, lin8(w, A0, [x2], '0 < %s' % XA('V'), {XA('V'): xr})], 'elrpd', '%s e. RR+' % XA('V'))
    KLg = '( %s x. ( log ` %s ) )' % (KNUM, XA('V'))
    klr = s([numst(w, A0, KNUM, 'RR'), s([xp], 'relogcld', '( log ` %s ) e. RR' % XA('V'))], 'remulcld', '%s e. RR' % KLg)
    msr = s([zf, sq([sq([on], 'nnred', '( F holord q ) e. RR'), sq([sq([dzq, dq0], 'absrpcld', '( abs ` ( Z - q ) ) e. RR+')], 'rpreccld', '( 1 / ( abs ` ( Z - q ) ) ) e. RR+') if False else sq([sq([sq([dzq, dq0], 'absrpcld', '( abs ` ( Z - q ) ) e. RR+')], 'rpreccld', '( 1 / ( abs ` ( Z - q ) ) ) e. RR+')], 'rpred', '( 1 / ( abs ` ( Z - q ) ) ) e. RR')], 'remulcld', '%s e. RR' % MZ())], 'fsumrecl', 'sum_ q e. %s %s e. RR' % (Z_, MZ()))
    lv = {'( abs ` %s )' % LD_: s([ac], 'abscld', '( abs ` %s ) e. RR' % LD_), '( abs ` ( %s - %s ) )' % (LD_, B_): s([s([ac, bc], 'subcld', '( %s - %s ) e. CC' % (LD_, B_))], 'abscld', '( abs ` ( %s - %s ) ) e. RR' % (LD_, B_)),
          '( abs ` %s )' % B_: s([bc], 'abscld', '( abs ` %s ) e. RR' % B_), KLg: klr, 'sum_ q e. %s %s' % (Z_, MZ()): msr}
    w.qed([lin8(w, A0, [tri2, lnd, fb], '( abs ` %s ) <_ ( %s + sum_ q e. %s %s )' % (LD_, KLg, Z_, MZ()), lv)], 'id', S['ef3ldb']) if False else None
    fin = lin8(w, A0, [tri2, lnd, fb], '( abs ` %s ) <_ ( %s + sum_ q e. %s %s )' % (LD_, KLg, Z_, MZ()), lv)
    w.lines[-1] = w.lines[-1].replace(fin + ':', 'qed:', 1)
    return run8(w)


ZU = '( S + ( _i x. U ) )'
BQ = lambda q='q', U='U', S_='S': '( ( ( abs ` ( %s - ( Im ` %s ) ) ) + ( abs ` ( %s - ( Re ` %s ) ) ) ) ^c -u ( 1 / 2 ) )' % (U, q, S_, q)
PWT = lambda q='q', U='U', S_='S': '( ; 1 5 x. ( %s x. ( %s x. %s ) ) )' % (WQ(q), RS(S_, q), BQ(q, U, S_))
LXV = '( log ` %s )' % XA('V')
GU = lambda U='U': '( 1 / ( 1 + ( abs ` %s ) ) )' % U
PWM = lambda U='U', V='V', S_='S': '( ( Y ^c %s ) x. ( ( ( %s x. ( log ` %s ) ) x. %s ) + sum_ q e. %s %s ) )' % (S_, KLD, XA(V), GU(U), ZS('F', V), PWT('q', U, S_))
S['ef3pw'] = ('( ( ( %s /\\ Y e. RR+ ) /\\ ( ( S e. RR /\\ ( ( 9 / ; 1 6 ) <_ S /\\ S <_ ( 5 / 8 ) ) ) /\\ ( V e. RR /\\ U e. RR ) ) /\\ '
              '( ( abs ` ( U - V ) ) <_ ( 1 / 4 ) /\\ ( F ` %s ) =/= 0 /\\ A. p e. %s ( Re ` p ) =/= S ) ) -> ( abs ` ( %s ` %s ) ) <_ %s )') % (
    DD(), ZU, ZS('F', 'V'), LDI(), ZU, PWM())


def gen_pw():
    from ef3_d import ld0_in
    from ef3_f import zk_facts_v
    w = W('ef3pw', 'Lean ` stripInt_norm_le ` with ` integral_inv_dist_le ` \'s pointwise bound: on the left edge ` S + i U ` near the centre ` V ` , ` abs ( ( F \' / F ) Y ^ z / z ) <_ Y ^ S ( 70000000 log X / ( 1 + abs U ) + sum_q 15 w_q d_q ^ ( -1/2 ) ( abs ( U - Im q ) + d_q ) ^ ( -1/2 ) ) ` , ` d_q = abs ( S - Re q ) ` .')
    A0, G = ante_of(S['ef3pw'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    dd, yp = conj_split(w, A0, s([], 'simp1', H1))
    sb, vu = conj_split(w, A0, s([], 'simp2', H2))
    sr, sbb = conj_split(w, A0, sb); s9, s58 = conj_split(w, A0, sbb)
    vr, ur = conj_split(w, A0, vu)
    uv, fz, alp = conj_split(w, A0, s([], 'simp3', H3))
    hol, ar, a1, allt, nzw = dd_parts(w, A0, dd)
    zc, zre, zim = crfacts(w, A0, 'S', 'U', sr, ur)
    lvb = {'S': sr, 'U': ur, 'V': vr}
    zrp = s([lin8(w, A0, [s9], '0 < S', lvb), zre], 'breqtrrd', '0 < ( Re ` %s )' % ZU)
    zin = ld0_in(w, A0, ZU, zc, zrp, fz)
    # LDI value
    FVB = lambda u: '( ( ( ( CC _D F ) ` %s ) / ( F ` %s ) ) x. ( ( Y ^c %s ) / %s ) )' % (u, u, u, u)
    cg, _ = w.congr(FVB('u'), {'u': ZU}, 'u = %s' % ZU, {'u': w.s([], 'id', '( u = %s -> u = %s )' % (ZU, ZU))})
    As = '( %s /\\ u = %s )' % (A0, ZU)
    cgA = w.s([cg], 'adantl', '( %s -> %s = %s )' % (As, FVB('u'), FVB(ZU)))
    LDZ = '( ( ( CC _D F ) ` %s ) / ( F ` %s ) )' % (ZU, ZU)
    ct = crfacts(w, A0, '2', 'V', numst(w, A0, '2', 'RR'), vr)
    # | z - CT ( V ) | <_ 3 / 2
    wz = '( %s - %s )' % (ZU, CT('V'))
    wzc = s([zc, ct[0]], 'subcld', '%s e. CC' % wz)
    rw = s([s([zc, ct[0]], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (wz, ZU, CT('V'))), s([zre, ct[1]], 'oveq12d', '( ( Re ` %s ) - ( Re ` %s ) ) = ( S - 2 )' % (ZU, CT('V')))], 'eqtrd', '( Re ` %s ) = ( S - 2 )' % wz)
    iw = s([s([zc, ct[0]], 'imsubd', '( Im ` %s ) = ( ( Im ` %s ) - ( Im ` %s ) )' % (wz, ZU, CT('V'))), s([zim, ct[2]], 'oveq12d', '( ( Im ` %s ) - ( Im ` %s ) ) = ( U - V )' % (ZU, CT('V')))], 'eqtrd', '( Im ` %s ) = ( U - V )' % wz)
    w2 = s([wzc, w.inst('absvalsq2')], 'syl', '( ( abs ` %s ) ^ 2 ) = ( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) )' % (wz, wz, wz))
    w3 = s([w2, s([s([rw], 'oveq1d', '( ( Re ` %s ) ^ 2 ) = ( ( S - 2 ) ^ 2 )' % wz), s([iw], 'oveq1d', '( ( Im ` %s ) ^ 2 ) = ( ( U - V ) ^ 2 )' % wz)], 'oveq12d',
                                                     '( ( ( Re ` %s ) ^ 2 ) + ( ( Im ` %s ) ^ 2 ) ) = ( ( ( S - 2 ) ^ 2 ) + ( ( U - V ) ^ 2 ) )' % (wz, wz))], 'eqtrd', '( ( abs ` %s ) ^ 2 ) = ( ( ( S - 2 ) ^ 2 ) + ( ( U - V ) ^ 2 ) )' % wz)
    uvr = s([ur, vr], 'resubcld', '( U - V ) e. RR')
    auv = s([s([uvr], 'recnd', '( U - V ) e. CC')], 'abscld', '( abs ` ( U - V ) ) e. RR')
    uv2 = s([s([uv, s([auv, numst(w, A0, '( 1 / 4 )', 'RR'), s([s([uvr], 'recnd', '( U - V ) e. CC')], 'absge0d', '0 <_ ( abs ` ( U - V ) )'), numst(w, A0, '( 1 / 4 )', 'ge0')], 'le2sqd',
                              '( ( abs ` ( U - V ) ) <_ ( 1 / 4 ) <-> ( ( abs ` ( U - V ) ) ^ 2 ) <_ ( ( 1 / 4 ) ^ 2 ) )')], 'mpbid', '( ( abs ` ( U - V ) ) ^ 2 ) <_ ( ( 1 / 4 ) ^ 2 )'), s([uvr, w.inst('absresq')], 'syl', '( ( abs ` ( U - V ) ) ^ 2 ) = ( ( U - V ) ^ 2 )')], 'eqbrtrrd', '( ( U - V ) ^ 2 ) <_ ( ( 1 / 4 ) ^ 2 )')
    cls = Closure(w, A0, {'S': ('RR', sr), '( ( U - V ) ^ 2 )': ('RR', s([uvr], 'resqcld', '( ( U - V ) ^ 2 ) e. RR'))}); cls.atom('S'); cls.atom('( ( U - V ) ^ 2 )')
    w4 = lin.nlinarith(w, A0, [s9, s58, uv2], '( ( ( S - 2 ) ^ 2 ) + ( ( U - V ) ^ 2 ) ) <_ ( ( 3 / 2 ) ^ 2 )', closure=cls)
    wabs = s([s([s([w3, w4], 'eqbrtrd', '( ( abs ` %s ) ^ 2 ) <_ ( ( 3 / 2 ) ^ 2 )' % wz), s([s([wzc], 'abscld', '( abs ` %s ) e. RR' % wz), numst(w, A0, '( 3 / 2 )', 'RR'), s([wzc], 'absge0d', '0 <_ ( abs ` %s )' % wz), numst(w, A0, '( 3 / 2 )', 'ge0')], 'le2sqd',
                                                                                                                         '( ( abs ` %s ) <_ ( 3 / 2 ) <-> ( ( abs ` %s ) ^ 2 ) <_ ( ( 3 / 2 ) ^ 2 ) )' % (wz, wz))], 'mpbird', '( abs ` %s ) <_ ( 3 / 2 )' % wz)], 'id', 'x') if False else \
        s([s([w3, w4], 'eqbrtrd', '( ( abs ` %s ) ^ 2 ) <_ ( ( 3 / 2 ) ^ 2 )' % wz), s([s([wzc], 'abscld', '( abs ` %s ) e. RR' % wz), numst(w, A0, '( 3 / 2 )', 'RR'), s([wzc], 'absge0d', '0 <_ ( abs ` %s )' % wz), numst(w, A0, '( 3 / 2 )', 'ge0')], 'le2sqd',
                                                                                                                  '( ( abs ` %s ) <_ ( 3 / 2 ) <-> ( ( abs ` %s ) ^ 2 ) <_ ( ( 3 / 2 ) ^ 2 ) )' % (wz, wz))], 'mpbird', '( abs ` %s ) <_ ( 3 / 2 )' % wz)
    ldb = s([s([s([dd, vr], 'jca', '( %s /\\ V e. RR )' % DD()), s([zc, wabs, fz], '3jca', '( %s e. CC /\\ ( abs ` %s ) <_ ( 3 / 2 ) /\\ ( F ` %s ) =/= 0 )' % (ZU, wz, ZU))], 'jca', tsub(ante_of(S['ef3ldb'])[0], {'Z': ZU})), w.inst('ef3ldb')], 'syl',
            tsub(ante_of(S['ef3ldb'])[1], {'Z': ZU}))
    # LDI value
    from ef3_b import ld0_elim
    zh, _ = ld0_elim(w, A0, ZU, zin)
    fzc = s([s([s([hol, w.inst('simpl')], 'syl', 'F e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', 'F : %s --> CC' % HP0), zh], 'ffvelcdmd', '( F ` %s ) e. CC' % ZU)
    dvh = s([hol, w.inst('ef2dvh')], 'syl', HOLF('( CC _D F )', HP0))
    dzc = s([s([s([dvh, w.inst('simpl')], 'syl', '( CC _D F ) e. ( %s -cn-> CC )' % HP0), w.inst('cncff')], 'syl', '( CC _D F ) : %s --> CC' % HP0), zh], 'ffvelcdmd', '( ( CC _D F ) ` %s ) e. CC' % ZU)
    ldc = s([dzc, fzc, fz], 'divcld', '%s e. CC' % LDZ)
    r0 = w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (ZU, ZU)), w.s([], 're0', '( Re ` 0 ) = 0')], 'eqtrdi', '( %s = 0 -> ( Re ` %s ) = 0 )' % (ZU, ZU))
    zn0 = s([s([zrp], 'gt0ne0d', '( Re ` %s ) =/= 0' % ZU), w.s([r0], 'necon3i', '( ( Re ` %s ) =/= 0 -> %s =/= 0 )' % (ZU, ZU))], 'syl', '%s =/= 0' % ZU)
    yzc = s([s([yp], 'rpcnd', 'Y e. CC'), zc], 'cxpcld', '( Y ^c %s ) e. CC' % ZU)
    YZ = '( ( Y ^c %s ) / %s )' % (ZU, ZU)
    yzq = s([yzc, zc, zn0], 'divcld', '%s e. CC' % YZ)
    fv = s([s([w.s([], 'eqid', '%s = %s' % (LDI(), LDI()))], 'a1i', '%s = %s' % (LDI(), LDI())), cgA, zin, s([ldc, yzq], 'mulcld', '%s e. CC' % FVB(ZU))], 'fvmptd', '( %s ` %s ) = %s' % (LDI(), ZU, FVB(ZU)))
    a1_ = s([s([fv], 'fveq2d', '( abs ` ( %s ` %s ) ) = ( abs ` %s )' % (LDI(), ZU, FVB(ZU))), s([ldc, yzq, w.inst('absmul')], 'syl2anc', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (FVB(ZU), LDZ, YZ))], 'eqtrd',
            '( abs ` ( %s ` %s ) ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (LDI(), ZU, LDZ, YZ))
    YS = '( Y ^c S )'
    az = '( abs ` %s )' % ZU
    a2_ = s([yzc, zc, zn0, w.inst('absdiv')], 'syl3anc', '( abs ` %s ) = ( ( abs ` ( Y ^c %s ) ) / %s )' % (YZ, ZU, az))
    a3_ = s([s([yp, zc, w.inst('abscxp')], 'syl2anc', '( abs ` ( Y ^c %s ) ) = ( Y ^c ( Re ` %s ) )' % (ZU, ZU)), s([zre], 'oveq2d', '( Y ^c ( Re ` %s ) ) = %s' % (ZU, YS))], 'eqtrd', '( abs ` ( Y ^c %s ) ) = %s' % (ZU, YS))
    azp = s([zc, zn0], 'absrpcld', '%s e. RR+' % az)
    ysp = s([yp, sr], 'rpcxpcld', '%s e. RR+' % YS)
    a4_ = s([a2_, s([s([a3_], 'oveq1d', '( ( abs ` ( Y ^c %s ) ) / %s ) = ( %s / %s )' % (ZU, az, YS, az)), s([s([ysp], 'rpcnd', '%s e. CC' % YS), s([azp], 'rpcnd', '%s e. CC' % az), s([azp], 'rpne0d', '%s =/= 0' % az)], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (YS, az, YS, az))], 'eqtrd',
                          '( ( abs ` ( Y ^c %s ) ) / %s ) = ( %s x. ( 1 / %s ) )' % (ZU, az, YS, az))], 'eqtrd', '( abs ` %s ) = ( %s x. ( 1 / %s ) )' % (YZ, YS, az))
    # 1 / abs z <_ 4 g
    re1 = s([zc, w.inst('absrele')], 'syl', '( abs ` ( Re ` %s ) ) <_ %s' % (ZU, az))
    re2 = s([s([zre], 'fveq2d', '( abs ` ( Re ` %s ) ) = ( abs ` S )' % ZU), s([sr, lin8(w, A0, [s9], '0 <_ S', lvb), w.inst('absid')], 'syl2anc', '( abs ` S ) = S')], 'eqtrd', '( abs ` ( Re ` %s ) ) = S' % ZU)
    im1 = s([zc, w.inst('absimle')], 'syl', '( abs ` ( Im ` %s ) ) <_ %s' % (ZU, az))
    im2 = s([zim], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` U )' % ZU)
    aU = s([s([ur], 'recnd', 'U e. CC')], 'abscld', '( abs ` U ) e. RR')
    lvz = {'S': sr, az: s([azp], 'rpred', '%s e. RR' % az), '( abs ` U )': aU, '( abs ` ( Re ` %s ) )' % ZU: s([s([s([zc], 'recld', '( Re ` %s ) e. RR' % ZU)], 'recnd', '( Re ` %s ) e. CC' % ZU)], 'abscld', '( abs ` ( Re ` %s ) ) e. RR' % ZU),
           '( abs ` ( Im ` %s ) )' % ZU: s([s([s([zc], 'imcld', '( Im ` %s ) e. RR' % ZU)], 'recnd', '( Im ` %s ) e. CC' % ZU)], 'abscld', '( abs ` ( Im ` %s ) ) e. RR' % ZU)}
    b4 = lin8(w, A0, [re1, re2, im1, im2, s9, s([s([ur], 'recnd', 'U e. CC')], 'absge0d', '0 <_ ( abs ` U )')], '( 1 + ( abs ` U ) ) <_ ( 4 x. %s )' % az, lvz)
    up = s([s([numst(w, A0, '1', 'RR'), aU], 'readdcld', '( 1 + ( abs ` U ) ) e. RR'), lin8(w, A0, [s([s([ur], 'recnd', 'U e. CC')], 'absge0d', '0 <_ ( abs ` U )')], '0 < ( 1 + ( abs ` U ) )', {'( abs ` U )': aU})], 'elrpd', '( 1 + ( abs ` U ) ) e. RR+')
    d1 = s([up, s([numst(w, A0, '4', 'RR+'), azp], 'rpmulcld', '( 4 x. %s ) e. RR+' % az), numst(w, A0, '4', 'RR'), numst(w, A0, '4', 'ge0'), b4], 'lediv2ad', '( 4 / ( 4 x. %s ) ) <_ ( 4 / ( 1 + ( abs ` U ) ) )' % az)
    d2 = s([numst(w, A0, '1', 'CC'), s([azp], 'rpcnd', '%s e. CC' % az), numst(w, A0, '4', 'CC'), s([azp], 'rpne0d', '%s =/= 0' % az), s([numst(w, A0, '4', 'RR+')], 'rpne0d', '4 =/= 0')], 'divcan5d', '( ( 4 x. 1 ) / ( 4 x. %s ) ) = ( 1 / %s )' % (az, az))
    d3 = s([s([s([numst(w, A0, '4', 'CC')], 'mulridd', '( 4 x. 1 ) = 4')], 'oveq1d', '( ( 4 x. 1 ) / ( 4 x. %s ) ) = ( 4 / ( 4 x. %s ) )' % (az, az)), d2], 'eqtr3d', '( 4 / ( 4 x. %s ) ) = ( 1 / %s )' % (az, az))
    G4 = '( 4 x. %s )' % GU()
    d4 = s([numst(w, A0, '4', 'CC'), s([up], 'rpcnd', '( 1 + ( abs ` U ) ) e. CC'), s([up], 'rpne0d', '( 1 + ( abs ` U ) ) =/= 0')], 'divrecd', '( 4 / ( 1 + ( abs ` U ) ) ) = %s' % G4)
    riz = s([s([d3, d1], 'eqbrtrrd', '( 1 / %s ) <_ ( 4 / ( 1 + ( abs ` U ) ) )' % az), d4], 'breqtrd', '( 1 / %s ) <_ %s' % (az, G4))
    riz2 = s([s([azp], 'rpreccld' if False else 'id', 'x')], 'id', 'x') if False else None
    rzr = s([s([azp], 'rpreccld', '( 1 / %s ) e. RR+' % az)], 'rpred', '( 1 / %s ) e. RR' % az)
    gur = s([s([up], 'rpreccld', '%s e. RR+' % GU())], 'rpred', '%s e. RR' % GU())
    g4r = s([numst(w, A0, '4', 'RR'), gur], 'remulcld', '%s e. RR' % G4)
    ysr = s([ysp], 'rpred', '%s e. RR' % YS)
    yb = s([rzr, g4r, ysr, s([ysp], 'rpge0d', '0 <_ %s' % YS), riz], 'lemul2ad', '( %s x. ( 1 / %s ) ) <_ ( %s x. %s )' % (YS, az, YS, G4))
    # T1
    LD1 = '( ( %s x. %s ) + sum_ q e. %s %s )' % (KNUM, LXV, ZS('F', 'V'), MZ().replace('Z', ZU) if False else '( ( F holord q ) x. ( 1 / ( abs ` ( %s - q ) ) ) )' % ZU)
    MZU = '( ( F holord q ) x. ( 1 / ( abs ` ( %s - q ) ) ) )' % ZU
    SM = 'sum_ q e. %s %s' % (ZS('F', 'V'), MZU)
    ydr = s([ysr, rzr], 'remulcld', '( %s x. ( 1 / %s ) ) e. RR' % (YS, az))
    abl = s([ldc], 'abscld', '( abs ` %s ) e. RR' % LDZ)
    # closures of the sums
    Z_ = ZS('F', 'V')
    zs = s([s([dd, vr], 'jca', '( %s /\\ V e. RR )' % DD()), w.inst('ef2zs')], 'syl', tsub(ante_of(stmt('ef2zs'))[1], {'T': 'V'}))
    zf, zo, _ = conj_split(w, A0, zs)
    Aq = '( %s /\\ q e. %s )' % (A0, Z_)
    sq = St(w, Aq)
    Lq = lambda x: lift(w, x, Aq)
    qin = sq([], 'simpr', 'q e. %s' % Z_)
    zk = zk_facts_v(w, Aq, Lq(dd), Lq(vr) if False else Lq(vr), None, qin) if False else None
    z = zs_unpack(w, Aq, 'F', 'V', Lq(vr), 'q', qin)
    on = sq([Lq(zo), qin, w.inst('rspa')], 'syl2anc', '( F holord q ) e. NN')
    mr = sq([on], 'nnred', '( F holord q ) e. RR')
    m0 = lin8(w, Aq, [sq([on], 'nnge1d', '1 <_ ( F holord q )')], '0 <_ ( F holord q )', {'( F holord q )': mr})
    fzne = sq([Lq(fz), z['fz']], 'neeqtrrd', '( F ` %s ) =/= ( F ` q )' % ZU)
    zneq = sq([fzne, w.s([w.s([], 'fveq2', '( %s = q -> ( F ` %s ) = ( F ` q ) )' % (ZU, ZU))], 'necon3i', '( ( F ` %s ) =/= ( F ` q ) -> %s =/= q )' % (ZU, ZU))], 'syl', '%s =/= q' % ZU)
    Zq = '( %s - q )' % ZU
    zqc = sq([Lq(zc), z['cc']], 'subcld', '%s e. CC' % Zq)
    zq0 = sq([Lq(zc), z['cc'], zneq], 'subne0d', '%s =/= 0' % Zq)
    azq = sq([zqc, zq0], 'absrpcld', '( abs ` %s ) e. RR+' % Zq)
    rzq = sq([sq([azq], 'rpreccld', '( 1 / ( abs ` %s ) ) e. RR+' % Zq)], 'rpred', '( 1 / ( abs ` %s ) ) e. RR' % Zq)
    mzr = sq([mr, rzq], 'remulcld', '%s e. RR' % MZU)
    smr = s([zf, mzr], 'fsumrecl', '%s e. RR' % SM)
    X1 = '( ( %s x. %s ) + %s )' % (KNUM, LXV, SM)
    xr_ = s([ar, s([s([s([vr], 'recnd', 'V e. CC')], 'abscld', '( abs ` V ) e. RR'), numst(w, A0, '2', 'RR')], 'readdcld', '( ( abs ` V ) + 2 ) e. RR')], 'remulcld', '%s e. RR' % XA('V'))
    x2 = s([s([dd, vr], 'jca', '( %s /\\ V e. RR )' % DD()), w.inst('ef2x2')], 'syl', '2 <_ %s' % XA('V'))
    lxr = s([s([xr_, lin8(w, A0, [x2], '0 < %s' % XA('V'), {XA('V'): xr_})], 'elrpd', '%s e. RR+' % XA('V'))], 'relogcld', '%s e. RR' % LXV)
    x1r = s([s([numst(w, A0, KNUM, 'RR'), lxr], 'remulcld', '( %s x. %s ) e. RR' % (KNUM, LXV)), smr], 'readdcld', '%s e. RR' % X1)
    t1 = s([abl, x1r, ydr, s([ysr, g4r], 'remulcld', '( %s x. %s ) e. RR' % (YS, G4)), s([ldc], 'absge0d', '0 <_ ( abs ` %s )' % LDZ),
            s([ysr, rzr, s([ysp], 'rpge0d', '0 <_ %s' % YS), s([s([azp], 'rpreccld', '( 1 / %s ) e. RR+' % az)], 'rpge0d', '0 <_ ( 1 / %s )' % az)], 'mulge0d', '0 <_ ( %s x. ( 1 / %s ) )' % (YS, az)), ldb, yb], 'lemul12ad',
           '( ( abs ` %s ) x. ( %s x. ( 1 / %s ) ) ) <_ ( %s x. ( %s x. %s ) )' % (LDZ, YS, az, X1, YS, G4))
    lab = s([a1_, s([a4_], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. ( %s x. ( 1 / %s ) ) )' % (LDZ, YZ, LDZ, YS, az))], 'eqtrd', '( abs ` ( %s ` %s ) ) = ( ( abs ` %s ) x. ( %s x. ( 1 / %s ) ) )' % (LDI(), ZU, LDZ, YS, az))
    t1b = s([lab, t1], 'eqbrtrd', '( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s x. %s ) )' % (LDI(), ZU, X1, YS, G4))
    # T2 : rearrange
    KLL = '( ( %s x. %s ) x. %s )' % (KLD, LXV, GU())
    cl = Closure(w, A0, {LXV: ('RR', lxr), SM: ('RR', smr), YS: ('RR', ysr), GU(): ('RR', gur)})
    for k in (LXV, SM, YS, GU()):
        cl.atom(k)
    t2 = ringeq(w, A0, '( %s x. ( %s x. %s ) )' % (X1, YS, G4), '( %s x. ( %s + ( %s x. %s ) ) )' % (YS, KLL, SM, G4), cl)
    SMG = 'sum_ q e. %s ( %s x. %s )' % (Z_, MZU, G4)
    t3 = s([zf, s([g4r], 'recnd', '%s e. CC' % G4), sq([mzr], 'recnd', '%s e. CC' % MZU)], 'fsummulc1', '( %s x. %s ) = %s' % (SM, G4, SMG))
    # T4 : per zero
    reb = sq([sq([Lq(vr), qin], 'jca', '( V e. RR /\\ q e. %s )' % Z_), w.inst('ef2reb')], 'syl', tsub(ante_of(stmt('ef2reb'))[1], {'P': 'q', 'T': 'V'}))
    rlo, rhi, imb = conj_split(w, Aq, reb)
    qre = sq([z['cc']], 'recld', '( Re ` q ) e. RR'); qim = sq([z['cc']], 'imcld', '( Im ` q ) e. RR')
    eqp = w.s([w.s([], 'fveq2', '( p = q -> ( Re ` p ) = ( Re ` q ) )')], 'neeq1d', '( p = q -> ( ( Re ` p ) =/= S <-> ( Re ` q ) =/= S ) )')
    rne = sq([eqp, Lq(alp), qin], 'rspcdva', '( Re ` q ) =/= S')
    ere = sq([sq([Lq(zc), z['cc']], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` q ) )' % (Zq, ZU)), sq([Lq(zre)], 'oveq1d', '( ( Re ` %s ) - ( Re ` q ) ) = ( S - ( Re ` q ) )' % ZU)], 'eqtrd', '( Re ` %s ) = ( S - ( Re ` q ) )' % Zq)
    eim = sq([sq([Lq(zc), z['cc']], 'imsubd', '( Im ` %s ) = ( ( Im ` %s ) - ( Im ` q ) )' % (Zq, ZU)), sq([Lq(zim)], 'oveq1d', '( ( Im ` %s ) - ( Im ` q ) ) = ( U - ( Im ` q ) )' % ZU)], 'eqtrd', '( Im ` %s ) = ( U - ( Im ` q ) )' % Zq)
    rn0 = sq([sq([sq([Lq(sr)], 'recnd', 'S e. CC'), sq([qre], 'recnd', '( Re ` q ) e. CC'), sq([rne], 'necomd', 'S =/= ( Re ` q )')], 'subne0d', '( S - ( Re ` q ) ) =/= 0'), ere], 'id', 'x') if False else None
    rn0 = sq([ere, sq([sq([Lq(sr)], 'recnd', 'S e. CC'), sq([qre], 'recnd', '( Re ` q ) e. CC'), sq([rne], 'necomd', 'S =/= ( Re ` q )')], 'subne0d', '( S - ( Re ` q ) ) =/= 0')], 'neeqtrrd' if False else 'eqnetrd', '( Re ` %s ) =/= 0' % Zq)
    dis = sq([sq([zqc, rn0], 'jca', '( %s e. CC /\\ ( Re ` %s ) =/= 0 )' % (Zq, Zq)), w.inst('ef3dis')], 'syl', tsub(ante_of(S['ef3dis'])[1], {'Z': Zq}))
    a1q = sq([ere], 'fveq2d', '( abs ` ( Re ` %s ) ) = ( abs ` ( S - ( Re ` q ) ) )' % Zq)
    b1q = sq([eim], 'fveq2d', '( abs ` ( Im ` %s ) ) = ( abs ` ( U - ( Im ` q ) ) )' % Zq)
    c1q = sq([a1q], 'oveq1d', '( ( abs ` ( Re ` %s ) ) ^c -u ( 1 / 2 ) ) = %s' % (Zq, RS('S')))
    c2q = sq([sq([b1q, a1q], 'oveq12d', '( ( abs ` ( Im ` %s ) ) + ( abs ` ( Re ` %s ) ) ) = ( ( abs ` ( U - ( Im ` q ) ) ) + ( abs ` ( S - ( Re ` q ) ) ) )' % (Zq, Zq))], 'oveq1d',
             '( ( ( abs ` ( Im ` %s ) ) + ( abs ` ( Re ` %s ) ) ) ^c -u ( 1 / 2 ) ) = %s' % (Zq, Zq, BQ()))
    DR = '( ( 5 / 4 ) x. ( %s x. %s ) )' % (RS('S'), BQ())
    c3q = sq([sq([c1q, c2q], 'oveq12d', '( ( ( abs ` ( Re ` %s ) ) ^c -u ( 1 / 2 ) ) x. ( ( ( abs ` ( Im ` %s ) ) + ( abs ` ( Re ` %s ) ) ) ^c -u ( 1 / 2 ) ) ) = ( %s x. %s )' % (Zq, Zq, Zq, RS('S'), BQ()))], 'oveq2d',
             '%s = %s' % (tsub(ante_of(S['ef3dis'])[1], {'Z': Zq}).split(' <_ ', 1)[1], DR))
    dis2 = sq([dis, c3q], 'breqtrd', '( 1 / ( abs ` %s ) ) <_ %s' % (Zq, DR))
    # weights
    aim = sq([sq([qim], 'recnd', '( Im ` q ) e. CC')], 'abscld', '( abs ` ( Im ` q ) ) e. RR')
    imv = sq([qim, Lq(vr)], 'resubcld', '( ( Im ` q ) - V ) e. RR')
    ib1 = sq([imb, sq([imv, numst(w, Aq, '( ; 1 3 / 8 )', 'RR')], 'absled', '( ( abs ` ( ( Im ` q ) - V ) ) <_ ( ; 1 3 / 8 ) <-> ( -u ( ; 1 3 / 8 ) <_ ( ( Im ` q ) - V ) /\\ ( ( Im ` q ) - V ) <_ ( ; 1 3 / 8 ) ) )')], 'mpbid',
             '( -u ( ; 1 3 / 8 ) <_ ( ( Im ` q ) - V ) /\\ ( ( Im ` q ) - V ) <_ ( ; 1 3 / 8 ) )')
    ib1a, ib1b = conj_split(w, Aq, ib1)
    ub1 = sq([Lq(uv), sq([Lq(uvr), numst(w, Aq, '( 1 / 4 )', 'RR')], 'absled', '( ( abs ` ( U - V ) ) <_ ( 1 / 4 ) <-> ( -u ( 1 / 4 ) <_ ( U - V ) /\\ ( U - V ) <_ ( 1 / 4 ) ) )')], 'mpbid', '( -u ( 1 / 4 ) <_ ( U - V ) /\\ ( U - V ) <_ ( 1 / 4 ) )')
    ub1a, ub1b = conj_split(w, Aq, ub1)
    lvq = {'( Im ` q )': qim, 'U': Lq(ur), 'V': Lq(vr), '( abs ` ( Im ` q ) )': aim, '( abs ` U )': Lq(aU)}
    iuq = sq([qim, Lq(ur)], 'resubcld', '( ( Im ` q ) - U ) e. RR')
    ab15 = sq([sq([lin8(w, Aq, [ib1a, ub1b], '-u ( ; 1 5 / 8 ) <_ ( ( Im ` q ) - U )', lvq), lin8(w, Aq, [ib1b, ub1a], '( ( Im ` q ) - U ) <_ ( ; 1 5 / 8 )', lvq)], 'jca', '( -u ( ; 1 5 / 8 ) <_ ( ( Im ` q ) - U ) /\\ ( ( Im ` q ) - U ) <_ ( ; 1 5 / 8 ) )'),
               sq([iuq, numst(w, Aq, '( ; 1 5 / 8 )', 'RR')], 'absled', '( ( abs ` ( ( Im ` q ) - U ) ) <_ ( ; 1 5 / 8 ) <-> ( -u ( ; 1 5 / 8 ) <_ ( ( Im ` q ) - U ) /\\ ( ( Im ` q ) - U ) <_ ( ; 1 5 / 8 ) ) )')], 'mpbird', '( abs ` ( ( Im ` q ) - U ) ) <_ ( ; 1 5 / 8 )')
    d2q = sq([sq([qim], 'recnd', '( Im ` q ) e. CC'), sq([Lq(ur)], 'recnd', 'U e. CC')], 'abs2difd', '( ( abs ` ( Im ` q ) ) - ( abs ` U ) ) <_ ( abs ` ( ( Im ` q ) - U ) )')
    lvq['( abs ` ( ( Im ` q ) - U ) )'] = sq([sq([iuq], 'recnd', '( ( Im ` q ) - U ) e. CC')], 'abscld', '( abs ` ( ( Im ` q ) - U ) ) e. RR')
    a3 = lin8(w, Aq, [ab15, d2q, sq([sq([Lq(ur)], 'recnd', 'U e. CC')], 'absge0d', '0 <_ ( abs ` U )')], '( 1 + ( abs ` ( Im ` q ) ) ) <_ ( 3 x. ( 1 + ( abs ` U ) ) )', lvq)
    ap = sq([sq([numst(w, Aq, '1', 'RR'), aim], 'readdcld', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR'), lin8(w, Aq, [sq([sq([qim], 'recnd', '( Im ` q ) e. CC')], 'absge0d', '0 <_ ( abs ` ( Im ` q ) )')], '0 < ( 1 + ( abs ` ( Im ` q ) ) )', lvq)], 'elrpd', '( 1 + ( abs ` ( Im ` q ) ) ) e. RR+')
    a = '( 1 + ( abs ` ( Im ` q ) ) )'
    l12 = sq([ap, sq([numst(w, Aq, '3', 'RR+'), Lq(up)], 'rpmulcld', '( 3 x. ( 1 + ( abs ` U ) ) ) e. RR+'), numst(w, Aq, '; 1 2', 'RR'), numst(w, Aq, '; 1 2', 'ge0'), a3], 'lediv2ad', '( ; 1 2 / ( 3 x. ( 1 + ( abs ` U ) ) ) ) <_ ( ; 1 2 / %s )' % a)
    cl0 = Closure(w, Aq, {})
    e12 = ringeq(w, Aq, '( 3 x. 4 )', '; 1 2', cl0)
    dc = sq([numst(w, Aq, '4', 'CC'), sq([Lq(up)], 'rpcnd', '( 1 + ( abs ` U ) ) e. CC'), numst(w, Aq, '3', 'CC'), sq([Lq(up)], 'rpne0d', '( 1 + ( abs ` U ) ) =/= 0'), sq([numst(w, Aq, '3', 'RR+')], 'rpne0d', '3 =/= 0')], 'divcan5d',
            '( ( 3 x. 4 ) / ( 3 x. ( 1 + ( abs ` U ) ) ) ) = ( 4 / ( 1 + ( abs ` U ) ) )')
    dc2 = sq([sq([e12], 'oveq1d', '( ( 3 x. 4 ) / ( 3 x. ( 1 + ( abs ` U ) ) ) ) = ( ; 1 2 / ( 3 x. ( 1 + ( abs ` U ) ) ) )'), dc], 'eqtr3d', '( ; 1 2 / ( 3 x. ( 1 + ( abs ` U ) ) ) ) = ( 4 / ( 1 + ( abs ` U ) ) )')
    g4le = sq([sq([sq([dc2, Lq(d4)], 'eqtrd', '( ; 1 2 / ( 3 x. ( 1 + ( abs ` U ) ) ) ) = %s' % G4), l12], 'eqbrtrrd', '%s <_ ( ; 1 2 / %s )' % (G4, a))], 'id', 'x') if False else \
        sq([sq([dc2, Lq(d4)], 'eqtrd', '( ; 1 2 / ( 3 x. ( 1 + ( abs ` U ) ) ) ) = %s' % G4), l12], 'eqbrtrrd', '%s <_ ( ; 1 2 / %s )' % (G4, a))
    q12 = sq([Lq(g4r), sq([numst(w, Aq, '; 1 2', 'RR'), ap], 'rerpdivcld', '( ; 1 2 / %s ) e. RR' % a), mr, m0, g4le], 'lemul2ad', '( ( F holord q ) x. %s ) <_ ( ( F holord q ) x. ( ; 1 2 / %s ) )' % (G4, a))
    mc = sq([mr], 'recnd', '( F holord q ) e. CC')
    ac = sq([ap], 'rpcnd', '%s e. CC' % a); an = sq([ap], 'rpne0d', '%s =/= 0' % a)
    e1 = sq([mc, numst(w, Aq, '; 1 2', 'CC'), ac, an], 'divassd', '( ( ( F holord q ) x. ; 1 2 ) / %s ) = ( ( F holord q ) x. ( ; 1 2 / %s ) )' % (a, a))
    e2 = sq([numst(w, Aq, '; 1 2', 'CC'), mc, ac, an], 'divassd', '( ( ; 1 2 x. ( F holord q ) ) / %s ) = ( ; 1 2 x. %s )' % (a, WQ()))
    e3 = sq([sq([mc, numst(w, Aq, '; 1 2', 'CC')], 'mulcomd', '( ( F holord q ) x. ; 1 2 ) = ( ; 1 2 x. ( F holord q ) )')], 'oveq1d', '( ( ( F holord q ) x. ; 1 2 ) / %s ) = ( ( ; 1 2 x. ( F holord q ) ) / %s )' % (a, a))
    e4 = sq([sq([e1], 'eqcomd', '( ( F holord q ) x. ( ; 1 2 / %s ) ) = ( ( ( F holord q ) x. ; 1 2 ) / %s )' % (a, a)), sq([e3, e2], 'eqtrd', '( ( ( F holord q ) x. ; 1 2 ) / %s ) = ( ; 1 2 x. %s )' % (a, WQ()))], 'eqtrd',
            '( ( F holord q ) x. ( ; 1 2 / %s ) ) = ( ; 1 2 x. %s )' % (a, WQ()))
    mw = sq([q12, e4], 'breqtrd', '( ( F holord q ) x. %s ) <_ ( ; 1 2 x. %s )' % (G4, WQ()))
    # real closures of the factors
    wqr = sq([mr, ap], 'rerpdivcld', '%s e. RR' % WQ())
    dq = '( abs ` ( S - ( Re ` q ) ) )'
    sqc = sq([sq([Lq(sr)], 'recnd', 'S e. CC'), sq([qre], 'recnd', '( Re ` q ) e. CC')], 'subcld', '( S - ( Re ` q ) ) e. CC')
    dqp = sq([sqc, sq([sq([Lq(sr)], 'recnd', 'S e. CC'), sq([qre], 'recnd', '( Re ` q ) e. CC'), sq([rne], 'necomd', 'S =/= ( Re ` q )')], 'subne0d', '( S - ( Re ` q ) ) =/= 0')], 'absrpcld', '%s e. RR+' % dq)
    rsr = sq([sq([dqp, sq([numst(w, Aq, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % RS('S'))], 'rpred', '%s e. RR' % RS('S'))
    uq = '( abs ` ( U - ( Im ` q ) ) )'
    uqr = sq([sq([sq([Lq(ur), qim], 'resubcld', '( U - ( Im ` q ) ) e. RR')], 'recnd', '( U - ( Im ` q ) ) e. CC')], 'abscld', '%s e. RR' % uq)
    uq0 = sq([sq([sq([Lq(ur), qim], 'resubcld', '( U - ( Im ` q ) ) e. RR')], 'recnd', '( U - ( Im ` q ) ) e. CC')], 'absge0d', '0 <_ %s' % uq)
    bqp = sq([sq([sq([uqr, sq([dqp], 'rpred', '%s e. RR' % dq)], 'readdcld', '( %s + %s ) e. RR' % (uq, dq)), lin8(w, Aq, [uq0, sq([dqp], 'rpgt0d', '0 < %s' % dq)], '0 < ( %s + %s )' % (uq, dq), {uq: uqr, dq: sq([dqp], 'rpred', '%s e. RR' % dq)})], 'elrpd', '( %s + %s ) e. RR+' % (uq, dq)),
              sq([numst(w, Aq, '( 1 / 2 )', 'RR')], 'renegcld', '-u ( 1 / 2 ) e. RR')], 'rpcxpcld', '%s e. RR+' % BQ())
    bqr = sq([bqp], 'rpred', '%s e. RR' % BQ())
    drr = sq([numst(w, Aq, '( 5 / 4 )', 'RR'), sq([rsr, bqr], 'remulcld', '( %s x. %s ) e. RR' % (RS('S'), BQ()))], 'remulcld', '%s e. RR' % DR)
    mg = sq([mr, Lq(g4r)], 'remulcld', '( ( F holord q ) x. %s ) e. RR' % G4)
    mg0 = sq([mr, Lq(g4r), m0, lin8(w, Aq, [sq([Lq(s([up], 'rpreccld', '%s e. RR+' % GU()))], 'rpgt0d', '0 < %s' % GU())], '0 <_ %s' % G4, {GU(): Lq(gur)})], 'mulge0d', '0 <_ ( ( F holord q ) x. %s )' % G4)
    pr_ = sq([mg, sq([numst(w, Aq, '; 1 2', 'RR'), wqr], 'remulcld', '( ; 1 2 x. %s ) e. RR' % WQ()), rzq, drr, mg0, sq([sq([azq], 'rpreccld', '( 1 / ( abs ` %s ) ) e. RR+' % Zq)], 'rpge0d', '0 <_ ( 1 / ( abs ` %s ) )' % Zq), mw, dis2], 'lemul12ad',
             '( ( ( F holord q ) x. %s ) x. ( 1 / ( abs ` %s ) ) ) <_ ( ( ; 1 2 x. %s ) x. %s )' % (G4, Zq, WQ(), DR))
    clq = Closure(w, Aq, {'( F holord q )': ('RR', mr), GU(): ('RR', Lq(gur)), '( 1 / ( abs ` %s ) )' % Zq: ('RR', rzq), WQ(): ('RR', wqr), RS('S'): ('RR', rsr), BQ(): ('RR', bqr)})
    for k in ('( F holord q )', GU(), '( 1 / ( abs ` %s ) )' % Zq, WQ(), RS('S'), BQ()):
        clq.atom(k)
    r1 = ringeq(w, Aq, '( %s x. %s )' % (MZU, G4), '( ( ( F holord q ) x. %s ) x. ( 1 / ( abs ` %s ) ) )' % (G4, Zq), clq)
    r2 = ringeq(w, Aq, '( ( ; 1 2 x. %s ) x. %s )' % (WQ(), DR), PWT(), clq)
    t4 = sq([sq([r1, pr_], 'eqbrtrd', '( %s x. %s ) <_ ( ( ; 1 2 x. %s ) x. %s )' % (MZU, G4, WQ(), DR)), r2], 'breqtrd', '( %s x. %s ) <_ %s' % (MZU, G4, PWT()))
    ptr = sq([numst(w, Aq, '; 1 5', 'RR'), sq([wqr, sq([rsr, bqr], 'remulcld', '( %s x. %s ) e. RR' % (RS('S'), BQ()))], 'remulcld', '( %s x. ( %s x. %s ) ) e. RR' % (WQ(), RS('S'), BQ()))], 'remulcld', '%s e. RR' % PWT())
    mgr = sq([mzr, Lq(g4r)], 'remulcld', '( %s x. %s ) e. RR' % (MZU, G4))
    t5 = s([zf, mgr, ptr, t4], 'fsumle', '%s <_ sum_ q e. %s %s' % (SMG, Z_, PWT()))
    SPW = 'sum_ q e. %s %s' % (Z_, PWT())
    smgr = s([zf, mgr], 'fsumrecl', '%s e. RR' % SMG)
    spwr = s([zf, ptr], 'fsumrecl', '%s e. RR' % SPW)
    kllr = s([s([numst(w, A0, KLD, 'RR'), lxr], 'remulcld', '( %s x. %s ) e. RR' % (KLD, LXV)), gur], 'remulcld', '%s e. RR' % KLL)
    t6 = s([t5, s([smgr, spwr, kllr], 'leadd2d', '( %s <_ %s <-> ( %s + %s ) <_ ( %s + %s ) )' % (SMG, SPW, KLL, SMG, KLL, SPW))], 'mpbid', '( %s + %s ) <_ ( %s + %s )' % (KLL, SMG, KLL, SPW))
    t7 = s([s([kllr, smgr], 'readdcld', '( %s + %s ) e. RR' % (KLL, SMG)), s([kllr, spwr], 'readdcld', '( %s + %s ) e. RR' % (KLL, SPW)), ysr, s([ysp], 'rpge0d', '0 <_ %s' % YS), t6], 'lemul2ad',
           '( %s x. ( %s + %s ) ) <_ ( %s x. ( %s + %s ) )' % (YS, KLL, SMG, YS, KLL, SPW))
    t8 = s([t2, s([s([t3], 'oveq2d', '( %s + ( %s x. %s ) ) = ( %s + %s )' % (KLL, SM, G4, KLL, SMG))], 'oveq2d', '( %s x. ( %s + ( %s x. %s ) ) ) = ( %s x. ( %s + %s ) )' % (YS, KLL, SM, G4, YS, KLL, SMG))], 'eqtrd',
           '( %s x. ( %s x. %s ) ) = ( %s x. ( %s + %s ) )' % (X1, YS, G4, YS, KLL, SMG))
    t9 = s([t1b, t8], 'breqtrd', '( abs ` ( %s ` %s ) ) <_ ( %s x. ( %s + %s ) )' % (LDI(), ZU, YS, KLL, SMG))
    absr = s([s([s([ldc, yzq], 'mulcld', '%s e. CC' % FVB(ZU)), fv], 'id', 'x')], 'id', 'x') if False else None
    lhsr = s([s([fv, s([ldc, yzq], 'mulcld', '%s e. CC' % FVB(ZU))], 'eqeltrd', '( %s ` %s ) e. CC' % (LDI(), ZU))], 'abscld', '( abs ` ( %s ` %s ) ) e. RR' % (LDI(), ZU))
    w.qed([lhsr, s([ysr, s([kllr, smgr], 'readdcld', '( %s + %s ) e. RR' % (KLL, SMG))], 'remulcld', '( %s x. ( %s + %s ) ) e. RR' % (YS, KLL, SMG)),
           s([ysr, s([kllr, spwr], 'readdcld', '( %s + %s ) e. RR' % (KLL, SPW))], 'remulcld', '( %s x. ( %s + %s ) ) e. RR' % (YS, KLL, SPW)), t9, t7], 'letrd', S['ef3pw'])
    return run8(w)


def inst_all_(w, A, al, var, val, valin, body):
    eq, new = w.wcongr(body, {var: val}, '%s = %s' % (var, val), {var: w.s([], 'id', '( %s = %s -> %s = %s )' % (var, val, var, val))})
    return w.s([eq, al, valin], 'rspcdva', '( %s -> %s )' % (A, new))


if __name__ == '__main__':
    gen_vle()
    gen_dis()
    gen_ldb()
    gen_pw()
