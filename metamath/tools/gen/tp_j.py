"""Sortie TP: Lean exists_window_interpolant, the node values of the Newton interpolant on a rectangle
(tpnode: sum_i b_i prod_(h<i) ( v_J - v_h ) = ( 1 / v_J ) ^ Y inside, 0 outside, b_i the boundary integrals)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift
import cl as _cl
import ef2lib as E
import mvlib
from tp_g import FY, CN0, TPI
from tp_i import FRA, FRP, AP, BQ

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


FR = FRA
INSV = lambda v: E.INS(v, AP, BQ)
X = '( V ` J )'
OMX = lambda i: 'prod_ h e. ( 0 ..^ %s ) ( %s - ( V ` h ) )' % (i, X)
PD = lambda k, d: 'prod_ g e. ( 0 ..^ %s ) ( %s - ( V ` g ) )' % (k, d)
GI = lambda i: '( d e. %s |-> ( ( %s ` d ) / %s ) )' % (FR, FY, PD('( %s + 1 )' % i, 'd'))
BI = lambda i: '( ( %s rectint <. %s , %s >. ) / %s )' % (GI(i), AP, BQ, TPI)
GFI = lambda n: '( d e. %s |-> ( %s x. ( ( %s ` d ) / %s ) ) )' % (FR, OMX(n), FY, PD('( %s + 1 )' % n, 'd'))
GF = '( n e. ( 0 ..^ N ) |-> %s )' % GFI('n')
NODES = 'A. r e. ( 0 ..^ N ) ( -. ( V ` r ) e. %s /\\ ( ( V ` r ) e. ( %s crect %s ) -> %s ) )' % (FR, AP, BQ, INSV('( V ` r )'))
NA = ('( ( ( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ T e. RR ) ) /\\ ( 0 < P /\\ P <_ Q /\\ S <_ T ) ) /\\ '
      '( ( Y e. NN /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC ) /\\ %s ) /\\ J e. ( 0 ..^ N ) )' % NODES)
S['tpnode'] = '( %s -> sum_ i e. ( 0 ..^ N ) ( %s x. %s ) = if ( %s , ( ( 1 / %s ) ^ Y ) , 0 ) )' % (NA, BI('i'), OMX('i'), INSV(X), X)


def gen_node():
    w = W('tpnode', 'Lean ` exists_window_interpolant ` (node values): with ` b_i = ( 1 / 2 pi i ) ` times the boundary integral of '
               '` ( 1 / z ) ^ Y / prod_ ( h <_ i ) ( z - v_h ) ` , the Newton sum ` sum_i b_i prod_ ( h < i ) ( v_J - v_h ) ` is '
               '` ( 1 / v_J ) ^ Y ` for a node strictly inside the rectangle and ` 0 ` for a node outside.')
    A0 = NA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    g1 = s([], 'simp1', '( ( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ T e. RR ) ) /\\ ( 0 < P /\\ P <_ Q /\\ S <_ T ) )')
    g2 = s([], 'simp2', '( ( Y e. NN /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC ) /\\ %s )' % NODES)
    jn = s([], 'simp3', 'J e. ( 0 ..^ N )')
    pqst = s([g1], 'simpld', '( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ T e. RR ) )')
    geo = s([g1], 'simprd', '( 0 < P /\\ P <_ Q /\\ S <_ T )')
    p = s([pqst], 'simplld', 'P e. RR'); q = s([pqst], 'simplrd', 'Q e. RR')
    sS = s([pqst], 'simprld', 'S e. RR'); t = s([pqst], 'simprrd', 'T e. RR')
    ynv = s([g2], 'simpld', '( Y e. NN /\\ N e. NN /\\ V : ( 0 ..^ N ) --> CC )')
    yn = s([ynv], 'simp1d', 'Y e. NN'); nn = s([ynv], 'simp2d', 'N e. NN'); vf = s([ynv], 'simp3d', 'V : ( 0 ..^ N ) --> CC')
    nod = s([g2], 'simprd', NODES)
    c = Closure(w, A0, {'P': ('RR', p), 'Q': ('RR', q), 'S': ('RR', sS), 'T': ('RR', t), 'N': ('NN', nn), 'Y': ('NN', yn)})
    c.have('_i', 'CC', s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'))
    ac = c.mem(AP, 'CC'); bc = c.mem(BQ, 'CC')
    ab = s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (AP, BQ))
    ra = s([p, sS, w.inst('crre')], 'syl2anc', '( Re ` %s ) = P' % AP); ia = s([p, sS, w.inst('crim')], 'syl2anc', '( Im ` %s ) = S' % AP)
    rb = s([q, t, w.inst('crre')], 'syl2anc', '( Re ` %s ) = Q' % BQ); ib = s([q, t, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % BQ)
    p0 = s([geo], 'simp1d', '0 < P'); pq = s([geo], 'simp2d', 'P <_ Q'); st_ = s([geo], 'simp3d', 'S <_ T')
    ra0 = s([p0, ra], 'breqtrrd', '0 < ( Re ` %s )' % AP)
    rab = s([pq, s([ra, rb], 'breq12d', '( ( Re ` %s ) <_ ( Re ` %s ) <-> P <_ Q )' % (AP, BQ))], 'mpbird', '( Re ` %s ) <_ ( Re ` %s )' % (AP, BQ))
    iab = s([st_, s([ia, ib], 'breq12d', '( ( Im ` %s ) <_ ( Im ` %s ) <-> S <_ T )' % (AP, BQ))], 'mpbird', '( Im ` %s ) <_ ( Im ` %s )' % (AP, BQ))
    GEOAB = '( 0 < ( Re ` %s ) /\\ ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (AP, AP, BQ, AP, BQ)
    geoab = s([ra0, rab, iab], '3jca', GEOAB)
    CR = '( %s crect %s )' % (AP, BQ)
    fru = s([ab, s([rab, iab], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (AP, BQ, AP, BQ)), w.inst('crectfru')], 'syl2anc',
            '%s C_ %s' % (FR, CR))
    rh = s([s([ab, ra0], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ 0 < ( Re ` %s ) )' % (AP, BQ, AP)), w.inst('ef2rhp')], 'syl',
           '( %s C_ %s /\\ %s C_ %s )' % (CR, E.HP0, CR, CN0))
    frc = s([fru, s([rh], 'simprd', '%s C_ %s' % (CR, CN0))], 'sstrd', '%s C_ %s' % (FR, CN0))
    frcc = s([frc, s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)], 'sstrd', '%s C_ CC' % FR)
    # nodes: V_q not on the frame, for q e. ( 0 ..^ N )
    def node_q(K, qin, qv):
        """( K -> -. ( V ` qv ) e. FR ) and ( K -> ( ( V ` qv ) e. CR -> INS ) )"""
        idq = w.s([], 'id', '( r = %s -> r = %s )' % (qv, qv))
        body = '( -. ( V ` r ) e. %s /\\ ( ( V ` r ) e. %s -> %s ) )' % (FR, CR, INSV('( V ` r )'))
        cg, nw = w.wcongr(body, {'r': qv}, 'r = %s' % qv, {'r': idq})
        if qv == 'r':
            r = w.s([w.s([_cl.lift(w, nod, K), qin], 'jca', '( %s -> ( %s /\\ r e. ( 0 ..^ N ) ) )' % (K, NODES)), w.inst('rspa')], 'syl', '( %s -> %s )' % (K, nw))
        else:
            r = w.s([qin, _cl.lift(w, nod, K), w.s([cg], 'rspcv', '( %s e. ( 0 ..^ N ) -> ( %s -> %s ) )' % (qv, NODES, nw))], 'sylc', '( %s -> %s )' % (K, nw))
        return w.s([r], 'simpld', '( %s -> -. ( V ` %s ) e. %s )' % (K, qv, FR)), w.s([r], 'simprd', '( %s -> ( ( V ` %s ) e. %s -> %s ) )' % (K, qv, CR, INSV('( V ` %s )' % qv)))
    xnf, xins = node_q(A0, jn, 'J')
    xc = s([vf, jn], 'ffvelcdmd', '%s e. CC' % X)
    c.have(X, 'CC', xc); c.atom(X)
    # every frame point avoids every node
    Ax = '( %s /\\ x e. %s )' % (A0, FR)
    Axq = '( %s /\\ q e. ( 0 ..^ N ) )' % Ax
    xq = w.s([], 'simpr', '( %s -> q e. ( 0 ..^ N ) )' % Axq)
    nf_q, _ = node_q(Axq, xq, 'q')
    xfr = _cl.lift(w, w.s([], 'simpr', '( %s -> x e. %s )' % (Ax, FR)), Axq)
    neq = w.s([xfr, nf_q, w.inst('nelne2')], 'syl2anc', '( %s -> x =/= ( V ` q ) )' % Axq)
    avoid = w.s([w.s([neq], 'ralrimiva', '( %s -> A. q e. ( 0 ..^ N ) x =/= ( V ` q ) )' % Ax)], 'ralrimiva', '( %s -> A. x e. %s A. q e. ( 0 ..^ N ) x =/= ( V ` q ) )' % (A0, FR))
    # the Newton integrands are continuous on the frame
    nn0 = c.mem('N', 'NN0')
    nv = s([nn0, vf], 'jca', '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )')
    def gcn(K, k, C, kss):
        """( K -> ( d e. FR |-> ( C x. ( ( FY ` d ) / PD(k) ) ) ) e. ( FR -cn-> CC ) )"""
        # tpgcn quantifies A. x e. E A. q e. K x =/= ( V ` q ) over K = ( 0 ..^ k ) C_ ( 0 ..^ N )
        Kx = '( %s /\\ x e. %s )' % (K, FR)
        Kxq = '( %s /\\ q e. ( 0 ..^ %s ) )' % (Kx, k)
        qN = w.s([_cl.lift(w, kss, Kxq), w.s([], 'simpr', '( %s -> q e. ( 0 ..^ %s ) )' % (Kxq, k))], 'sseldd', '( %s -> q e. ( 0 ..^ N ) )' % Kxq)
        allx = _cl.lift(w, avoid, K)
        axq = w.s([w.s([_cl.lift(w, allx, Kx), w.s([], 'simpr', '( %s -> x e. %s )' % (Kx, FR))], 'jca',
                       '( %s -> ( A. x e. %s A. q e. ( 0 ..^ N ) x =/= ( V ` q ) /\\ x e. %s ) )' % (Kx, FR, FR)), w.inst('rspa')], 'syl',
                  '( %s -> A. q e. ( 0 ..^ N ) x =/= ( V ` q ) )' % Kx)
        one = w.s([w.s([_cl.lift(w, axq, Kxq), qN], 'jca', '( %s -> ( A. q e. ( 0 ..^ N ) x =/= ( V ` q ) /\\ q e. ( 0 ..^ N ) ) )' % Kxq), w.inst('rspa')], 'syl',
                  '( %s -> x =/= ( V ` q ) )' % Kxq)
        al = w.s([w.s([one], 'ralrimiva', '( %s -> A. q e. ( 0 ..^ %s ) x =/= ( V ` q ) )' % (Kx, k))], 'ralrimiva',
                 '( %s -> A. x e. %s A. q e. ( 0 ..^ %s ) x =/= ( V ` q ) )' % (K, FR, k))
        ga, gc_ = ante_of(tsub(S['tpgcn'], {'K': '( 0 ..^ %s )' % k, 'E': FR, 'C': C}))
        have = {'Y e. NN': _cl.lift(w, yn, K), 'C e. CC'.replace('C', C): None, '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )': _cl.lift(w, nv, K),
                '( 0 ..^ %s ) C_ ( 0 ..^ N )' % k: kss, '%s C_ %s' % (FR, CN0): _cl.lift(w, frc, K), body_of(w, al): al}
        return have, ga, gc_
    # per-i facts: context Ai
    Ai = '( %s /\\ i e. ( 0 ..^ N ) )' % A0
    ci = Closure(w, Ai, {'N': ('NN', _cl.lift(w, nn, Ai)), X: ('CC', _cl.lift(w, xc, Ai))}); ci.atom(X)
    iin = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Ai)
    ci.have('i', 'NN0', w.s([iin, w.inst('elfzonn0')], 'syl', '( %s -> i e. NN0 )' % Ai))
    i1ss = w.s([w.s([w.s([iin, w.inst('fzofzp1')], 'syl', '( %s -> ( i + 1 ) e. ( 0 ... N ) )' % Ai), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` ( i + 1 ) ) )' % Ai),
                w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ ( i + 1 ) ) C_ ( 0 ..^ N ) )' % Ai)
    iss = w.s([w.s([w.s([iin, w.inst('elfzofz')], 'syl', '( %s -> i e. ( 0 ... N ) )' % Ai), w.inst('elfzuz3')], 'syl', '( %s -> N e. ( ZZ>= ` i ) )' % Ai),
               w.inst('fzoss2')], 'syl', '( %s -> ( 0 ..^ i ) C_ ( 0 ..^ N ) )' % Ai)
    # OMX(i) e. CC
    Aih = '( %s /\\ h e. ( 0 ..^ i ) )' % Ai
    vhi = w.s([_cl.lift(w, vf, Aih), w.s([_cl.lift(w, iss, Aih), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ i ) )' % Aih)], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % Aih)],
              'ffvelcdmd', '( %s -> ( V ` h ) e. CC )' % Aih)
    chi = Closure(w, Aih, {X: ('CC', _cl.lift(w, xc, Aih)), '( V ` h )': ('CC', vhi)}); chi.atom(X); chi.atom('( V ` h )')
    omc = w.s([w.s([w.s([], 'fzofi', '( 0 ..^ i ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ i ) e. Fin )' % Ai), chi.mem('( %s - ( V ` h ) )' % X, 'CC')], 'fprodcl',
              '( %s -> %s e. CC )' % (Ai, OMX('i')))
    ci.have(OMX('i'), 'CC', omc); ci.atom(OMX('i'))
    # G_i and ( GF ` i ) continuous
    h1, ga1, gc1 = gcn(Ai, '( i + 1 )', '1', i1ss)
    h1['1 e. CC'] = w.s([], '1cnd', '( %s -> 1 e. CC )' % Ai)
    g1cn = w.s([conj(w, Ai, ga1, h1), w.inst('tpgcn')], 'syl', '( %s -> %s )' % (Ai, gc1))
    # ( d |-> ( 1 x. ... ) ) = GI(i)
    Aid = '( %s /\\ d e. %s )' % (Ai, FR)
    dfr = w.s([], 'simpr', '( %s -> d e. %s )' % (Aid, FR))
    cd = Closure(w, Aid, {})
    dcn = w.s([_cl.lift(w, frc, Aid), dfr], 'sseldd', '( %s -> d e. %s )' % (Aid, CN0))
    fyh = w.s([_cl.lift(w, yn, Aid), w.inst('tpfh')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (Aid, FY, CN0, CN0, FY))
    fyf = w.s([w.s([fyh], 'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Aid, FY, CN0)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (Aid, FY, CN0))
    fyv = w.s([fyf, dcn], 'ffvelcdmd', '( %s -> ( %s ` d ) e. CC )' % (Aid, FY))
    cd.have('( %s ` d )' % FY, 'CC', fyv); cd.atom('( %s ` d )' % FY)
    # PD( i + 1 , d ) complex, nonzero
    Aidh = '( %s /\\ g e. ( 0 ..^ ( i + 1 ) ) )' % Aid
    hN = w.s([_cl.lift(w, i1ss, Aidh), w.s([], 'simpr', '( %s -> g e. ( 0 ..^ ( i + 1 ) ) )' % Aidh)], 'sseldd', '( %s -> g e. ( 0 ..^ N ) )' % Aidh)
    vdh = w.s([_cl.lift(w, vf, Aidh), hN], 'ffvelcdmd', '( %s -> ( V ` g ) e. CC )' % Aidh)
    dc_ = w.s([_cl.lift(w, frcc, Aid), dfr], 'sseldd', '( %s -> d e. CC )' % Aid)
    cdh = Closure(w, Aidh, {'d': ('CC', _cl.lift(w, dc_, Aidh)), '( V ` g )': ('CC', vdh)}); cdh.atom('( V ` g )')
    idqh = w.s([], 'id', '( q = g -> q = g )')
    cgqh, nqh = w.wcongr('d =/= ( V ` q )', {'q': 'g'}, 'q = g', {'q': idqh})
    idxd = w.s([], 'id', '( x = d -> x = d )')
    cgxd, nxd = w.wcongr('A. q e. ( 0 ..^ N ) x =/= ( V ` q )', {'x': 'd'}, 'x = d', {'x': idxd})
    ad = w.s([dfr, _cl.lift(w, avoid, Aid), w.s([cgxd], 'rspcv', '( d e. %s -> ( A. x e. %s A. q e. ( 0 ..^ N ) x =/= ( V ` q ) -> %s ) )' % (FR, FR, nxd))], 'sylc', '( %s -> %s )' % (Aid, nxd))
    dvh = w.s([hN, _cl.lift(w, ad, Aidh), w.s([cgqh], 'rspcv', '( g e. ( 0 ..^ N ) -> ( %s -> %s ) )' % (nxd, nqh))], 'sylc', '( %s -> %s )' % (Aidh, nqh))
    cdh.have('( d - ( V ` g ) )', 'ne0', ap(w, Aidh, 'subne0d', '( d - ( V ` g ) ) =/= 0', cdh, facts=[dvh]))
    fz1 = w.s([w.s([], 'fzofi', '( 0 ..^ ( i + 1 ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( i + 1 ) ) e. Fin )' % Aid)
    pdc = w.s([fz1, cdh.mem('( d - ( V ` g ) )', 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (Aid, PD('( i + 1 )', 'd')))
    pdn = w.s([fz1, cdh.mem('( d - ( V ` g ) )', 'CC'), cdh.ne0('( d - ( V ` g ) )')], 'fprodn0', '( %s -> %s =/= 0 )' % (Aid, PD('( i + 1 )', 'd')))
    cd.have(PD('( i + 1 )', 'd'), 'CC', pdc); cd.have(PD('( i + 1 )', 'd'), 'ne0', pdn); cd.atom(PD('( i + 1 )', 'd'))
    Q1 = '( ( %s ` d ) / %s )' % (FY, PD('( i + 1 )', 'd'))
    m1 = ap(w, Aid, 'mullidd', '( 1 x. %s ) = %s' % (Q1, Q1), cd)
    meq = w.s([m1], 'mpteq2dva', '( %s -> ( d e. %s |-> ( 1 x. %s ) ) = %s )' % (Ai, FR, Q1, GI('i')))
    gicn = w.s([meq, g1cn], 'eqeltrrd', '( %s -> %s e. ( %s -cn-> CC ) )' % (Ai, GI('i'), FR))
    # ( GF ` i ) = GFI(i)
    idni = w.s([], 'id', '( n = i -> n = i )')
    cgni, nni = w.congr(GFI('n'), {'n': 'i'}, 'n = i', {'n': idni})
    assert nni == GFI('i'), nni
    frex = s([s([w.s([], 'cnex', 'CC e. _V')], 'a1i', 'CC e. _V'), frcc], 'ssexd', '%s e. _V' % FR)
    gfie = w.s([_cl.lift(w, frex, Ai), w.inst('mptexg')], 'syl', '( %s -> %s e. _V )' % (Ai, GFI('i')))
    gfv = w.s([w.s([], 'eqidd', '( %s -> %s = %s )' % (Ai, GF, GF)), w.s([cgni], 'adantl', '( ( %s /\\ n = i ) -> %s = %s )' % (Ai, GFI('n'), GFI('i'))), iin, gfie],
              'fvmptd', '( %s -> ( %s ` i ) = %s )' % (Ai, GF, GFI('i')))
    h2, ga2, gc2 = gcn(Ai, '( i + 1 )', OMX('i'), i1ss)
    h2['%s e. CC' % OMX('i')] = omc
    gfcn0 = w.s([conj(w, Ai, ga2, h2), w.inst('tpgcn')], 'syl', '( %s -> %s )' % (Ai, gc2))
    gfcn = w.s([gfv, gfcn0], 'eqeltrd', '( %s -> ( %s ` i ) e. ( %s -cn-> CC ) )' % (Ai, GF, FR))
    # ( GF ` i ) rectint = OMX(i) x. ( GI(i) rectint )
    IG = lambda i: '( %s rectint <. %s , %s >. )' % (GI(i), AP, BQ)
    Aiu = '( %s /\\ x e. %s )' % (Ai, FR)
    xfr2 = w.s([], 'simpr', '( %s -> x e. %s )' % (Aiu, FR))
    from z4blib import fvmd
    Q1x = '( ( %s ` x ) / %s )' % (FY, PD('( i + 1 )', 'x'))
    cx = Closure(w, Aiu, {})
    # values at x: ( ( GF ` i ) ` x ) = OMX(i) x. Q1x ; ( GI(i) ` x ) = Q1x
    fyx = w.s([w.s([w.s([w.s([_cl.lift(w, yn, Aiu), w.inst('tpfh')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (Aiu, FY, CN0, CN0, FY))],
                         'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Aiu, FY, CN0)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (Aiu, FY, CN0)),
               w.s([_cl.lift(w, frc, Aiu), xfr2], 'sseldd', '( %s -> x e. %s )' % (Aiu, CN0))], 'ffvelcdmd', '( %s -> ( %s ` x ) e. CC )' % (Aiu, FY))
    exq = w.s([], 'ovexd', '( %s -> %s e. _V )' % (Aiu, Q1x))
    v1 = fvmd(w, Aiu, 'd', FR, '( ( %s ` d ) / %s )' % (FY, PD('( i + 1 )', 'd')), 'x', xfr2, exq)
    v2a = w.s([gfv], 'fveq1d', '( %s -> ( ( %s ` i ) ` x ) = ( %s ` x ) )' % (Ai, GF, GFI('i')))
    v2b = fvmd(w, Aiu, 'd', FR, '( %s x. ( ( %s ` d ) / %s ) )' % (OMX('i'), FY, PD('( i + 1 )', 'd')), 'x', xfr2,
               w.s([], 'ovexd', '( %s -> ( %s x. %s ) e. _V )' % (Aiu, OMX('i'), Q1x)))
    v2 = w.s([_cl.lift(w, v2a, Aiu), v2b], 'eqtrd', '( %s -> ( ( %s ` i ) ` x ) = ( %s x. %s ) )' % (Aiu, GF, OMX('i'), Q1x))
    v12 = w.s([v2, w.s([v1], 'oveq2d', '( %s -> ( %s x. ( %s ` x ) ) = ( %s x. %s ) )' % (Aiu, OMX('i'), GI('i'), OMX('i'), Q1x))], 'eqtr4d',
              '( %s -> ( ( %s ` i ) ` x ) = ( %s x. ( %s ` x ) ) )' % (Aiu, GF, OMX('i'), GI('i')))
    allv = w.s([v12], 'ralrimiva', '( %s -> A. x e. %s ( ( %s ` i ) ` x ) = ( %s x. ( %s ` x ) ) )' % (Ai, FR, GF, OMX('i'), GI('i')))
    MC = tsub(S['tpmulc'], {'A': AP, 'B': BQ, 'E': FR, 'G': GI('i'), 'C': OMX('i'), 'F': '( %s ` i )' % GF, 'V': '_V'})
    ma, mc_ = ante_of(MC)
    have = {'( %s e. CC /\\ %s e. CC )' % (AP, BQ): _cl.lift(w, ab, Ai), '%s C_ %s' % (FR, FR): w.s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '( %s -> %s C_ %s )' % (Ai, FR, FR)),
            '%s e. ( %s -cn-> CC )' % (GI('i'), FR): gicn, '%s e. CC' % OMX('i'): omc,
            '( %s ` i ) e. _V' % GF: w.s([w.s([], 'fvex', '( %s ` i ) e. _V' % GF)], 'a1i', '( %s -> ( %s ` i ) e. _V )' % (Ai, GF)), body_of(w, allv): allv}
    mul = w.s([conj(w, Ai, ma, have), w.inst('tpmulc')], 'syl', '( %s -> %s )' % (Ai, mc_))
    # ---- the theorem's sum: sum_i BI(i) OMX(i) = ( sum_i ( GF ` i ) rectint ) / TPI
    tpi_c = s([s([], '2cnd', '2 e. CC'), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC')],
              'mulcld', '%s e. CC' % TPI)
    tpi_n = s([s([], '2cnd', '2 e. CC'), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC')], 'mulcld', '( _i x. _pi ) e. CC'),
               s([w.s([], '2ne0', '2 =/= 0')], 'a1i', '2 =/= 0'),
               s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([w.s([], 'picn', '_pi e. CC')], 'a1i', '_pi e. CC'),
                  s([w.s([], 'ine0', '_i =/= 0')], 'a1i', '_i =/= 0'), s([w.s([], 'pine0', '_pi =/= 0')], 'a1i', '_pi =/= 0')], 'mulne0d', '( _i x. _pi ) =/= 0')],
              'mulne0d', '%s =/= 0' % TPI)
    c.have(TPI, 'CC', tpi_c); c.have(TPI, 'ne0', tpi_n); c.atom(TPI)
    ci.have(TPI, 'CC', _cl.lift(w, tpi_c, Ai)); ci.have(TPI, 'ne0', _cl.lift(w, tpi_n, Ai)); ci.atom(TPI)
    IGc = w.s([_cl.lift(w, ab, Ai), w.s([gicn, w.s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '( %s -> %s C_ %s )' % (Ai, FR, FR))], 'jca',
                                          '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (Ai, GI('i'), FR, FR, FR)), w.inst('rectintcle')], 'syl2anc',
              '( %s -> %s e. CC )' % (Ai, IG('i')))
    ci.have(IG('i'), 'CC', IGc); ci.atom(IG('i'))
    IF_ = '( ( %s ` i ) rectint <. %s , %s >. )' % (GF, AP, BQ)
    t1 = ap(w, Ai, 'mulcomd', '( %s x. %s ) = ( %s x. %s )' % (BI('i'), OMX('i'), OMX('i'), BI('i')), ci)
    t2 = ap(w, Ai, 'divassd', '( ( %s x. %s ) / %s ) = ( %s x. %s )' % (OMX('i'), IG('i'), TPI, OMX('i'), BI('i')), ci)
    t3 = w.s([mul], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s x. %s ) / %s ) )' % (Ai, IF_, TPI, OMX('i'), IG('i'), TPI))
    term = w.s([w.s([t1, t2], 'eqtr4d', '( %s -> ( %s x. %s ) = ( ( %s x. %s ) / %s ) )' % (Ai, BI('i'), OMX('i'), OMX('i'), IG('i'), TPI)), t3], 'eqtr4d',
               '( %s -> ( %s x. %s ) = ( %s / %s ) )' % (Ai, BI('i'), OMX('i'), IF_, TPI))
    LHS = 'sum_ i e. ( 0 ..^ N ) ( %s x. %s )' % (BI('i'), OMX('i'))
    SIF = 'sum_ i e. ( 0 ..^ N ) %s' % IF_
    fzN = s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    ifc = w.s([_cl.lift(w, ab, Ai), w.s([gfcn, w.s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '( %s -> %s C_ %s )' % (Ai, FR, FR))], 'jca',
                                          '( %s -> ( ( %s ` i ) e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (Ai, GF, FR, FR, FR)), w.inst('rectintcle')], 'syl2anc',
              '( %s -> %s e. CC )' % (Ai, IF_))
    l1 = s([term], 'sumeq2dv', '%s = sum_ i e. ( 0 ..^ N ) ( %s / %s )' % (LHS, IF_, TPI))
    l2 = s([fzN, tpi_c, ifc, tpi_n], 'fsumdivc', '( %s / %s ) = sum_ i e. ( 0 ..^ N ) ( %s / %s )' % (SIF, TPI, IF_, TPI))
    lhs = s([l1, l2], 'eqtr4d', '%s = ( %s / %s )' % (LHS, SIF, TPI))
    # ---- ef2rsum: SIF = rectint of the pointwise sum
    Aj = '( %s /\\ j e. ( 0 ..^ N ) )' % A0
    idij = w.s([], 'id', '( i = j -> i = j )')
    cgij, nij = w.wcongr('( %s ` i ) e. ( %s -cn-> CC )' % (GF, FR), {'i': 'j'}, 'i = j', {'i': idij})
    allcn = s([w.s([gfcn], 'ralrimiva', '( %s -> A. i e. ( 0 ..^ N ) ( %s ` i ) e. ( %s -cn-> CC ) )' % (A0, GF, FR)),
               w.s([cgij], 'cbvralvw', '( A. i e. ( 0 ..^ N ) ( %s ` i ) e. ( %s -cn-> CC ) <-> A. j e. ( 0 ..^ N ) %s )' % (GF, FR, nij))], 'sylib',
              'A. j e. ( 0 ..^ N ) %s' % nij)
    fe = s([pqst, w.inst('tpfrm')], 'syl', '%s = %s' % (FR, FRP))
    fpe = s([s([fe], 'eqcomd', '%s = %s' % (FRP, FR))], 'eqimssd', '%s C_ %s' % (FRP, FR))
    RS = tsub(stmt('ef2rsum'), {'R': 'T', 'K': '( 0 ..^ N )', 'D': FR, 'G': GF, 'k': 'i'})
    rsa, rsc = ante_of(RS)
    have = {'( P e. RR /\\ Q e. RR )': s([pqst], 'simpld', '( P e. RR /\\ Q e. RR )'), '( S e. RR /\\ T e. RR )': s([pqst], 'simprd', '( S e. RR /\\ T e. RR )'),
            '( 0 ..^ N ) e. Fin': fzN, '%s C_ CC' % FR: frcc, body_of(w, allcn): allcn, '%s C_ %s' % (FRP, FR): fpe}
    rsum = s([conj(w, A0, rsa, have), w.inst('ef2rsum')], 'syl', rsc)
    SUMF = '( b e. %s |-> sum_ i e. ( 0 ..^ N ) ( ( %s ` i ) ` b ) )' % (FR, GF)
    # ---- the pointwise sum on the frame is ( 1 / d ) ^ Y / ( d - X )
    TM = '( d e. %s |-> ( 1 x. ( ( %s ` d ) / ( d - %s ) ) ) )' % (FR, FY, X)
    Au = '( %s /\\ u e. %s )' % (A0, FR)
    ufr = w.s([], 'simpr', '( %s -> u e. %s )' % (Au, FR))
    uc = w.s([_cl.lift(w, frcc, Au), ufr], 'sseldd', '( %s -> u e. CC )' % Au)
    ucn = w.s([_cl.lift(w, frc, Au), ufr], 'sseldd', '( %s -> u e. %s )' % (Au, CN0))
    fyu = w.s([w.s([w.s([w.s([_cl.lift(w, yn, Au), w.inst('tpfh')], 'syl', '( %s -> ( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (Au, FY, CN0, CN0, FY))],
                         'simpld', '( %s -> %s e. ( %s -cn-> CC ) )' % (Au, FY, CN0)), w.inst('cncff')], 'syl', '( %s -> %s : %s --> CC )' % (Au, FY, CN0)), ucn],
              'ffvelcdmd', '( %s -> ( %s ` u ) e. CC )' % (Au, FY))
    FU = '( %s ` u )' % FY
    cu = Closure(w, Au, {'u': ('CC', uc), X: ('CC', _cl.lift(w, xc, Au)), FU: ('CC', fyu)}); cu.atom(X); cu.atom(FU)
    # u =/= X, u avoids all nodes
    une = w.s([ufr, _cl.lift(w, xnf, Au), w.inst('nelne2')], 'syl2anc', '( %s -> u =/= %s )' % (Au, X))
    idxu = w.s([], 'id', '( x = u -> x = u )')
    cgxu, nxu = w.wcongr('A. q e. ( 0 ..^ N ) x =/= ( V ` q )', {'x': 'u'}, 'x = u', {'x': idxu})
    au = w.s([ufr, _cl.lift(w, avoid, Au), w.s([cgxu], 'rspcv', '( u e. %s -> ( A. x e. %s A. q e. ( 0 ..^ N ) x =/= ( V ` q ) -> %s ) )' % (FR, FR, nxu))], 'sylc',
             '( %s -> %s )' % (Au, nxu))
    idqy = w.s([], 'id', '( q = y -> q = y )')
    cgqy, nqy = w.wcongr('u =/= ( V ` q )', {'q': 'y'}, 'q = y', {'q': idqy})
    auy = w.s([au, w.s([cgqy], 'cbvralvw', '( %s <-> A. y e. ( 0 ..^ N ) %s )' % (nxu, nqy))], 'sylib', '( %s -> A. y e. ( 0 ..^ N ) %s )' % (Au, nqy))
    tel = w.s([w.s([_cl.lift(w, nv, Au), w.s([_cl.lift(w, xc, Au), uc, une], '3jca', '( %s -> ( %s e. CC /\\ u e. CC /\\ u =/= %s ) )' % (Au, X, X)), auy],
                  '3jca', '( %s -> ( ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ ( %s e. CC /\\ u e. CC /\\ u =/= %s ) /\\ A. y e. ( 0 ..^ N ) %s ) )' % (Au, X, X, nqy)),
               w.inst('tptel')], 'syl',
              '( %s -> sum_ i e. ( 0 ..^ N ) ( %s / %s ) = ( ( 1 - ( %s / %s ) ) / ( u - %s ) ) )' % (Au, OMX('i'), PD('( i + 1 )', 'u'), OMX('N'), PD('N', 'u'), X))
    # ---- products at u over ( 0 ..^ k ), k <_ N
    def pdfacts(K, dv, k, kss, av):
        Kh = '( %s /\\ g e. ( 0 ..^ %s ) )' % (K, k)
        hNk = w.s([_cl.lift(w, kss, Kh), w.s([], 'simpr', '( %s -> g e. ( 0 ..^ %s ) )' % (Kh, k))], 'sseldd', '( %s -> g e. ( 0 ..^ N ) )' % Kh)
        vhk = w.s([_cl.lift(w, vf, Kh), hNk], 'ffvelcdmd', '( %s -> ( V ` g ) e. CC )' % Kh)
        dck = _cl.lift(w, uc, Kh) if dv == 'u' else None
        ck = Closure(w, Kh, {dv: ('CC', dck), '( V ` g )': ('CC', vhk)}); ck.atom('( V ` g )')
        idqh2 = w.s([], 'id', '( q = g -> q = g )')
        cg2, nq2 = w.wcongr('%s =/= ( V ` q )' % dv, {'q': 'g'}, 'q = g', {'q': idqh2})
        ne2 = w.s([hNk, _cl.lift(w, av, Kh), w.s([cg2], 'rspcv', '( g e. ( 0 ..^ N ) -> ( A. q e. ( 0 ..^ N ) %s =/= ( V ` q ) -> %s ) )' % (dv, nq2))], 'sylc', '( %s -> %s )' % (Kh, nq2))
        ck.have('( %s - ( V ` g ) )' % dv, 'ne0', ap(w, Kh, 'subne0d', '( %s - ( V ` g ) ) =/= 0' % dv, ck, facts=[ne2]))
        fzk = w.s([w.s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % k)], 'a1i', '( %s -> ( 0 ..^ %s ) e. Fin )' % (K, k))
        pc = w.s([fzk, ck.mem('( %s - ( V ` g ) )' % dv, 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (K, PD(k, dv)))
        pn = w.s([fzk, ck.mem('( %s - ( V ` g ) )' % dv, 'CC'), ck.ne0('( %s - ( V ` g ) )' % dv)], 'fprodn0', '( %s -> %s =/= 0 )' % (K, PD(k, dv)))
        return pc, pn
    Aui = '( %s /\\ i e. ( 0 ..^ N ) )' % Au
    toAi = w.s([w.s([], 'simpll', '( %s -> %s )' % (Aui, A0)), w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Aui)], 'jca', '( %s -> %s )' % (Aui, Ai))
    L_ = lambda st: w.s([toAi, st], 'syl', '( %s -> %s )' % (Aui, body_of(w, st)))
    pc1, pn1 = pdfacts(Aui, 'u', '( i + 1 )', L_(i1ss), _cl.lift(w, au, Aui))
    cui = Closure(w, Aui, {FU: ('CC', _cl.lift(w, fyu, Aui)), OMX('i'): ('CC', L_(omc)), PD('( i + 1 )', 'u'): ('CC', pc1)})
    cui.have(PD('( i + 1 )', 'u'), 'ne0', pn1)
    for a in (FU, OMX('i'), PD('( i + 1 )', 'u')):
        cui.atom(a)
    ufr_i = _cl.lift(w, ufr, Aui)
    QU = '( %s / %s )' % (FU, PD('( i + 1 )', 'u'))
    gva = w.s([L_(gfv)], 'fveq1d', '( %s -> ( ( %s ` i ) ` u ) = ( %s ` u ) )' % (Aui, GF, GFI('i')))
    gvb = fvmd(w, Aui, 'd', FR, '( %s x. ( ( %s ` d ) / %s ) )' % (OMX('i'), FY, PD('( i + 1 )', 'd')), 'u', ufr_i,
               w.s([], 'ovexd', '( %s -> ( %s x. %s ) e. _V )' % (Aui, OMX('i'), QU)))
    gvu = w.s([gva, gvb], 'eqtrd', '( %s -> ( ( %s ` i ) ` u ) = ( %s x. %s ) )' % (Aui, GF, OMX('i'), QU))
    d12 = ap(w, Aui, 'div12d', '( %s x. %s ) = ( %s x. ( %s / %s ) )' % (OMX('i'), QU, FU, OMX('i'), PD('( i + 1 )', 'u')), cui)
    TT = '( %s / %s )' % (OMX('i'), PD('( i + 1 )', 'u'))
    pt = w.s([gvu, d12], 'eqtrd', '( %s -> ( ( %s ` i ) ` u ) = ( %s x. %s ) )' % (Aui, GF, FU, TT))
    SG = 'sum_ i e. ( 0 ..^ N ) ( ( %s ` i ) ` u )' % GF
    ST = 'sum_ i e. ( 0 ..^ N ) %s' % TT
    su1 = w.s([pt], 'sumeq2dv', '( %s -> %s = sum_ i e. ( 0 ..^ N ) ( %s x. %s ) )' % (Au, SG, FU, TT))
    su2 = w.s([_cl.lift(w, fzN, Au), fyu, cui.mem(TT, 'CC')], 'fsummulc2', '( %s -> ( %s x. %s ) = sum_ i e. ( 0 ..^ N ) ( %s x. %s ) )' % (Au, FU, ST, FU, TT))
    su3 = w.s([su1, su2], 'eqtr4d', '( %s -> %s = ( %s x. %s ) )' % (Au, SG, FU, ST))
    # OMX ( N ) = 0
    idhJ = w.s([], 'id', '( h = J -> h = J )')
    cghJ, nhJ = w.congr('( %s - ( V ` h ) )' % X, {'h': 'J'}, 'h = J', {'h': idhJ})
    AhN = '( %s /\\ h e. ( 0 ..^ N ) )' % A0
    vhN = w.s([_cl.lift(w, vf, AhN), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % AhN)], 'ffvelcdmd', '( %s -> ( V ` h ) e. CC )' % AhN)
    chN = Closure(w, AhN, {X: ('CC', _cl.lift(w, xc, AhN)), '( V ` h )': ('CC', vhN)}); chN.atom(X); chN.atom('( V ` h )')
    AhJ = '( %s /\\ h = J )' % A0
    z0 = w.s([w.s([cghJ], 'adantl', '( %s -> ( %s - ( V ` h ) ) = ( %s - %s ) )' % (AhJ, X, X, X)), _cl.lift(w, ap(w, A0, 'subidd', '( %s - %s ) = 0' % (X, X), c), AhJ)],
             'eqtrd', '( %s -> ( %s - ( V ` h ) ) = 0 )' % (AhJ, X))
    om0 = s([w.s([], 'nfv', 'F/ h %s' % A0), fzN, chN.mem('( %s - ( V ` h ) )' % X, 'CC'), jn, z0], 'fprodeq0g', '%s = 0' % OMX('N'))
    avN = _cl.lift(w, au, Au)
    pcN, pnN = pdfacts(Au, 'u', 'N', w.s([w.s([], 'ssid', '( 0 ..^ N ) C_ ( 0 ..^ N )')], 'a1i', '( %s -> ( 0 ..^ N ) C_ ( 0 ..^ N ) )' % Au), au)
    cu.have(PD('N', 'u'), 'CC', pcN); cu.have(PD('N', 'u'), 'ne0', pnN); cu.atom(PD('N', 'u'))
    z1 = w.s([_cl.lift(w, om0, Au)], 'oveq1d', '( %s -> ( %s / %s ) = ( 0 / %s ) )' % (Au, OMX('N'), PD('N', 'u'), PD('N', 'u')))
    z2 = w.s([z1, ap(w, Au, 'div0d', '( 0 / %s ) = 0' % PD('N', 'u'), cu)], 'eqtrd', '( %s -> ( %s / %s ) = 0 )' % (Au, OMX('N'), PD('N', 'u')))
    z3 = w.s([w.s([z2], 'oveq2d', '( %s -> ( 1 - ( %s / %s ) ) = ( 1 - 0 ) )' % (Au, OMX('N'), PD('N', 'u'))), w.s([w.s([], '1m0e1', '( 1 - 0 ) = 1')], 'a1i', '( %s -> ( 1 - 0 ) = 1 )' % Au)],
             'eqtrd', '( %s -> ( 1 - ( %s / %s ) ) = 1 )' % (Au, OMX('N'), PD('N', 'u')))
    z4 = w.s([z3], 'oveq1d', '( %s -> ( ( 1 - ( %s / %s ) ) / ( u - %s ) ) = ( 1 / ( u - %s ) ) )' % (Au, OMX('N'), PD('N', 'u'), X, X))
    stv = w.s([tel, z4], 'eqtrd', '( %s -> %s = ( 1 / ( u - %s ) ) )' % (Au, ST, X))
    cu.have('( u - %s )' % X, 'ne0', ap(w, Au, 'subne0d', '( u - %s ) =/= 0' % X, cu, facts=[une]))
    su4 = w.s([su3, w.s([stv], 'oveq2d', '( %s -> ( %s x. %s ) = ( %s x. ( 1 / ( u - %s ) ) ) )' % (Au, FU, ST, FU, X))], 'eqtrd',
              '( %s -> %s = ( %s x. ( 1 / ( u - %s ) ) ) )' % (Au, SG, FU, X))
    su5 = ap(w, Au, 'divrecd', '( %s / ( u - %s ) ) = ( %s x. ( 1 / ( u - %s ) ) )' % (FU, X, FU, X), cu)
    su6 = ap(w, Au, 'mullidd', '( 1 x. ( %s / ( u - %s ) ) ) = ( %s / ( u - %s ) )' % (FU, X, FU, X), cu)
    su7 = w.s([su4, w.s([su6, su5], 'eqtrd', '( %s -> ( 1 x. ( %s / ( u - %s ) ) ) = ( %s x. ( 1 / ( u - %s ) ) ) )' % (Au, FU, X, FU, X))], 'eqtr4d',
              '( %s -> %s = ( 1 x. ( %s / ( u - %s ) ) ) )' % (Au, SG, FU, X))
    sfv = fvmd(w, Au, 'b', FR, 'sum_ i e. ( 0 ..^ N ) ( ( %s ` i ) ` b )' % GF, 'u', ufr,
               w.s([w.s([], 'sumex', '%s e. _V' % SG)], 'a1i', '( %s -> %s e. _V )' % (Au, SG)))
    tfv = fvmd(w, Au, 'd', FR, '( 1 x. ( ( %s ` d ) / ( d - %s ) ) )' % (FY, X), 'u', ufr,
               w.s([], 'ovexd', '( %s -> ( 1 x. ( %s / ( u - %s ) ) ) e. _V )' % (Au, FU, X)))
    peq = w.s([w.s([sfv, su7], 'eqtrd', '( %s -> ( %s ` u ) = ( 1 x. ( %s / ( u - %s ) ) ) )' % (Au, SUMF, FU, X)), tfv], 'eqtr4d',
              '( %s -> ( %s ` u ) = ( %s ` u ) )' % (Au, SUMF, TM))
    allu = w.s([peq], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, FR, SUMF, TM))
    EQ = tsub(stmt('rectinteqe'), {'A': AP, 'B': BQ, 'E': FR, 'F': SUMF, 'G': TM, 'V': '_V'})
    ea, ec = ante_of(EQ)
    have = {'( %s e. CC /\\ %s e. CC )' % (AP, BQ): ab, '%s C_ %s' % (FR, FR): s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '%s C_ %s' % (FR, FR)),
            '%s e. _V' % SUMF: s([frex, w.inst('mptexg')], 'syl', '%s e. _V' % SUMF), '%s e. _V' % TM: s([frex, w.inst('mptexg')], 'syl', '%s e. _V' % TM),
            body_of(w, allu): allu}
    ieq = s([conj(w, A0, ea, have), w.inst('rectinteqe')], 'syl', ec)
    # tpstk with M := 1, Q := X, E := FR
    SK = tsub(S['tpstk'], {'A': AP, 'B': BQ, 'E': FR, 'M': '1', 'Q': X})
    ska, skc = ante_of(SK)
    fdx = s([s([frc, xnf], 'jca', '( %s C_ %s /\\ -. %s e. %s )' % (FR, CN0, X, FR)), w.s([], 'ssdifsn', '( %s C_ ( %s \\ { %s } ) <-> ( %s C_ %s /\\ -. %s e. %s ) )' % (FR, CN0, X, FR, CN0, X, FR))],
            'sylibr', '%s C_ ( %s \\ { %s } )' % (FR, CN0, X))
    have = {'Y e. NN': yn, '( %s e. CC /\\ %s e. CC )' % (AP, BQ): ab, GEOAB: geoab, '1 e. CC': s([], '1cnd', '1 e. CC'), '%s e. CC' % X: xc,
            '%s C_ ( %s \\ { %s } )' % (FR, CN0, X): fdx, '%s C_ %s' % (FR, FR): s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '%s C_ %s' % (FR, FR)),
            '( %s e. %s -> %s )' % (X, CR, INSV(X)): xins}
    stk = s([conj(w, A0, ska, have), w.inst('tpstk')], 'syl', skc)
    WX = '( ( 1 / %s ) ^ Y )' % X
    IFB = 'if ( %s , ( %s x. ( 1 x. %s ) ) , 0 )' % (INSV(X), TPI, WX)
    tot = s([rsum, ieq, stk], '3eqtr3d', '%s = %s' % (SIF, IFB))
    lhs2 = s([lhs, s([tot], 'oveq1d', '( %s / %s ) = ( %s / %s )' % (SIF, TPI, IFB, TPI))], 'eqtrd', '%s = ( %s / %s )' % (LHS, IFB, TPI))
    GOAL = 'if ( %s , %s , 0 )' % (INSV(X), WX)
    # cases
    Ci = '( %s /\\ %s )' % (A0, INSV(X))
    ins = w.s([], 'simpr', '( %s -> %s )' % (Ci, INSV(X)))
    xcr = w.s([_cl.lift(w, ab, Ci), w.s([_cl.lift(w, xc, Ci), ins], 'jca', '( %s -> ( %s e. CC /\\ %s ) )' % (Ci, X, INSV(X))), w.inst('crectinp')], 'syl2anc', '( %s -> %s e. %s )' % (Ci, X, CR))
    xcn = w.s([_cl.lift(w, s([rh], 'simprd', '%s C_ %s' % (CR, CN0)), Ci), xcr], 'sseldd', '( %s -> %s e. %s )' % (Ci, X, CN0))
    xn0 = w.s([w.s([xcn, w.s([], 'eldifsn', '( %s e. %s <-> ( %s e. CC /\\ %s =/= 0 ) )' % (X, CN0, X, X))], 'sylib', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (Ci, X, X)),
               w.inst('simpr')], 'syl', '( %s -> %s =/= 0 )' % (Ci, X))
    cc_ = Closure(w, Ci, {X: ('CC', _cl.lift(w, xc, Ci)), 'Y': ('NN', _cl.lift(w, yn, Ci))}); cc_.have(X, 'ne0', xn0); cc_.atom(X)
    cc_.have(TPI, 'CC', _cl.lift(w, tpi_c, Ci)); cc_.have(TPI, 'ne0', _cl.lift(w, tpi_n, Ci)); cc_.atom(TPI)
    wxc = cc_.mem(WX, 'CC')
    c1a = w.s([ins], 'iftrued', '( %s -> %s = ( %s x. ( 1 x. %s ) ) )' % (Ci, IFB, TPI, WX))
    c1b = w.s([c1a], 'oveq1d', '( %s -> ( %s / %s ) = ( ( %s x. ( 1 x. %s ) ) / %s ) )' % (Ci, IFB, TPI, TPI, WX, TPI))
    c1c = ap(w, Ci, 'divcan3d', '( ( %s x. ( 1 x. %s ) ) / %s ) = ( 1 x. %s )' % (TPI, WX, TPI, WX), cc_)
    c1d = ap(w, Ci, 'mullidd', '( 1 x. %s ) = %s' % (WX, WX), cc_)
    c1e = w.s([ins], 'iftrued', '( %s -> %s = %s )' % (Ci, GOAL, WX))
    case1 = w.s([w.s([c1b, c1c, c1d], '3eqtrd', '( %s -> ( %s / %s ) = %s )' % (Ci, IFB, TPI, WX)), c1e], 'eqtr4d', '( %s -> ( %s / %s ) = %s )' % (Ci, IFB, TPI, GOAL))
    Cn = '( %s /\\ -. %s )' % (A0, INSV(X))
    nin = w.s([], 'simpr', '( %s -> -. %s )' % (Cn, INSV(X)))
    cn_ = Closure(w, Cn, {}); cn_.have(TPI, 'CC', _cl.lift(w, tpi_c, Cn)); cn_.have(TPI, 'ne0', _cl.lift(w, tpi_n, Cn)); cn_.atom(TPI)
    c2a = w.s([w.s([nin], 'iffalsed', '( %s -> %s = 0 )' % (Cn, IFB))], 'oveq1d', '( %s -> ( %s / %s ) = ( 0 / %s ) )' % (Cn, IFB, TPI, TPI))
    c2b = ap(w, Cn, 'div0d', '( 0 / %s ) = 0' % TPI, cn_)
    c2c = w.s([nin], 'iffalsed', '( %s -> %s = 0 )' % (Cn, GOAL))
    case2 = w.s([w.s([c2a, c2b], 'eqtrd', '( %s -> ( %s / %s ) = 0 )' % (Cn, IFB, TPI)), c2c], 'eqtr4d', '( %s -> ( %s / %s ) = %s )' % (Cn, IFB, TPI, GOAL))
    cs = s([case1, case2], 'pm2.61dan', '( %s / %s ) = %s' % (IFB, TPI, GOAL))
    w.qed([lhs2, cs], 'eqtrd', S['tpnode'])
    return run(w)


if __name__ == '__main__':
    gen_node()
