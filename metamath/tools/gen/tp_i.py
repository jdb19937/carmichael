"""Sortie TP: frame-level tools for the Newton coefficients (tpgcn: continuity of a Newton integrand on a set
avoiding 0 and the nodes; tpmulc: a constant factor leaves the boundary integral; tpfrm: the frame of
( P + i S ) , ( Q + i T ) in coordinates)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
import tplib
from tplib import S, W, Closure, ap, apc, lin, lift
import cl as _cl
import ef2lib as E
from tp_g import FY, CN0, FRAB, P10, P01

only = sys.argv[1:]
conj, up, body_of, top_and, ante_of, tsub = E.conj, E.up, E.body_of, E.top_and, E.ante_of, E.tsub
stmt = tplib.stmt


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


PK = lambda K: 'prod_ g e. %s ( d - ( V ` g ) )' % K
GCA = ('( ( Y e. NN /\\ C e. CC ) /\\ ( ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ K C_ ( 0 ..^ N ) ) /\\ '
       '( E C_ %s /\\ A. x e. E A. q e. K x =/= ( V ` q ) ) )' % CN0)
GC = '( d e. E |-> ( C x. ( ( %s ` d ) / %s ) ) )' % (FY, PK('K'))
S['tpgcn'] = '( %s -> %s e. ( E -cn-> CC ) )' % (GCA, GC)


def gen_gcn():
    w = W('tpgcn', 'A Newton integrand ` C ( 1 / d ) ^ Y / prod_ ( g e. K ) ( d - V_h ) ` is continuous on every set avoiding ` 0 ` and the nodes.')
    A0 = GCA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    t1 = s([], 'simp1', '( Y e. NN /\\ C e. CC )'); t2 = s([], 'simp2', '( ( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC ) /\\ K C_ ( 0 ..^ N ) )')
    t3 = s([], 'simp3', '( E C_ %s /\\ A. x e. E A. q e. K x =/= ( V ` q ) )' % CN0)
    yn = s([t1], 'simpld', 'Y e. NN'); cc = s([t1], 'simprd', 'C e. CC')
    vf = s([s([t2], 'simpld', '( N e. NN0 /\\ V : ( 0 ..^ N ) --> CC )')], 'simprd', 'V : ( 0 ..^ N ) --> CC')
    ks = s([t2], 'simprd', 'K C_ ( 0 ..^ N )')
    ec = s([t3], 'simpld', 'E C_ %s' % CN0); av = s([t3], 'simprd', 'A. x e. E A. q e. K x =/= ( V ` q )')
    kf = s([s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin'), ks, w.inst('ssfi')], 'syl2anc', 'K e. Fin')
    cs = s([w.s([], 'difss', '%s C_ CC' % CN0)], 'a1i', '%s C_ CC' % CN0)
    ecc = s([ec, cs], 'sstrd', 'E C_ CC')
    # numerator ( FY ` d )
    fh = s([yn, w.inst('tpfh')], 'syl', '( %s e. ( %s -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (FY, CN0, CN0, FY))
    fcn = s([fh], 'simpld', '%s e. ( %s -cn-> CC )' % (FY, CN0))
    rf = s([ec, fcn, w.inst('rescncf')], 'sylc', '( %s |` E ) e. ( E -cn-> CC )' % FY)
    fr = s([s([fcn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (FY, CN0)), ec], 'feqresmpt', '( %s |` E ) = ( d e. E |-> ( %s ` d ) )' % (FY, FY))
    num = s([fr, rf], 'eqeltrrd', '( d e. E |-> ( %s ` d ) ) e. ( E -cn-> CC )' % FY)
    # denominator: entire product, restricted, nonzero on E
    Ah = '( %s /\\ g e. K )' % A0
    vh = w.s([_cl.lift(w, vf, Ah), w.s([_cl.lift(w, ks, Ah), w.s([], 'simpr', '( %s -> g e. K )' % Ah)], 'sseldd', '( %s -> g e. ( 0 ..^ N ) )' % Ah)],
             'ffvelcdmd', '( %s -> ( V ` g ) e. CC )' % Ah)
    hs = w.s([vh, w.s([w.s([], 'cnopn', 'CC e. ( TopOpen ` CCfld )')], 'a1i', '( %s -> CC e. ( TopOpen ` CCfld ) )' % Ah), w.inst('ef2hsub')], 'syl2anc',
             '( %s -> ( ( d e. CC |-> ( d - ( V ` g ) ) ) e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D ( d e. CC |-> ( d - ( V ` g ) ) ) ) ) )' % Ah)
    idhk = w.s([], 'id', '( g = k -> g = k )')
    cghk, _ = w.congr('( d - ( V ` g ) )', {'g': 'k'}, 'g = k', {'g': idhk})
    ent = s([kf, hs, cghk], 'z6ehfp', '( ( d e. CC |-> %s ) e. ( CC -cn-> CC ) /\\ CC C_ dom ( CC _D ( d e. CC |-> %s ) ) )' % (PK('K'), PK('K')))
    entc = s([ent], 'simpld', '( d e. CC |-> %s ) e. ( CC -cn-> CC )' % PK('K'))
    Ad = '( %s /\\ d e. E )' % A0
    dE = w.s([], 'simpr', '( %s -> d e. E )' % Ad)
    dcn = w.s([_cl.lift(w, ec, Ad), dE], 'sseldd', '( %s -> d e. %s )' % (Ad, CN0))
    dc = w.s([_cl.lift(w, ecc, Ad), dE], 'sseldd', '( %s -> d e. CC )' % Ad)
    Adh = '( %s /\\ g e. K )' % Ad
    # A. q e. K d =/= ( V ` q ) at this d
    idxd = w.s([], 'id', '( x = d -> x = d )')
    cgxd, nxd = w.wcongr('A. q e. K x =/= ( V ` q )', {'x': 'd'}, 'x = d', {'x': idxd})
    aqd = w.s([dE, _cl.lift(w, av, Ad), w.s([cgxd], 'rspcv', '( d e. E -> ( A. x e. E A. q e. K x =/= ( V ` q ) -> %s ) )' % nxd)], 'sylc',
              '( %s -> A. q e. K d =/= ( V ` q ) )' % Ad)
    idqh = w.s([], 'id', '( q = g -> q = g )')
    cgq, nq = w.wcongr('d =/= ( V ` q )', {'q': 'g'}, 'q = g', {'q': idqh})
    hK = w.s([], 'simpr', '( %s -> g e. K )' % Adh)
    ne = w.s([hK, _cl.lift(w, aqd, Adh), w.s([cgq], 'rspcv', '( g e. K -> ( A. q e. K d =/= ( V ` q ) -> %s ) )' % nq)], 'sylc', '( %s -> %s )' % (Adh, nq))
    ch = Closure(w, Adh, {'d': ('CC', _cl.lift(w, dc, Adh))})
    vh2 = w.s([_cl.lift(w, vf, Adh), w.s([_cl.lift(w, ks, Adh), hK], 'sseldd', '( %s -> g e. ( 0 ..^ N ) )' % Adh)], 'ffvelcdmd', '( %s -> ( V ` g ) e. CC )' % Adh)
    ch.have('( V ` g )', 'CC', vh2); ch.atom('( V ` g )')
    fne = ap(w, Adh, 'subne0d', '( d - ( V ` g ) ) =/= 0', ch, facts=[ne])
    fk = w.s([w.s([kf], 'adantr', '( %s -> K e. Fin )' % Ad), ch.mem('( d - ( V ` g ) )', 'CC'), fne], 'fprodn0', '( %s -> %s =/= 0 )' % (Ad, PK('K')))
    fcc = w.s([w.s([kf], 'adantr', '( %s -> K e. Fin )' % Ad), ch.mem('( d - ( V ` g ) )', 'CC')], 'fprodcl', '( %s -> %s e. CC )' % (Ad, PK('K')))
    fin = w.s([w.s([fcc, fk], 'jca', '( %s -> ( %s e. CC /\\ %s =/= 0 ) )' % (Ad, PK('K'), PK('K'))),
               w.s([], 'eldifsn', '( %s e. ( CC \\ { 0 } ) <-> ( %s e. CC /\\ %s =/= 0 ) )' % (PK('K'), PK('K'), PK('K')))], 'sylibr',
              '( %s -> %s e. ( CC \\ { 0 } ) )' % (Ad, PK('K')))
    re_ = s([ecc, entc, w.inst('rescncf')], 'sylc', '( ( d e. CC |-> %s ) |` E ) e. ( E -cn-> CC )' % PK('K'))
    rm = s([ecc, w.inst('resmpt')], 'syl', '( ( d e. CC |-> %s ) |` E ) = ( d e. E |-> %s )' % (PK('K'), PK('K')))
    dcc = s([rm, re_], 'eqeltrrd', '( d e. E |-> %s ) e. ( E -cn-> CC )' % PK('K'))
    dff = s([fin], 'fmptd', '( d e. E |-> %s ) : E --> ( CC \\ { 0 } )' % PK('K'))
    den = s([s([cs, dcc, w.inst('cncfcdm')], 'syl2anc', '( ( d e. E |-> %s ) e. ( E -cn-> ( CC \\ { 0 } ) ) <-> ( d e. E |-> %s ) : E --> ( CC \\ { 0 } ) )' % (PK('K'), PK('K'))), dff],
            'mpbird', '( d e. E |-> %s ) e. ( E -cn-> ( CC \\ { 0 } ) )' % PK('K'))
    q = s([num, den], 'divcncf', '( d e. E |-> ( ( %s ` d ) / %s ) ) e. ( E -cn-> CC )' % (FY, PK('K')))
    cst = s([cc, ecc, s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', 'CC C_ CC'), w.inst('cncfmptc')], 'syl3anc', '( d e. E |-> C ) e. ( E -cn-> CC )')
    w.qed([cst, q], 'mulcncf', S['tpgcn'])
    return run(w)


MCA = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( %s C_ E /\\ G e. ( E -cn-> CC ) ) ) /\\ ( C e. CC /\\ F e. V /\\ A. x e. E ( F ` x ) = ( C x. ( G ` x ) ) ) )' % FRAB)
S['tpmulc'] = '( %s -> ( F rectint <. A , B >. ) = ( C x. ( G rectint <. A , B >. ) ) )' % MCA


def gen_mulc():
    w = W('tpmulc', 'A constant factor leaves the boundary integral over any carrier of the frame (C3 ~ rectintlce with ` ( C - 1 ) G + G ` ).')
    A0 = MCA
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    ab = s([], 'simpll', '( A e. CC /\\ B e. CC )'); x2 = s([], 'simplr', '( %s C_ E /\\ G e. ( E -cn-> CC ) )' % FRAB)
    fre = s([x2], 'simpld', '%s C_ E' % FRAB); gcn = s([x2], 'simprd', 'G e. ( E -cn-> CC )')
    x3 = s([], 'simpr', '( C e. CC /\\ F e. V /\\ A. x e. E ( F ` x ) = ( C x. ( G ` x ) ) )')
    cc = s([x3], 'simp1d', 'C e. CC'); fv = s([x3], 'simp2d', 'F e. V'); al = s([x3], 'simp3d', 'A. x e. E ( F ` x ) = ( C x. ( G ` x ) )')
    c = Closure(w, A0, {'C': ('CC', cc)})
    Au = '( %s /\\ u e. E )' % A0
    ue = w.s([], 'simpr', '( %s -> u e. E )' % Au)
    gu = w.s([w.s([_cl.lift(w, gcn, Au), w.inst('cncff')], 'syl', '( %s -> G : E --> CC )' % Au), ue], 'ffvelcdmd', '( %s -> ( G ` u ) e. CC )' % Au)
    idxu = w.s([], 'id', '( x = u -> x = u )')
    cgxu, nxu = w.wcongr('( F ` x ) = ( C x. ( G ` x ) )', {'x': 'u'}, 'x = u', {'x': idxu})
    fu = w.s([ue, _cl.lift(w, al, Au), w.s([cgxu], 'rspcv', '( u e. E -> ( A. x e. E ( F ` x ) = ( C x. ( G ` x ) ) -> %s ) )' % nxu)], 'sylc',
             '( %s -> ( F ` u ) = ( C x. ( G ` u ) ) )' % Au)
    cu = Closure(w, Au, {'C': ('CC', _cl.lift(w, cc, Au)), '( G ` u )': ('CC', gu)}); cu.atom('( G ` u )')
    import mvlib
    r = mvlib.ringeq(w, Au, '( C x. ( G ` u ) )', '( ( ( C - 1 ) x. ( G ` u ) ) + ( G ` u ) )', cu)
    pt = w.s([fu, r], 'eqtrd', '( %s -> ( F ` u ) = ( ( ( C - 1 ) x. ( G ` u ) ) + ( G ` u ) ) )' % Au)
    allp = w.s([pt], 'ralrimiva', '( %s -> A. u e. E ( F ` u ) = ( ( ( C - 1 ) x. ( G ` u ) ) + ( G ` u ) ) )' % A0)
    LC = tsub(stmt('rectintlce'), {'C': '( C - 1 )', 'H': 'G', 'D': 'E'})
    la, lc = ante_of(LC)
    m1c = c.mem('( C - 1 )', 'CC')
    have = {'( A e. CC /\\ B e. CC )': ab, '%s C_ E' % FRAB: fre, 'F e. V': fv, '( C - 1 ) e. CC': m1c, 'G e. ( E -cn-> CC )': gcn,
            'E C_ E': s([w.s([], 'ssid', 'E C_ E')], 'a1i', 'E C_ E'), body_of(w, allp): allp}
    lce = s([conj(w, A0, la, have), w.inst('rectintlce')], 'syl', lc)
    I = '( G rectint <. A , B >. )'
    ic = s([ab, s([gcn, fre], 'jca', '( G e. ( E -cn-> CC ) /\\ %s C_ E )' % FRAB), w.inst('rectintcle')], 'syl2anc', '%s e. CC' % I)
    c.have(I, 'CC', ic); c.atom(I)
    r2 = mvlib.ringeq(w, A0, '( ( ( C - 1 ) x. %s ) + %s )' % (I, I), '( C x. %s )' % I, c)
    w.qed([lce, r2], 'eqtrd', S['tpmulc'])
    return run(w)


AP = '( P + ( _i x. S ) )'; BQ = '( Q + ( _i x. T ) )'
FRA = tsub(FRAB, {'A': AP, 'B': BQ})
FRP = '( ( ( %s cseg ( Q + ( _i x. S ) ) ) u. ( ( Q + ( _i x. S ) ) cseg %s ) ) u. ( ( %s cseg ( P + ( _i x. T ) ) ) u. ( ( P + ( _i x. T ) ) cseg %s ) ) )' % (AP, BQ, BQ, AP)
S['tpfrm'] = '( ( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ T e. RR ) ) -> %s = %s )' % (FRA, FRP)


def gen_frm():
    w = W('tpfrm', 'The frame of the rectangle with corners ` P + i S ` , ` Q + i T ` , in coordinates.')
    A0 = '( ( P e. RR /\\ Q e. RR ) /\\ ( S e. RR /\\ T e. RR ) )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    p = s([], 'simpll', 'P e. RR'); q = s([], 'simplr', 'Q e. RR'); ss_ = s([], 'simprl', 'S e. RR'); t = s([], 'simprr', 'T e. RR')
    rb = s([q, t, w.inst('crre')], 'syl2anc', '( Re ` %s ) = Q' % BQ)
    ia = s([p, ss_, w.inst('crim')], 'syl2anc', '( Im ` %s ) = S' % AP)
    ra = s([p, ss_, w.inst('crre')], 'syl2anc', '( Re ` %s ) = P' % AP)
    ib = s([q, t, w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % BQ)
    st, new = w.rewrite(FRA, {'( Re ` %s )' % BQ: ('Q', rb), '( Im ` %s )' % AP: ('S', ia), '( Re ` %s )' % AP: ('P', ra), '( Im ` %s )' % BQ: ('T', ib)}, A0)
    assert new == FRP, new
    last = [l for l in w.lines if l.startswith(st + ':')][0]
    w.lines[w.lines.index(last)] = 'qed' + last[len(st):]
    return run(w)


if __name__ == '__main__':
    gen_gcn()
    gen_mulc()
    gen_frm()
