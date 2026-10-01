"""Sortie TP: ordering the Newton nodes (tpord1: a permutation listing a given subset first;
tpord: every prefix product of an ordering 'factors >_ C first' is >_ C ^ ( i + 1 ))."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from tplib import *
import mvlib
import cl as _cl

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


FNN = '( 0 ..^ N )'
S['tpord1'] = ('( ( N e. NN0 /\\ G C_ ( 0 ..^ N ) ) -> E. s ( s : ( 0 ..^ N ) -1-1-onto-> ( 0 ..^ N ) /\\ '
               'A. h e. ( 0 ..^ N ) ( ( s ` h ) e. G <-> h < ( # ` G ) ) ) )')


def gen_ord1():
    w = W('tpord1', 'A permutation of ` 0 ..^ N ` that lists a given subset G first: ` s ( h ) e. G ` exactly for ` h < # G ` .')
    A = '( N e. NN0 /\\ G C_ ( 0 ..^ N ) )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A, f))
    nn = s([], 'simpl', 'N e. NN0'); gs = s([], 'simpr', 'G C_ ( 0 ..^ N )')
    a = '( # ` G )'
    BB = '( ( 0 ..^ N ) \\ G )'
    fz = s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin')
    gf = s([fz, gs, w.inst('ssfi')], 'syl2anc', 'G e. Fin')
    an = s([gf, w.inst('hashcl')], 'syl', '%s e. NN0' % a)
    c = Closure(w, A, {'N': ('NN0', nn), a: ('NN0', an)})
    hN = s([nn, w.inst('hashfzo0')], 'syl', '( # ` ( 0 ..^ N ) ) = N')
    ale = s([s([fz, gs, w.inst('hashss')], 'syl2anc', '%s <_ ( # ` ( 0 ..^ N ) )' % a), hN], 'breqtrd', '%s <_ N' % a)
    nua = s([s([c.mem(a, 'ZZ'), c.mem('N', 'ZZ'), ale], '3jca', '( %s e. ZZ /\\ N e. ZZ /\\ %s <_ N )' % (a, a)), w.inst('eluz2')], 'sylibr',
            'N e. ( ZZ>= ` %s )' % a)
    hb = s([fz, gs, w.inst('hashssdif')], 'syl2anc', '( # ` %s ) = ( ( # ` ( 0 ..^ N ) ) - %s )' % (BB, a))
    hb = s([hb, s([hN], 'oveq1d', '( ( # ` ( 0 ..^ N ) ) - %s ) = ( N - %s )' % (a, a))], 'eqtrd', '( # ` %s ) = ( N - %s )' % (BB, a))
    hr = s([nua, w.inst('hashfzo')], 'syl', '( # ` ( %s ..^ N ) ) = ( N - %s )' % (a, a))
    ha = s([an, w.inst('hashfzo0')], 'syl', '( # ` ( 0 ..^ %s ) ) = %s' % (a, a))
    fza = s([w.s([], 'fzofi', '( 0 ..^ %s ) e. Fin' % a)], 'a1i', '( 0 ..^ %s ) e. Fin' % a)
    fzr = s([w.s([], 'fzofi', '( %s ..^ N ) e. Fin' % a)], 'a1i', '( %s ..^ N ) e. Fin' % a)
    bf = s([fz, w.inst('diffi')], 'syl', '%s e. Fin' % BB)
    e1 = s([ha, s([fza, gf, w.inst('hasheqf1o')], 'syl2anc', '( ( # ` ( 0 ..^ %s ) ) = ( # ` G ) <-> E. g g : ( 0 ..^ %s ) -1-1-onto-> G )' % (a, a))],
           'mpbid', 'E. g g : ( 0 ..^ %s ) -1-1-onto-> G' % a)
    hrb = s([hr, hb], 'eqtr4d', '( # ` ( %s ..^ N ) ) = ( # ` %s )' % (a, BB))
    e2 = s([hrb, s([fzr, bf, w.inst('hasheqf1o')], 'syl2anc', '( ( # ` ( %s ..^ N ) ) = ( # ` %s ) <-> E. b b : ( %s ..^ N ) -1-1-onto-> %s )' % (a, BB, a, BB))],
           'mpbid', 'E. b b : ( %s ..^ N ) -1-1-onto-> %s' % (a, BB))
    # under the two bijections
    G1 = 'g : ( 0 ..^ %s ) -1-1-onto-> G' % a; B1 = 'b : ( %s ..^ N ) -1-1-onto-> %s' % (a, BB)
    X = '( %s /\\ ( %s /\\ %s ) )' % (A, G1, B1)
    sx = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (X, f))
    g1 = sx([], 'simprl', G1); b1 = sx([], 'simprr', B1)
    LA = lambda st: _cl.lift(w, st, X)
    u = sx([sx([g1, b1], 'jca', '( %s /\\ %s )' % (G1, B1)),
            sx([sx([w.s([], 'fzodisj', '( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/)' % (a, a))], 'a1i', '( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/)' % (a, a)),
                sx([w.s([], 'disjdif', '( G i^i %s ) = (/)' % BB)], 'a1i', '( G i^i %s ) = (/)' % BB)], 'jca',
               '( ( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/) /\\ ( G i^i %s ) = (/) )' % (a, a, BB)), w.inst('f1oun')], 'syl2anc',
           '( g u. b ) : ( ( 0 ..^ %s ) u. ( %s ..^ N ) ) -1-1-onto-> ( G u. %s )' % (a, a, BB))
    ainz = ap(w, A, 'elfzd', '%s e. ( 0 ... N )' % a, c, facts=[s([w.s([], '0z', '0 e. ZZ')], 'a1i', '0 e. ZZ'), c.mem('N', 'ZZ'), c.mem(a, 'ZZ'),
                                                             ap(w, A, 'nn0ge0d', '0 <_ %s' % a, c), ale])
    dsp = s([ainz, w.inst('fzosplit')], 'syl', '( 0 ..^ N ) = ( ( 0 ..^ %s ) u. ( %s ..^ N ) )' % (a, a))
    cod = s([gs, w.inst('undif')], 'sylib', '( G u. %s ) = ( 0 ..^ N )' % BB)
    f2 = sx([LA(s([dsp], 'eqcomd', '( ( 0 ..^ %s ) u. ( %s ..^ N ) ) = ( 0 ..^ N )' % (a, a)))], 'f1oeq2d',
            '( ( g u. b ) : ( ( 0 ..^ %s ) u. ( %s ..^ N ) ) -1-1-onto-> ( G u. %s ) <-> ( g u. b ) : ( 0 ..^ N ) -1-1-onto-> ( G u. %s ) )' % (a, a, BB, BB))
    f3 = sx([LA(cod)], 'f1oeq3d', '( ( g u. b ) : ( 0 ..^ N ) -1-1-onto-> ( G u. %s ) <-> ( g u. b ) : ( 0 ..^ N ) -1-1-onto-> ( 0 ..^ N ) )' % BB)
    sf = sx([sx([u, f2], 'mpbid', '( g u. b ) : ( 0 ..^ N ) -1-1-onto-> ( G u. %s )' % BB), f3], 'mpbid', '( g u. b ) : ( 0 ..^ N ) -1-1-onto-> ( 0 ..^ N )')
    # membership property
    Xh = '( %s /\\ h e. ( 0 ..^ N ) )' % X
    XA_ = '( %s /\\ h e. ( 0 ..^ %s ) )' % (X, a)
    XB_ = '( %s /\\ h e. ( %s ..^ N ) )' % (X, a)
    gfn = sx([g1, w.inst('f1ofn')], 'syl', 'g Fn ( 0 ..^ %s )' % a)
    bfn = sx([b1, w.inst('f1ofn')], 'syl', 'b Fn ( %s ..^ N )' % a)
    dj = w.s([], 'fzodisj', '( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/)' % (a, a))
    ha_ = w.s([], 'simpr', '( %s -> h e. ( 0 ..^ %s ) )' % (XA_, a))
    va = w.s([_cl.lift(w, gfn, XA_), _cl.lift(w, bfn, XA_), w.s([w.s([dj], 'a1i', '( %s -> ( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/) )' % (XA_, a, a)), ha_], 'jca',
              '( %s -> ( ( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/) /\\ h e. ( 0 ..^ %s ) ) )' % (XA_, a, a, a)), w.inst('fvun1')], 'syl3anc',
             '( %s -> ( ( g u. b ) ` h ) = ( g ` h ) )' % XA_)
    gv = w.s([w.s([_cl.lift(w, g1, XA_), w.inst('f1of')], 'syl', '( %s -> g : ( 0 ..^ %s ) --> G )' % (XA_, a)), ha_], 'ffvelcdmd', '( %s -> ( g ` h ) e. G )' % XA_)
    inA = w.s([va, gv], 'eqeltrd', '( %s -> ( ( g u. b ) ` h ) e. G )' % XA_)
    ltA = w.s([ha_, w.inst('elfzolt2')], 'syl', '( %s -> h < %s )' % (XA_, a))
    bA = w.s([inA, ltA], '2thd', '( %s -> ( ( ( g u. b ) ` h ) e. G <-> h < %s ) )' % (XA_, a))
    hb_ = w.s([], 'simpr', '( %s -> h e. ( %s ..^ N ) )' % (XB_, a))
    vb = w.s([_cl.lift(w, gfn, XB_), _cl.lift(w, bfn, XB_), w.s([w.s([dj], 'a1i', '( %s -> ( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/) )' % (XB_, a, a)), hb_], 'jca',
              '( %s -> ( ( ( 0 ..^ %s ) i^i ( %s ..^ N ) ) = (/) /\\ h e. ( %s ..^ N ) ) )' % (XB_, a, a, a)), w.inst('fvun2')], 'syl3anc',
             '( %s -> ( ( g u. b ) ` h ) = ( b ` h ) )' % XB_)
    bv = w.s([w.s([_cl.lift(w, b1, XB_), w.inst('f1of')], 'syl', '( %s -> b : ( %s ..^ N ) --> %s )' % (XB_, a, BB)), hb_], 'ffvelcdmd', '( %s -> ( b ` h ) e. %s )' % (XB_, BB))
    inB = w.s([vb, bv], 'eqeltrd', '( %s -> ( ( g u. b ) ` h ) e. %s )' % (XB_, BB))
    nG = w.s([inB, w.inst('eldifn')], 'syl', '( %s -> -. ( ( g u. b ) ` h ) e. G )' % XB_)
    cb = Closure(w, XB_, {a: ('NN0', _cl.lift(w, an, XB_)), 'h': ('ZZ', w.s([hb_, w.inst('elfzoelz')], 'syl', '( %s -> h e. ZZ )' % XB_))})
    leB = w.s([hb_, w.inst('elfzole1')], 'syl', '( %s -> %s <_ h )' % (XB_, a))
    nlt = w.s([leB, ap(w, XB_, 'lenltd', '( %s <_ h <-> -. h < %s )' % (a, a), cb)], 'mpbid', '( %s -> -. h < %s )' % (XB_, a))
    bB = w.s([nG, nlt], '2falsed', '( %s -> ( ( ( g u. b ) ` h ) e. G <-> h < %s ) )' % (XB_, a))
    bAB = w.s([bA, bB], 'jaodan', '( ( %s /\\ ( h e. ( 0 ..^ %s ) \\/ h e. ( %s ..^ N ) ) ) -> ( ( ( g u. b ) ` h ) e. G <-> h < %s ) )' % (X, a, a, a))
    hin = w.s([w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % Xh), _cl.lift(w, dsp, Xh)], 'eleqtrd', '( %s -> h e. ( ( 0 ..^ %s ) u. ( %s ..^ N ) ) )' % (Xh, a, a))
    hor = w.s([hin, w.inst('elun')], 'sylib', '( %s -> ( h e. ( 0 ..^ %s ) \\/ h e. ( %s ..^ N ) ) )' % (Xh, a, a))
    bH = w.s([w.s([], 'simpl', '( %s -> %s )' % (Xh, X)), hor, bAB], 'syl2anc',
             '( %s -> ( ( ( g u. b ) ` h ) e. G <-> h < %s ) )' % (Xh, a))
    al = w.s([bH], 'ralrimiva', '( %s -> A. h e. ( 0 ..^ N ) ( ( ( g u. b ) ` h ) e. G <-> h < %s ) )' % (X, a))
    PHI = lambda sv: '( %s : ( 0 ..^ N ) -1-1-onto-> ( 0 ..^ N ) /\\ A. h e. ( 0 ..^ N ) ( ( %s ` h ) e. G <-> h < %s ) )' % (sv, sv, a)
    both = sx([sf, al], 'jca', PHI('( g u. b )'))
    ids = w.s([], 'id', '( s = ( g u. b ) -> s = ( g u. b ) )')
    cgs, news = w.wcongr(PHI('s'), {'s': '( g u. b )'}, 's = ( g u. b )', {'s': ids})
    assert news == PHI('( g u. b )'), news
    ue = w.s([w.s([], 'vex', 'g e. _V'), w.s([], 'vex', 'b e. _V')], 'unex', '( g u. b ) e. _V')
    sp = w.s([cgs], 'spcegv', '( ( g u. b ) e. _V -> ( %s -> E. s %s ) )' % (news, PHI('s')))
    goalx = sx([sx([ue], 'a1i', '( g u. b ) e. _V'), both, sp], 'sylc', 'E. s %s' % PHI('s'))
    GOAL = 'E. s %s' % PHI('s')
    t1 = w.s([goalx], 'expr', '( ( %s /\\ %s ) -> ( %s -> %s ) )' % (A, G1, B1, GOAL))
    t2 = w.s([t1], 'exlimdv', '( ( %s /\\ %s ) -> ( E. b %s -> %s ) )' % (A, G1, B1, GOAL))
    t3 = w.s([_cl.lift(w, e2, '( %s /\\ %s )' % (A, G1)), t2], 'mpd', '( ( %s /\\ %s ) -> %s )' % (A, G1, GOAL))
    t4 = w.s([t3], 'ex', '( %s -> ( %s -> %s ) )' % (A, G1, GOAL))
    t5 = w.s([t4], 'exlimdv', '( %s -> ( E. g %s -> %s ) )' % (A, G1, GOAL))
    w.qed([e1, t5], 'mpd', S['tpord1'])
    return run(w)


GS = '{ x e. ( 0 ..^ N ) | C <_ ( F ` x ) }'
AG = '( # ` %s )' % GS
SF = 's : ( 0 ..^ N ) -1-1-onto-> ( 0 ..^ N )'
PRE = lambda i: 'prod_ h e. ( 0 ..^ ( %s + 1 ) ) ( F ` ( s ` h ) )' % i
ALLI = 'A. i e. ( 0 ..^ N ) ( C ^ ( i + 1 ) ) <_ %s' % PRE('i')
S['tpord'] = ('( ( ( N e. NN0 /\\ F : ( 0 ..^ N ) --> RR+ ) /\\ ( C e. RR+ /\\ ( C ^ N ) <_ prod_ y e. ( 0 ..^ N ) ( F ` y ) ) ) -> '
              'E. s ( %s /\\ %s ) )' % (SF, ALLI))


def gen_ord():
    w = W('tpord', 'Ordering the Newton nodes: when the factors ` >_ C ` come first, every prefix product is ` >_ C ^ ( i + 1 ) ` '
               '(replaces the sort and Lean ` prod_range_pow_le_prod_prefix_pow ` ).')
    A = '( ( N e. NN0 /\\ F : ( 0 ..^ N ) --> RR+ ) /\\ ( C e. RR+ /\\ ( C ^ N ) <_ prod_ y e. ( 0 ..^ N ) ( F ` y ) ) )'
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A, f))
    nn = s([], 'simpll', 'N e. NN0'); ff = s([], 'simplr', 'F : ( 0 ..^ N ) --> RR+')
    cp = s([], 'simprl', 'C e. RR+'); hy = s([], 'simprr', '( C ^ N ) <_ prod_ y e. ( 0 ..^ N ) ( F ` y )')
    gsub = s([w.s([], 'ssrab2', '%s C_ ( 0 ..^ N )' % GS)], 'a1i', '%s C_ ( 0 ..^ N )' % GS)
    ALLH = 'A. h e. ( 0 ..^ N ) ( ( s ` h ) e. %s <-> h < %s )' % (GS, AG)
    ALLZ = 'A. z e. ( 0 ..^ N ) ( ( s ` z ) e. %s <-> z < %s )' % (GS, AG)
    o1 = s([nn, gsub, w.inst('tpord1')], 'syl2anc', 'E. s ( %s /\\ %s )' % (SF, ALLH))
    idhz = w.s([], 'id', '( h = z -> h = z )')
    cghz, newz = w.wcongr('( ( s ` h ) e. %s <-> h < %s )' % (GS, AG), {'h': 'z'}, 'h = z', {'h': idhz})
    cbz = w.s([cghz], 'cbvralvw', '( %s <-> %s )' % (ALLH, ALLZ))
    anb = w.s([cbz], 'anbi2i', '( ( %s /\\ %s ) <-> ( %s /\\ %s ) )' % (SF, ALLH, SF, ALLZ))
    G = '( %s /\\ ( %s /\\ %s ) )' % (A, SF, ALLZ)
    Gi = '( %s /\\ i e. ( 0 ..^ N ) )' % G
    gi = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Gi, f))
    Li = lambda st: _cl.lift(w, st, Gi)
    ci = Closure(w, Gi, {'N': ('NN0', Li(nn)), 'C': ('RR+', Li(cp))})
    iin = w.s([], 'simpr', '( %s -> i e. ( 0 ..^ N ) )' % Gi)
    ci.have('i', 'NN0', gi([iin, w.inst('elfzonn0')], 'syl', 'i e. NN0'))
    ci.have(AG, 'NN0', gi([gi([gi([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( 0 ..^ N ) e. Fin'), Li(gsub), w.inst('ssfi')], 'syl2anc', '%s e. Fin' % GS),
                           w.inst('hashcl')], 'syl', '%s e. NN0' % AG))
    sfm = gi([Li(w.s([], 'simprl', '( %s -> %s )' % (G, SF))), w.inst('f1of')], 'syl', 's : ( 0 ..^ N ) --> ( 0 ..^ N )')
    allz = Li(w.s([], 'simprr', '( %s -> %s )' % (G, ALLZ)))
    ip1 = gi([iin, w.inst('fzofzp1')], 'syl', '( i + 1 ) e. ( 0 ... N )')
    nui = gi([ip1, w.inst('elfzuz3')], 'syl', 'N e. ( ZZ>= ` ( i + 1 ) )')
    # facts at a node h of a context K (K extends Gi), given h e. ( 0 ..^ N )
    def node(K, hin):
        cK = Closure(w, K, {'C': ('RR+', _cl.lift(w, cp, K))})
        sh = w.s([_cl.lift(w, sfm, K), hin], 'ffvelcdmd', '( %s -> ( s ` h ) e. ( 0 ..^ N ) )' % K)
        fsh = w.s([_cl.lift(w, ff, K), sh], 'ffvelcdmd', '( %s -> ( F ` ( s ` h ) ) e. RR+ )' % K)
        cK.have('( F ` ( s ` h ) )', 'RR+', fsh); cK.atom('( F ` ( s ` h ) )')
        idzh = w.s([], 'id', '( z = h -> z = h )')
        cgz, nz = w.wcongr('( ( s ` z ) e. %s <-> z < %s )' % (GS, AG), {'z': 'h'}, 'z = h', {'z': idzh})
        rz = w.s([cgz], 'rspcv', '( h e. ( 0 ..^ N ) -> ( %s -> %s ) )' % (ALLZ, nz))
        bi = w.s([hin, _cl.lift(w, allz, K), rz], 'sylc', '( %s -> %s )' % (K, nz))
        idxs = w.s([], 'id', '( x = ( s ` h ) -> x = ( s ` h ) )')
        cgx, nx = w.wcongr('C <_ ( F ` x )', {'x': '( s ` h )'}, 'x = ( s ` h )', {'x': idxs})
        er = w.s([cgx], 'elrab', '( ( s ` h ) e. %s <-> ( ( s ` h ) e. ( 0 ..^ N ) /\\ %s ) )' % (GS, nx))
        return cK, sh, fsh, bi, er, nx
    # ---- case ( i + 1 ) <_ a
    K1 = '( %s /\\ ( i + 1 ) <_ %s )' % (Gi, AG)
    K1h = '( %s /\\ h e. ( 0 ..^ ( i + 1 ) ) )' % K1
    hA = w.s([], 'simpr', '( %s -> h e. ( 0 ..^ ( i + 1 ) ) )' % K1h)
    sub1 = gi([nui, w.inst('fzoss2')], 'syl', '( 0 ..^ ( i + 1 ) ) C_ ( 0 ..^ N )')
    hN1 = w.s([_cl.lift(w, sub1, K1h), hA], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % K1h)
    c1, sh1, fsh1, bi1, er1, nx1 = node(K1h, hN1)
    c1.have('h', 'ZZ', w.s([hA, w.inst('elfzoelz')], 'syl', '( %s -> h e. ZZ )' % K1h))
    c1.have('i', 'NN0', _cl.lift(w, ci.mem('i', 'NN0'), K1h)); c1.have(AG, 'NN0', _cl.lift(w, ci.mem(AG, 'NN0'), K1h))
    hlt = w.s([hA, w.inst('elfzolt2')], 'syl', '( %s -> h < ( i + 1 ) )' % K1h)
    hla = lin.linarith(w, K1h, [hlt, _cl.lift(w, w.s([], 'simpr', '( %s -> ( i + 1 ) <_ %s )' % (K1, AG)), K1h)], 'h < %s' % AG, closure=c1)
    ing = w.s([hla, bi1], 'mpbird', '( %s -> ( s ` h ) e. %s )' % (K1h, GS))
    cle = w.s([w.s([ing, er1], 'sylib', '( %s -> ( ( s ` h ) e. ( 0 ..^ N ) /\\ %s ) )' % (K1h, nx1))], 'simprd', '( %s -> %s )' % (K1h, nx1))
    fz1 = w.s([w.s([], 'fzofi', '( 0 ..^ ( i + 1 ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( i + 1 ) ) e. Fin )' % K1)
    pl = w.s([w.s([], 'nfv', 'F/ h %s' % K1), fz1, c1.mem('C', 'RR'), c1.ge0('C'), c1.mem('( F ` ( s ` h ) )', 'RR'), cle], 'fprodle',
             '( %s -> prod_ h e. ( 0 ..^ ( i + 1 ) ) C <_ %s )' % (K1, PRE('i')))
    pc0 = w.s([fz1, _cl.lift(w, ci.mem('C', 'CC'), K1), w.inst('fprodconst')], 'syl2anc',
              '( %s -> prod_ h e. ( 0 ..^ ( i + 1 ) ) C = ( C ^ ( # ` ( 0 ..^ ( i + 1 ) ) ) ) )' % K1)
    hsh = w.s([_cl.lift(w, ci.mem('( i + 1 )', 'NN0'), K1), w.inst('hashfzo0')], 'syl', '( %s -> ( # ` ( 0 ..^ ( i + 1 ) ) ) = ( i + 1 ) )' % K1)
    pc1 = w.s([pc0, w.s([hsh], 'oveq2d', '( %s -> ( C ^ ( # ` ( 0 ..^ ( i + 1 ) ) ) ) = ( C ^ ( i + 1 ) ) )' % K1)], 'eqtrd',
              '( %s -> prod_ h e. ( 0 ..^ ( i + 1 ) ) C = ( C ^ ( i + 1 ) ) )' % K1)
    case1 = w.s([pc1, pl], 'eqbrtrrd', '( %s -> ( C ^ ( i + 1 ) ) <_ %s )' % (K1, PRE('i')))
    # ---- case a < i + 1
    K2 = '( %s /\\ -. ( i + 1 ) <_ %s )' % (Gi, AG)
    K2h = '( %s /\\ h e. ( ( i + 1 ) ..^ N ) )' % K2
    hB = w.s([], 'simpr', '( %s -> h e. ( ( i + 1 ) ..^ N ) )' % K2h)
    i1uz = gi([gi([ci.mem('( i + 1 )', 'NN0'), w.inst('elnn0uz')], 'sylib', '( i + 1 ) e. ( ZZ>= ` 0 )'), w.inst('fzoss1')], 'syl',
              '( ( i + 1 ) ..^ N ) C_ ( 0 ..^ N )')
    hN2 = w.s([_cl.lift(w, i1uz, K2h), hB], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % K2h)
    c2, sh2, fsh2, bi2, er2, nx2 = node(K2h, hN2)
    c2.have('h', 'ZZ', w.s([hB, w.inst('elfzoelz')], 'syl', '( %s -> h e. ZZ )' % K2h))
    c2.have('i', 'NN0', _cl.lift(w, ci.mem('i', 'NN0'), K2h)); c2.have(AG, 'NN0', _cl.lift(w, ci.mem(AG, 'NN0'), K2h))
    nle = _cl.lift(w, w.s([], 'simpr', '( %s -> -. ( i + 1 ) <_ %s )' % (K2, AG)), K2h)
    alt = w.s([nle, ap(w, K2h, 'ltnled', '( %s < ( i + 1 ) <-> -. ( i + 1 ) <_ %s )' % (AG, AG), c2)], 'mpbird', '( %s -> %s < ( i + 1 ) )' % (K2h, AG))
    hge = w.s([hB, w.inst('elfzole1')], 'syl', '( %s -> ( i + 1 ) <_ h )' % K2h)
    nhl = lin.linarith(w, K2h, [alt, hge], '%s <_ h' % AG, closure=c2)
    nhl = w.s([nhl, ap(w, K2h, 'lenltd', '( %s <_ h <-> -. h < %s )' % (AG, AG), c2)], 'mpbid', '( %s -> -. h < %s )' % (K2h, AG))
    ning = w.s([nhl, bi2], 'mtbird', '( %s -> -. ( s ` h ) e. %s )' % (K2h, GS))
    nab = w.s([ning, er2], 'sylnib', '( %s -> -. ( ( s ` h ) e. ( 0 ..^ N ) /\\ %s ) )' % (K2h, nx2))
    ncle = w.s([nab, sh2], 'mpnanrd', '( %s -> -. %s )' % (K2h, nx2))
    flt = w.s([ncle, ap(w, K2h, 'ltnled', '( ( F ` ( s ` h ) ) < C <-> -. C <_ ( F ` ( s ` h ) ) )', c2)], 'mpbird', '( %s -> ( F ` ( s ` h ) ) < C )' % K2h)
    fle = ap(w, K2h, 'ltled', '( F ` ( s ` h ) ) <_ C', c2, facts=[flt])
    fz2 = w.s([w.s([], 'fzofi', '( ( i + 1 ) ..^ N ) e. Fin')], 'a1i', '( %s -> ( ( i + 1 ) ..^ N ) e. Fin )' % K2)
    REST = 'prod_ h e. ( ( i + 1 ) ..^ N ) ( F ` ( s ` h ) )'
    rl = w.s([w.s([], 'nfv', 'F/ h %s' % K2), fz2, c2.mem('( F ` ( s ` h ) )', 'RR'), c2.ge0('( F ` ( s ` h ) )'), c2.mem('C', 'RR'), fle], 'fprodle',
             '( %s -> %s <_ prod_ h e. ( ( i + 1 ) ..^ N ) C )' % (K2, REST))
    L2 = lambda st: _cl.lift(w, st, K2)
    ck = Closure(w, K2, {'N': ('NN0', L2(nn)), 'C': ('RR+', L2(cp)), 'i': ('NN0', L2(ci.mem('i', 'NN0')))})
    NR = '( N - ( i + 1 ) )'
    rc0 = w.s([fz2, ck.mem('C', 'CC'), w.inst('fprodconst')], 'syl2anc', '( %s -> prod_ h e. ( ( i + 1 ) ..^ N ) C = ( C ^ ( # ` ( ( i + 1 ) ..^ N ) ) ) )' % K2)
    hr = w.s([L2(nui), w.inst('hashfzo')], 'syl', '( %s -> ( # ` ( ( i + 1 ) ..^ N ) ) = %s )' % (K2, NR))
    rc1 = w.s([rc0, w.s([hr], 'oveq2d', '( %s -> ( C ^ ( # ` ( ( i + 1 ) ..^ N ) ) ) = ( C ^ %s ) )' % (K2, NR))], 'eqtrd',
              '( %s -> prod_ h e. ( ( i + 1 ) ..^ N ) C = ( C ^ %s ) )' % (K2, NR))
    rle = w.s([rl, rc1], 'breqtrd', '( %s -> %s <_ ( C ^ %s ) )' % (K2, REST, NR))
    # total product
    dsp = w.s([L2(ip1), w.inst('fzosplit')], 'syl', '( %s -> ( 0 ..^ N ) = ( ( 0 ..^ ( i + 1 ) ) u. ( ( i + 1 ) ..^ N ) ) )' % K2)
    K2x = '( %s /\\ h e. ( 0 ..^ N ) )' % K2
    cx, shx, fshx, _, _, _ = node(K2x, w.s([], 'simpr', '( %s -> h e. ( 0 ..^ N ) )' % K2x))
    TOT = 'prod_ h e. ( 0 ..^ N ) ( F ` ( s ` h ) )'
    spl = w.s([w.s([w.s([], 'fzodisj', '( ( 0 ..^ ( i + 1 ) ) i^i ( ( i + 1 ) ..^ N ) ) = (/)')], 'a1i',
                   '( %s -> ( ( 0 ..^ ( i + 1 ) ) i^i ( ( i + 1 ) ..^ N ) ) = (/) )' % K2), dsp,
               w.s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % K2), cx.mem('( F ` ( s ` h ) )', 'CC')], 'fprodsplit',
              '( %s -> %s = ( %s x. %s ) )' % (K2, TOT, PRE('i'), REST))
    # reindex the total: prod over h of F ( s h ) = prod over y of F y
    idyy = w.s([], 'id', '( v = ( s ` h ) -> v = ( s ` h ) )')
    cgy, ny = w.congr('( F ` v )', {'v': '( s ` h )'}, 'v = ( s ` h )', {'v': idyy})
    K2y = '( %s /\\ v e. ( 0 ..^ N ) )' % K2
    cy = Closure(w, K2y, {})
    fy = w.s([_cl.lift(w, ff, K2y), w.s([], 'simpr', '( %s -> v e. ( 0 ..^ N ) )' % K2y)], 'ffvelcdmd', '( %s -> ( F ` v ) e. RR+ )' % K2y)
    cy.have('( F ` v )', 'RR+', fy); cy.atom('( F ` v )')
    ri = w.s([cgy, w.s([w.s([], 'fzofi', '( 0 ..^ N ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ N ) e. Fin )' % K2), L2(Li(w.s([], 'simprl', '( %s -> %s )' % (G, SF)))),
              w.s([], 'eqidd', '( ( %s /\\ h e. ( 0 ..^ N ) ) -> ( s ` h ) = ( s ` h ) )' % K2), cy.mem('( F ` v )', 'CC')], 'fprodf1o',
             '( %s -> prod_ v e. ( 0 ..^ N ) ( F ` v ) = %s )' % (K2, TOT))
    idyv = w.s([], 'id', '( y = v -> y = v )')
    cyv, _ = w.congr('( F ` y )', {'y': 'v'}, 'y = v', {'y': idyv})
    cbp = w.s([cyv], 'cbvprodv', 'prod_ y e. ( 0 ..^ N ) ( F ` y ) = prod_ v e. ( 0 ..^ N ) ( F ` v )')
    ri = w.s([w.s([cbp], 'a1i', '( %s -> prod_ y e. ( 0 ..^ N ) ( F ` y ) = prod_ v e. ( 0 ..^ N ) ( F ` v ) )' % K2), ri], 'eqtrd', '( %s -> prod_ y e. ( 0 ..^ N ) ( F ` y ) = %s )' % (K2, TOT))
    tge = w.s([L2(hy), ri], 'breqtrd', '( %s -> ( C ^ N ) <_ %s )' % (K2, TOT))
    tge = w.s([tge, spl], 'breqtrd', '( %s -> ( C ^ N ) <_ ( %s x. %s ) )' % (K2, PRE('i'), REST))
    K2p = '( %s /\\ h e. ( 0 ..^ ( i + 1 ) ) )' % K2
    sub2 = L2(gi([nui, w.inst('fzoss2')], 'syl', '( 0 ..^ ( i + 1 ) ) C_ ( 0 ..^ N )'))
    cp_, _, _, _, _, _ = node(K2p, w.s([_cl.lift(w, sub2, K2p), w.s([], 'simpr', '( %s -> h e. ( 0 ..^ ( i + 1 ) ) )' % K2p)], 'sseldd', '( %s -> h e. ( 0 ..^ N ) )' % K2p))
    fzp = w.s([w.s([], 'fzofi', '( 0 ..^ ( i + 1 ) ) e. Fin')], 'a1i', '( %s -> ( 0 ..^ ( i + 1 ) ) e. Fin )' % K2)
    pr = w.s([fzp, cp_.mem('( F ` ( s ` h ) )', 'RR+')], 'fprodrpcl', '( %s -> %s e. RR+ )' % (K2, PRE('i')))
    ck.have(PRE('i'), 'RR+', pr); ck.atom(PRE('i'))
    cr = Closure(w, K2h, {})
    rr = w.s([fz2, c2.mem('( F ` ( s ` h ) )', 'RR+')], 'fprodrpcl', '( %s -> %s e. RR+ )' % (K2, REST))
    ck.have(REST, 'RR+', rr); ck.atom(REST)
    CR = '( C ^ %s )' % NR
    nr0 = w.s([L2(nui), w.inst('uznn0sub')], 'syl', '( %s -> %s e. NN0 )' % (K2, NR))
    ck.have(NR, 'NN0', nr0)
    ck.atom(CR); ck.have(CR, 'RR+', ck.mem(CR, 'RR+'))
    m1 = ap(w, K2, 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (PRE('i'), REST, PRE('i'), CR), ck, facts=[rle])
    ex = ap(w, K2, 'expaddd', '( C ^ ( ( i + 1 ) + %s ) ) = ( ( C ^ ( i + 1 ) ) x. %s )' % (NR, CR), ck)
    pn = ap(w, K2, 'pncan3d', '( ( i + 1 ) + %s ) = N' % NR, ck)
    ex2 = w.s([w.s([pn], 'oveq2d', '( %s -> ( C ^ ( ( i + 1 ) + %s ) ) = ( C ^ N ) )' % (K2, NR)), ex], 'eqtr3d', '( %s -> ( C ^ N ) = ( ( C ^ ( i + 1 ) ) x. %s ) )' % (K2, CR))
    m2 = w.s([ex2, w.s([tge, m1], 'letrd', '( %s -> ( C ^ N ) <_ ( %s x. %s ) )' % (K2, PRE('i'), CR))], 'eqbrtrrd',
             '( %s -> ( ( C ^ ( i + 1 ) ) x. %s ) <_ ( %s x. %s ) )' % (K2, CR, PRE('i'), CR))
    ck.atom('( C ^ ( i + 1 ) )')
    m3 = ap(w, K2, 'lemul1d', '( ( C ^ ( i + 1 ) ) <_ %s <-> ( ( C ^ ( i + 1 ) ) x. %s ) <_ ( %s x. %s ) )' % (PRE('i'), CR, PRE('i'), CR), ck)
    case2 = w.s([m2, m3], 'mpbird', '( %s -> ( C ^ ( i + 1 ) ) <_ %s )' % (K2, PRE('i')))
    both = w.s([case1, case2], 'pm2.61dan', '( %s -> ( C ^ ( i + 1 ) ) <_ %s )' % (Gi, PRE('i')))
    alli = w.s([both], 'ralrimiva', '( %s -> %s )' % (G, ALLI))
    pair = w.s([w.s([], 'simprl', '( %s -> %s )' % (G, SF)), alli], 'jca', '( %s -> ( %s /\\ %s ) )' % (G, SF, ALLI))
    pi_ = w.s([pair], 'ex', '( %s -> ( ( %s /\\ %s ) -> ( %s /\\ %s ) ) )' % (A, SF, ALLZ, SF, ALLI))
    pj = s([s([anb], 'a1i', '( ( %s /\\ %s ) <-> ( %s /\\ %s ) )' % (SF, ALLH, SF, ALLZ)), pi_], 'sylbid', '( ( %s /\\ %s ) -> ( %s /\\ %s ) )' % (SF, ALLH, SF, ALLI))
    pk = s([pj], 'eximdv', '( E. s ( %s /\\ %s ) -> E. s ( %s /\\ %s ) )' % (SF, ALLH, SF, ALLI))
    w.qed([o1, pk], 'mpd', S['tpord'])
    return run(w)


if __name__ == '__main__':
    gen_ord1()
    gen_ord()
