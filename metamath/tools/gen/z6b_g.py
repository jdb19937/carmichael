"""Sortie Z6b, section 3: Goursat with two continuity-only points (z6gour2) and Cauchy's formula with one extra
continuity-only point (z6cau2).

z6gsub    a sub-rectangle avoiding Q (set theory, ssdifpr)
z6gour2h  Re P < Re Q: cut at x = ( Re P + Re Q ) / 2 (rectinthspx), rectintgour1 on each half
z6gour2v  Im P < Im Q: cut at y = ( Im P + Im Q ) / 2 (rectintvspx)
z6gour2a  either
z6cneq    P =/= Q differ in Re or Im, in one of the two orders
z6gour2   the case split (P = Q: rectintgour1; else z6gour2a in one of the two orders)
z6cau2    rectintcau's worksheet with rectintgour1 replaced by z6gour2
Run: MM_DB=sorties/z6b.mm LIN_FAST=1 python3 tools/gen/z6b_g.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z6blib import *
from tm import sub
from cl import split_imp
from z6a_e3 import conjs, build, apply, unpack, c_
import lin

only = sys.argv[1:]


def want(lab):
    return not only or lab in only


def z6gsub():
    w = W('z6gsub', 'A subset ` X ` of ` Y ` that avoids ` Q ` loses at most ` P ` against ` Y \\ { P , Q } ` (~ ssdifpr ).')
    a = ante('z6gsub'); st = mkst(w, a)
    xy = st([], 'simpl', 'X C_ Y'); nq = st([], 'simpr', '-. Q e. X')
    s1 = st([xy], 'ssdifd', '( X \\ { P } ) C_ ( Y \\ { P } )')
    xyq = st([st([xy, nq], 'jca', '( X C_ Y /\\ -. Q e. X )'), c_(w, a, w.s([], 'ssdifsn', '( X C_ ( Y \\ { Q } ) <-> ( X C_ Y /\\ -. Q e. X ) )'),
                                                                       '( X C_ ( Y \\ { Q } ) <-> ( X C_ Y /\\ -. Q e. X ) )')], 'mpbird', 'X C_ ( Y \\ { Q } )')
    s2 = st([c_(w, a, w.s([], 'difss', '( X \\ { P } ) C_ X'), '( X \\ { P } ) C_ X'), xyq], 'sstrd', '( X \\ { P } ) C_ ( Y \\ { Q } )')
    w.qed([st([s1, s2], 'jca', '( ( X \\ { P } ) C_ ( Y \\ { P } ) /\\ ( X \\ { P } ) C_ ( Y \\ { Q } ) )'), w.inst('ssdifpr')], 'syl', STATEMENTS['z6gsub'])
    return w


def cpt(w, a, st, xr, yr, X, Y):
    """( a -> ( X + ( _i x. Y ) ) e. CC ) from X, Y real"""
    ic = c_(w, a, w.s([], 'ax-icn', '_i e. CC'), '_i e. CC')
    iy = st([ic, st([yr], 'recnd', '%s e. CC' % Y)], 'mulcld', '( _i x. %s ) e. CC' % Y)
    return st([st([xr], 'recnd', '%s e. CC' % X), iy], 'addcld', '( %s + ( _i x. %s ) ) e. CC' % (X, Y))


def gour2hv(kind):
    """z6gour2h (kind 'h', cut Re = x) or z6gour2v (kind 'v', cut Im = y)"""
    lab = 'z6gour2' + kind
    Rk, Ik = ('Re', 'Im') if kind == 'h' else ('Im', 'Re')
    w = W(lab, 'Goursat on a rectangle with two continuity-only interior points ` P ` , ` Q ` with ` %s P < %s Q ` : cut the rectangle at '
          '` %s = ( %s P + %s Q ) / 2 ` (~ %s ) and apply ~ rectintgour1 to each half, which holds one of the points.'
          % (Rk, Rk, Rk, Rk, Rk, 'rectinthspx' if kind == 'h' else 'rectintvspx'))
    a = ante(lab); f = unpack(w, a); st = mkst(w, a)
    ac = f['A e. CC']; bc = f['B e. CC']; pc = f['P e. CC']; qc = f['Q e. CC']
    fcn = f['F e. ( D -cn-> CC )']; rd = f['( A crect B ) C_ D']; rdom = f['( ( A crect B ) \\ { P , Q } ) C_ dom ( CC _D F )']
    re = {}
    for Z, zc in (('A', ac), ('B', bc), ('P', pc), ('Q', qc)):
        re[('Re', Z)] = st([zc], 'recld', '( Re ` %s ) e. RR' % Z)
        re[('Im', Z)] = st([zc], 'imcld', '( Im ` %s ) e. RR' % Z)
    R = lambda k, Z: '( %s ` %s )' % (k, Z)
    lt = lambda x, y: f['%s < %s' % (x, y)]
    # the strict interiority facts, keyed (k, lo, hi)
    for Z in ('P', 'Q'):
        for k in ('Re', 'Im'):
            f[(k, 'A', Z)] = lt(R(k, 'A'), R(k, Z)); f[(k, Z, 'B')] = lt(R(k, Z), R(k, 'B'))
    pq = f['%s < %s' % (R(Rk, 'P'), R(Rk, 'Q'))]
    X = '( ( %s + %s ) / 2 )' % (R(Rk, 'P'), R(Rk, 'Q'))
    xr = st([st([re[(Rk, 'P')], re[(Rk, 'Q')]], 'readdcld', '( %s + %s ) e. RR' % (R(Rk, 'P'), R(Rk, 'Q')))], 'rehalfcld', '%s e. RR' % X)
    px = st([pq, st([re[(Rk, 'P')], re[(Rk, 'Q')], w.inst('avglt1')], 'syl2anc', '( %s < %s <-> %s < %s )' % (R(Rk, 'P'), R(Rk, 'Q'), R(Rk, 'P'), X))], 'mpbid',
            '%s < %s' % (R(Rk, 'P'), X))
    xq = st([pq, st([re[(Rk, 'P')], re[(Rk, 'Q')], w.inst('avglt2')], 'syl2anc', '( %s < %s <-> %s < %s )' % (R(Rk, 'P'), R(Rk, 'Q'), X, R(Rk, 'Q')))], 'mpbid',
            '%s < %s' % (X, R(Rk, 'Q')))
    ax = st([f[(Rk, 'A', 'P')], px], 'lttrd', '%s < %s' % (R(Rk, 'A'), X))
    xb = st([xq, f[(Rk, 'Q', 'B')]], 'lttrd', '%s < %s' % (X, R(Rk, 'B')))
    ab = {}
    for k in ('Re', 'Im'):
        ab[k] = st([f[(k, 'A', 'P')], f[(k, 'P', 'B')]], 'lttrd', '%s < %s' % (R(k, 'A'), R(k, 'B')))
    abl = {k: st([ab[k]], 'ltled', '%s <_ %s' % (R(k, 'A'), R(k, 'B'))) for k in ('Re', 'Im')}
    geo = st([abl['Re'], abl['Im']], 'jca', '( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) )')
    xab = st([xr, st([ax], 'ltled', '%s <_ %s' % (R(Rk, 'A'), X)), st([xb], 'ltled', '%s <_ %s' % (X, R(Rk, 'B'))),
              st([re[(Rk, 'A')], re[(Rk, 'B')], w.inst('elicc2')], 'syl2anc',
                 '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (X, R(Rk, 'A'), R(Rk, 'B'), X, R(Rk, 'A'), X, X, R(Rk, 'B')))],
             'mpbir3and', '%s e. ( %s [,] %s )' % (X, R(Rk, 'A'), R(Rk, 'B')))
    abcc = st([ac, bc], 'jca', '( A e. CC /\\ B e. CC )')
    fd = st([fcn, rd], 'jca', '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D )')
    if kind == 'h':
        B1 = '( %s + ( _i x. ( Im ` B ) ) )' % X; A2 = '( %s + ( _i x. ( Im ` A ) ) )' % X
        b1c = cpt(w, a, st, xr, re[('Im', 'B')], X, '( Im ` B )'); a2c = cpt(w, a, st, xr, re[('Im', 'A')], X, '( Im ` A )')
        rb1 = st([xr, re[('Im', 'B')]], 'crred', '( Re ` %s ) = %s' % (B1, X)); ib1 = st([xr, re[('Im', 'B')]], 'crimd', '( Im ` %s ) = ( Im ` B )' % B1)
        ra2 = st([xr, re[('Im', 'A')]], 'crred', '( Re ` %s ) = %s' % (A2, X)); ia2 = st([xr, re[('Im', 'A')]], 'crimd', '( Im ` %s ) = ( Im ` A )' % A2)
        cut = 'rectinthspx'
    else:
        B1 = '( ( Re ` B ) + ( _i x. %s ) )' % X; A2 = '( ( Re ` A ) + ( _i x. %s ) )' % X
        b1c = cpt(w, a, st, re[('Re', 'B')], xr, '( Re ` B )', X); a2c = cpt(w, a, st, re[('Re', 'A')], xr, '( Re ` A )', X)
        rb1 = st([re[('Re', 'B')], xr], 'crred', '( Re ` %s ) = ( Re ` B )' % B1); ib1 = st([re[('Re', 'B')], xr], 'crimd', '( Im ` %s ) = %s' % (B1, X))
        ra2 = st([re[('Re', 'A')], xr], 'crred', '( Re ` %s ) = ( Re ` A )' % A2); ia2 = st([re[('Re', 'A')], xr], 'crimd', '( Im ` %s ) = %s' % (A2, X))
        cut = 'rectintvspx'
    RIa = '( F rectint <. A , %s >. )' % B1; RIb = '( F rectint <. %s , B >. )' % A2
    SPH = ('( ( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) ) /\\ '
           '%s < %s /\\ %s e. ( %s [,] %s ) )' % (R(Rk, 'A'), R(Rk, 'B'), X, R(Rk, 'A'), R(Rk, 'B')))
    h3 = st([abcc, geo, fd], '3jca', '( ( A e. CC /\\ B e. CC ) /\\ ( ( Re ` A ) <_ ( Re ` B ) /\\ ( Im ` A ) <_ ( Im ` B ) ) /\\ '
                                     '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D ) )')
    split = st([st([h3, ab[Rk], xab], '3jca', SPH), w.inst(cut)], 'syl', '( F rectint <. A , B >. ) = ( %s + %s )' % (RIa, RIb))
    # values of the new corners: ( k B1 ) = VB[k], ( k A2 ) = VA[k]
    eqB1 = {'Re': rb1, 'Im': ib1}; eqA2 = {'Re': ra2, 'Im': ia2}
    VB = {k: (X if k == Rk else R(k, 'B')) for k in ('Re', 'Im')}
    VA = {k: (X if k == Rk else R(k, 'A')) for k in ('Re', 'Im')}
    # left half: P inside ( A crect B1 )
    qpl = {}
    for k in ('Re', 'Im'):
        up = px if k == Rk else f[(k, 'P', 'B')]
        qpl[k] = st([f[(k, 'A', 'P')], st([up, eqB1[k]], 'breqtrrd', '%s < ( %s ` %s )' % (R(k, 'P'), k, B1))], 'jca',
                    '( %s < %s /\\ %s < ( %s ` %s ) )' % (R(k, 'A'), R(k, 'P'), R(k, 'P'), k, B1))
    QPL = '( ( ( Re ` A ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` %s ) ) /\\ ( ( Im ` A ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` %s ) ) )' % (B1, B1)
    qpl_ = st([qpl['Re'], qpl['Im']], 'jca', QPL)
    # right half: Q inside ( A2 crect B )
    qpr = {}
    for k in ('Re', 'Im'):
        lo = xq if k == Rk else f[(k, 'A', 'Q')]
        qpr[k] = st([st([eqA2[k], lo], 'eqbrtrd', '( %s ` %s ) < %s' % (k, A2, R(k, 'Q'))), f[(k, 'Q', 'B')]], 'jca',
                    '( ( %s ` %s ) < %s /\\ %s < %s )' % (k, A2, R(k, 'Q'), R(k, 'Q'), R(k, 'B')))
    QPR = '( ( ( Re ` %s ) < ( Re ` Q ) /\\ ( Re ` Q ) < ( Re ` B ) ) /\\ ( ( Im ` %s ) < ( Im ` Q ) /\\ ( Im ` Q ) < ( Im ` B ) ) )' % (A2, A2)
    qpr_ = st([qpr['Re'], qpr['Im']], 'jca', QPR)
    # sub-rectangles
    lel = {}; ler = {}
    for k in ('Re', 'Im'):
        vb = st([xb], 'ltled', '%s <_ %s' % (X, R(k, 'B'))) if k == Rk else st([re[(k, 'B')]], 'leidd', '%s <_ %s' % (R(k, 'B'), R(k, 'B')))
        lel[k] = st([st([re[(k, 'A')]], 'leidd', '%s <_ %s' % (R(k, 'A'), R(k, 'A'))), st([eqB1[k], vb], 'eqbrtrd', '( %s ` %s ) <_ %s' % (k, B1, R(k, 'B')))],
                    'jca', '( %s <_ %s /\\ ( %s ` %s ) <_ %s )' % (R(k, 'A'), R(k, 'A'), k, B1, R(k, 'B')))
        va = st([ax], 'ltled', '%s <_ %s' % (R(k, 'A'), X)) if k == Rk else st([re[(k, 'A')]], 'leidd', '%s <_ %s' % (R(k, 'A'), R(k, 'A')))
        ler[k] = st([st([va, eqA2[k]], 'breqtrrd', '%s <_ ( %s ` %s )' % (R(k, 'A'), k, A2)), st([re[(k, 'B')]], 'leidd', '%s <_ %s' % (R(k, 'B'), R(k, 'B')))],
                    'jca', '( %s <_ ( %s ` %s ) /\\ %s <_ %s )' % (R(k, 'A'), k, A2, R(k, 'B'), R(k, 'B')))
    R1 = '( A crect %s )' % B1; R2 = '( %s crect B )' % A2
    ssl = st([abcc, st([ac, b1c], 'jca', '( A e. CC /\\ %s e. CC )' % B1),
              st([lel['Re'], lel['Im']], 'jca', '( ( ( Re ` A ) <_ ( Re ` A ) /\\ ( Re ` %s ) <_ ( Re ` B ) ) /\\ ( ( Im ` A ) <_ ( Im ` A ) /\\ ( Im ` %s ) <_ ( Im ` B ) ) )' % (B1, B1)),
              w.inst('crectss2')], 'syl3anc', '%s C_ ( A crect B )' % R1)
    ssr = st([abcc, st([a2c, bc], 'jca', '( %s e. CC /\\ B e. CC )' % A2),
              st([ler['Re'], ler['Im']], 'jca', '( ( ( Re ` A ) <_ ( Re ` %s ) /\\ ( Re ` B ) <_ ( Re ` B ) ) /\\ ( ( Im ` A ) <_ ( Im ` %s ) /\\ ( Im ` B ) <_ ( Im ` B ) ) )' % (A2, A2)),
              w.inst('crectss2')], 'syl3anc', '%s C_ ( A crect B )' % R2)
    # the other point lies outside
    def outside(Z, C, E, cc, ec, bound, eqk, isub):
        """( a -> -. Z e. ( C crect E ) ); bound: ( a -> strict inequality ) contradicting the membership in the Rk coordinate"""
        RC = '( %s crect %s )' % (C, E)
        az = '( %s /\\ %s e. %s )' % (a, Z, RC); sz = mkst(w, az)
        zin = sz([], 'simpr', '%s e. %s' % (Z, RC))
        el = sz([c_(w, az, cc, '%s e. CC' % C) if False else w.s([cc], 'adantr', '( %s -> %s e. CC )' % (az, C)),
                 w.s([ec], 'adantr', '( %s -> %s e. CC )' % (az, E)), w.inst('elcrect')], 'syl2anc',
                '( %s e. %s <-> ( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) ) )'
                % (Z, RC, Z, Z, C, E, Z, C, E))
        m3 = sz([zin, el], 'mpbid', '( %s e. CC /\\ ( Re ` %s ) e. ( ( Re ` %s ) [,] ( Re ` %s ) ) /\\ ( Im ` %s ) e. ( ( Im ` %s ) [,] ( Im ` %s ) ) )'
                % (Z, Z, C, E, Z, C, E))
        ivl = sz([m3], 'simp2d' if Rk == 'Re' else 'simp3d', '( %s ` %s ) e. ( ( %s ` %s ) [,] ( %s ` %s ) )' % (Rk, Z, Rk, C, Rk, E))
        cr = sz([w.s([cc], 'adantr', '( %s -> %s e. CC )' % (az, C))], 'recld' if Rk == 'Re' else 'imcld', '( %s ` %s ) e. RR' % (Rk, C))
        er = sz([w.s([ec], 'adantr', '( %s -> %s e. CC )' % (az, E))], 'recld' if Rk == 'Re' else 'imcld', '( %s ` %s ) e. RR' % (Rk, E))
        if isub:   # Z <_ ( Rk E )
            le = sz([sz([cr], 'rexrd', '( %s ` %s ) e. RR*' % (Rk, C)), sz([er], 'rexrd', '( %s ` %s ) e. RR*' % (Rk, E)), ivl, w.inst('iccleub')], 'syl3anc',
                    '( %s ` %s ) <_ ( %s ` %s )' % (Rk, Z, Rk, E))
            imp = w.s([le], 'ex', '( %s -> ( %s e. %s -> ( %s ` %s ) <_ ( %s ` %s ) ) )' % (a, Z, RC, Rk, Z, Rk, E))
            gt = st([eqk, bound], 'eqbrtrd', '( %s ` %s ) < ( %s ` %s )' % (Rk, E, Rk, Z))
            ng = st([gt, st([st([ec], 'recld' if Rk == 'Re' else 'imcld', '( %s ` %s ) e. RR' % (Rk, E)), re[(Rk, Z)]], 'ltnled',
                             '( ( %s ` %s ) < ( %s ` %s ) <-> -. ( %s ` %s ) <_ ( %s ` %s ) )' % (Rk, E, Rk, Z, Rk, Z, Rk, E))], 'mpbid',
                    '-. ( %s ` %s ) <_ ( %s ` %s )' % (Rk, Z, Rk, E))
        else:      # ( Rk C ) <_ Z
            le = sz([sz([cr], 'rexrd', '( %s ` %s ) e. RR*' % (Rk, C)), sz([er], 'rexrd', '( %s ` %s ) e. RR*' % (Rk, E)), ivl, w.inst('iccgelb')], 'syl3anc',
                    '( %s ` %s ) <_ ( %s ` %s )' % (Rk, C, Rk, Z))
            imp = w.s([le], 'ex', '( %s -> ( %s e. %s -> ( %s ` %s ) <_ ( %s ` %s ) ) )' % (a, Z, RC, Rk, C, Rk, Z))
            gt = st([bound, eqk], 'breqtrrd', '( %s ` %s ) < ( %s ` %s )' % (Rk, Z, Rk, C))
            ng = st([gt, st([re[(Rk, Z)], st([cc], 'recld' if Rk == 'Re' else 'imcld', '( %s ` %s ) e. RR' % (Rk, C))], 'ltnled',
                             '( ( %s ` %s ) < ( %s ` %s ) <-> -. ( %s ` %s ) <_ ( %s ` %s ) )' % (Rk, Z, Rk, C, Rk, C, Rk, Z))], 'mpbid',
                    '-. ( %s ` %s ) <_ ( %s ` %s )' % (Rk, C, Rk, Z))
        return st([ng, imp], 'mtod', '-. %s e. %s' % (Z, RC))
    qout = outside('Q', 'A', B1, ac, b1c, xq, eqB1[Rk], True)
    pout = outside('P', A2, 'B', a2c, bc, px, eqA2[Rk], False)
    dl = st([st([ssl, qout], 'jca', '( %s C_ ( A crect B ) /\\ -. Q e. %s )' % (R1, R1)), w.inst('z6gsub')], 'syl',
            '( %s \\ { P } ) C_ ( ( A crect B ) \\ { P , Q } )' % R1)
    dr0 = st([st([ssr, pout], 'jca', '( %s C_ ( A crect B ) /\\ -. P e. %s )' % (R2, R2)), w.inst('z6gsub')], 'syl',
             '( %s \\ { Q } ) C_ ( ( A crect B ) \\ { Q , P } )' % R2)
    pqc = c_(w, a, w.s([w.s([], 'prcom', '{ Q , P } = { P , Q }')], 'difeq2i', '( ( A crect B ) \\ { Q , P } ) = ( ( A crect B ) \\ { P , Q } )'),
             '( ( A crect B ) \\ { Q , P } ) = ( ( A crect B ) \\ { P , Q } )')
    dr = st([dr0, pqc], 'sseqtrd', '( %s \\ { Q } ) C_ ( ( A crect B ) \\ { P , Q } )' % R2)
    gl = st([st([ac, b1c], 'jca', '( A e. CC /\\ %s e. CC )' % B1), st([pc, qpl_], 'jca', '( P e. CC /\\ %s )' % QPL),
             st([fcn, st([ssl, rd], 'sstrd', '%s C_ D' % R1), st([dl, rdom], 'sstrd', '( %s \\ { P } ) C_ dom ( CC _D F )' % R1)], '3jca',
                '( F e. ( D -cn-> CC ) /\\ %s C_ D /\\ ( %s \\ { P } ) C_ dom ( CC _D F ) )' % (R1, R1)), w.inst('rectintgour1')], 'syl3anc', '%s = 0' % RIa)
    gr = st([st([a2c, bc], 'jca', '( %s e. CC /\\ B e. CC )' % A2), st([qc, qpr_], 'jca', '( Q e. CC /\\ %s )' % QPR),
             st([fcn, st([ssr, rd], 'sstrd', '%s C_ D' % R2), st([dr, rdom], 'sstrd', '( %s \\ { Q } ) C_ dom ( CC _D F )' % R2)], '3jca',
                '( F e. ( D -cn-> CC ) /\\ %s C_ D /\\ ( %s \\ { Q } ) C_ dom ( CC _D F ) )' % (R2, R2)), w.inst('rectintgour1')], 'syl3anc', '%s = 0' % RIb)
    s00 = st([split, st([gl, gr], 'oveq12d', '( %s + %s ) = ( 0 + 0 )' % (RIa, RIb))], 'eqtrd', '( F rectint <. A , B >. ) = ( 0 + 0 )')
    w.qed([s00, c_(w, a, w.s([], '00id', '( 0 + 0 ) = 0'), '( 0 + 0 ) = 0')], 'eqtrd', STATEMENTS[lab])
    return w


def z6gour2h():
    return gour2hv('h')


def z6gour2v():
    return gour2hv('v')


def z6gour2a():
    w = W('z6gour2a', 'Goursat with two continuity-only interior points that differ in the real or the imaginary part in the stated order '
          '(~ z6gour2h , ~ z6gour2v ).')
    h = w.s([], 'z6gour2h', STATEMENTS['z6gour2h']); v = w.s([], 'z6gour2v', STATEMENTS['z6gour2v'])
    w.qed([h, v], 'jaodan', STATEMENTS['z6gour2a'])
    return w


def z6cneq():
    w = W('z6cneq', 'Two distinct complex numbers differ in the real or in the imaginary part, in one of the two orders (~ replim , ~ lttri2 ).')
    a = ante('z6cneq'); st = mkst(w, a)
    pc = st([], 'simpll', 'P e. CC'); qc = st([], 'simplr', 'Q e. CC'); ne = st([], 'simpr', 'P =/= Q')
    EQ = '( ( Re ` P ) = ( Re ` Q ) /\\ ( Im ` P ) = ( Im ` Q ) )'
    b = '( %s /\\ %s )' % (a, EQ); sb = mkst(w, b)
    re_ = sb([], 'simprl', '( Re ` P ) = ( Re ` Q )'); im_ = sb([], 'simprr', '( Im ` P ) = ( Im ` Q )')
    PQ = lambda Z: '( ( Re ` %s ) + ( _i x. ( Im ` %s ) ) )' % (Z, Z)
    e1 = sb([re_, sb([im_], 'oveq2d', '( _i x. ( Im ` P ) ) = ( _i x. ( Im ` Q ) )')], 'oveq12d', '%s = %s' % (PQ('P'), PQ('Q')))
    rp = sb([w.s([pc], 'adantr', '( %s -> P e. CC )' % b)], 'replimd', 'P = %s' % PQ('P'))
    rq = sb([w.s([qc], 'adantr', '( %s -> Q e. CC )' % b)], 'replimd', 'Q = %s' % PQ('Q'))
    pq = sb([sb([rp, e1], 'eqtrd', 'P = %s' % PQ('Q')), rq], 'eqtr4d', 'P = Q')
    imp = w.s([pq], 'ex', '( %s -> ( %s -> P = Q ) )' % (a, EQ))
    nn = st([ne], 'neneqd', '-. P = Q')
    nq = st([nn, imp], 'mtod', '-. %s' % EQ)
    io = st([nq, c_(w, a, w.s([], 'ianor', '( -. %s <-> ( -. ( Re ` P ) = ( Re ` Q ) \\/ -. ( Im ` P ) = ( Im ` Q ) ) )' % EQ),
                    '( -. %s <-> ( -. ( Re ` P ) = ( Re ` Q ) \\/ -. ( Im ` P ) = ( Im ` Q ) ) )' % EQ)], 'mpbid',
            '( -. ( Re ` P ) = ( Re ` Q ) \\/ -. ( Im ` P ) = ( Im ` Q ) )')
    dn = w.s([w.s([], 'df-ne', '( ( Re ` P ) =/= ( Re ` Q ) <-> -. ( Re ` P ) = ( Re ` Q ) )'), w.s([], 'df-ne', '( ( Im ` P ) =/= ( Im ` Q ) <-> -. ( Im ` P ) = ( Im ` Q ) )')],
             'orbi12i', '( ( ( Re ` P ) =/= ( Re ` Q ) \\/ ( Im ` P ) =/= ( Im ` Q ) ) <-> ( -. ( Re ` P ) = ( Re ` Q ) \\/ -. ( Im ` P ) = ( Im ` Q ) ) )')
    nd = st([io, c_(w, a, dn, '( ( ( Re ` P ) =/= ( Re ` Q ) \\/ ( Im ` P ) =/= ( Im ` Q ) ) <-> ( -. ( Re ` P ) = ( Re ` Q ) \\/ -. ( Im ` P ) = ( Im ` Q ) ) )')],
            'mpbird', '( ( Re ` P ) =/= ( Re ` Q ) \\/ ( Im ` P ) =/= ( Im ` Q ) )')
    rpr = st([pc], 'recld', '( Re ` P ) e. RR'); rqr = st([qc], 'recld', '( Re ` Q ) e. RR')
    ipr = st([pc], 'imcld', '( Im ` P ) e. RR'); iqr = st([qc], 'imcld', '( Im ` Q ) e. RR')
    l1 = st([rpr, rqr, w.inst('lttri2')], 'syl2anc', '( ( Re ` P ) =/= ( Re ` Q ) <-> ( ( Re ` P ) < ( Re ` Q ) \\/ ( Re ` Q ) < ( Re ` P ) ) )')
    l2 = st([ipr, iqr, w.inst('lttri2')], 'syl2anc', '( ( Im ` P ) =/= ( Im ` Q ) <-> ( ( Im ` P ) < ( Im ` Q ) \\/ ( Im ` Q ) < ( Im ` P ) ) )')
    O4 = '( ( ( Re ` P ) < ( Re ` Q ) \\/ ( Re ` Q ) < ( Re ` P ) ) \\/ ( ( Im ` P ) < ( Im ` Q ) \\/ ( Im ` Q ) < ( Im ` P ) ) )'
    l12 = st([l1, l2], 'orbi12d', '( ( ( Re ` P ) =/= ( Re ` Q ) \\/ ( Im ` P ) =/= ( Im ` Q ) ) <-> %s )' % O4)
    o4 = st([nd, l12], 'mpbid', O4)
    cn = split_imp(STATEMENTS['z6cneq'])[1]
    w.qed([o4, c_(w, a, w.s([], 'or4', '( %s <-> %s )' % (O4, cn)), '( %s <-> %s )' % (O4, cn))], 'mpbid', STATEMENTS['z6cneq'])
    return w


def z6gour2():
    w = W('z6gour2', 'Cauchy-Goursat for a rectangle with two continuity-only interior points ` P ` , ` Q ` : for ` P = Q ` this is ~ rectintgour1 ; '
          'otherwise the points differ in one coordinate (~ z6cneq ) and ~ z6gour2a applies in one of the two orders.')
    a = ante('z6gour2'); st = mkst(w, a)
    RI = '( F rectint <. A , B >. ) = 0'
    # P = Q
    c1 = '( %s /\\ P = Q )' % a; f1 = unpack(w, c1); s1 = mkst(w, c1)
    qp = s1([f1['P = Q']], 'eqcomd', 'Q = P')
    pr = s1([s1([qp], 'preq2d', '{ P , Q } = { P , P }'), c_(w, c1, w.s([], 'dfsn2', '{ P } = { P , P }'), '{ P } = { P , P }')], 'eqtr4d', '{ P , Q } = { P }')
    dd = s1([pr], 'difeq2d', '( ( A crect B ) \\ { P , Q } ) = ( ( A crect B ) \\ { P } )')
    dom1 = s1([dd, f1['( ( A crect B ) \\ { P , Q } ) C_ dom ( CC _D F )']], 'eqsstrrd', '( ( A crect B ) \\ { P } ) C_ dom ( CC _D F )')
    f1['( ( A crect B ) \\ { P } ) C_ dom ( CC _D F )'] = dom1
    g1, _ = applyn(w, c1, 'rectintgour1', {}, f1)
    e1 = w.s([g1], 'ex', '( %s -> ( P = Q -> %s ) )' % (a, RI))
    # P =/= Q
    c2 = '( %s /\\ P =/= Q )' % a; f2 = unpack(w, c2); s2 = mkst(w, c2)
    dis, _ = applyn(w, c2, 'z6cneq', {}, f2)
    D1 = '( ( Re ` P ) < ( Re ` Q ) \\/ ( Im ` P ) < ( Im ` Q ) )'; D2 = '( ( Re ` Q ) < ( Re ` P ) \\/ ( Im ` Q ) < ( Im ` P ) )'
    ga = w.s([], 'z6gour2a', STATEMENTS['z6gour2a'])
    h1 = w.s([w.s([ga], 'ex', '( %s -> ( %s -> %s ) )' % (a, D1, RI))], 'adantr', '( %s -> ( %s -> %s ) )' % (c2, D1, RI))
    swp = {'P': 'Q', 'Q': 'P'}
    A2s = sub(split_imp(STATEMENTS['z6gour2a'])[0], swp)       # ( ANT2' /\\ D2 )
    ANT2s = sub(ANT2, swp)
    qpc = c_(w, c2, w.s([w.s([], 'prcom', '{ Q , P } = { P , Q }')], 'difeq2i', '( ( A crect B ) \\ { Q , P } ) = ( ( A crect B ) \\ { P , Q } )'),
             '( ( A crect B ) \\ { Q , P } ) = ( ( A crect B ) \\ { P , Q } )')
    f2['( ( A crect B ) \\ { Q , P } ) C_ dom ( CC _D F )'] = s2([qpc, f2['( ( A crect B ) \\ { P , Q } ) C_ dom ( CC _D F )']], 'eqsstrd',
                                                                  '( ( A crect B ) \\ { Q , P } ) C_ dom ( CC _D F )')
    ants = build(w, c2, ANT2s, f2)
    gs = w.s([], 'z6gour2a', sub(STATEMENTS['z6gour2a'], swp))
    h2 = s2([ants, w.s([gs], 'ex', '( %s -> ( %s -> %s ) )' % (ANT2s, D2, RI))], 'syl', '( %s -> %s )' % (D2, RI))
    g2 = s2([dis, s2([h1, h2], 'jaod', '( ( %s \\/ %s ) -> %s )' % (D1, D2, RI))], 'mpd', RI)
    e2 = w.s([g2], 'ex', '( %s -> ( P =/= Q -> %s ) )' % (a, RI))
    w.qed([e1, e2], 'pm2.61dne', STATEMENTS['z6gour2'])
    return w


def z6cau2():
    """rectintcau's worksheet, transformed"""
    import mm as MM
    src = open(os.path.join(MM.WSDIR, 'rectintcau.mmp')).read().split('\n')
    OA = '( ( A e. CC /\\ B e. CC ) /\\ ( P e. CC /\\ %s ) /\\ ( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ dom ( CC _D F ) ) )' % QPX('P')
    NA = split_imp(STATEMENTS['z6cau2'])[0]
    F3 = '( F e. ( D -cn-> CC ) /\\ ( A crect B ) C_ D /\\ ( ( A crect B ) \\ { Q } ) C_ dom ( CC _D F ) )'
    PQS = '( ( P e. CC /\\ %s ) /\\ ( Q e. CC /\\ %s ) )' % (QPX('P'), QPX('Q'))
    out = []
    body = [l for l in src]
    # join continuation lines: each step starts at column 0 with a label; the file keeps one step per line
    for l in body:
        if l.startswith('$( <MM>'):
            out.append(l.replace('THEOREM=rectintcau', 'THEOREM=z6cau2')); continue
        if l.startswith('* '):
            out.append('* Cauchy integral formula for a rectangle with one extra continuity-only interior point ` Q =/= P ` : the proof of '
                       '~ rectintcau with ~ z6gour2 in place of ~ rectintgour1 (DetectionShift.lean ` rectInt_cauchy_on ` , used there for '
                       'the ` dslope ` step with the removable point ` 0 ` ).'); continue
        if OA in l:
            l = l.replace(OA, NA)
        lab = l.split(':', 1)[0]
        if lab == 's1':
            l = 's1::simpl1 |- ( %s -> ( A e. CC /\\ B e. CC ) )' % NA
        elif lab == 's2':
            out.append('n1::simpl2 |- ( %s -> %s )' % (NA, PQS))
            l = 's2:n1:simpld |- ( %s -> ( P e. CC /\\ %s ) )' % (NA, QPX('P'))
        elif lab == 's3':
            l = 's3::simpr |- ( %s -> %s )' % (NA, F3)
        elif lab == 'i10':
            l = 'i10::simp1'
        elif lab == 'i12':
            l = 'i12::simp3'
        elif lab == 's13':
            l = 's13:s3,i12:syl |- ( %s -> ( ( A crect B ) \\ { Q } ) C_ dom ( CC _D F ) )' % NA
        elif lab in ('s40', 's41', 's42'):
            continue
        elif lab == 's43':
            l = 's43:s3:simp2d |- ( %s -> ( A crect B ) C_ D )' % NA
        elif lab == 's62':
            out.append('n62a::simpl3 |- ( %s -> P =/= Q )' % NA)
            out.append('n62b:s61,n62a:jca |- ( %s -> ( P e. ( A crect B ) /\\ P =/= Q ) )' % NA)
            out.append('n62i::eldifsn')
            out.append('n62c:n62b,n62i:sylibr |- ( %s -> P e. ( ( A crect B ) \\ { Q } ) )' % NA)
            l = 's62:s13,n62c:sseldd |- ( %s -> P e. dom ( CC _D F ) )' % NA
        elif lab == 's76':
            out.append('n76a:s13,i75:syl |- ( %s -> ( ( ( A crect B ) \\ { Q } ) \\ { P } ) C_ ( dom ( CC _D F ) \\ { P } ) )' % NA)
            out.append('n76b::prcom |- { P , Q } = { Q , P }')
            out.append('n76c::df-pr |- { Q , P } = ( { Q } u. { P } )')
            out.append('n76d:n76b,n76c:eqtri |- { P , Q } = ( { Q } u. { P } )')
            out.append('n76e:n76d:difeq2i |- ( ( A crect B ) \\ { P , Q } ) = ( ( A crect B ) \\ ( { Q } u. { P } ) )')
            out.append('n76f::difun1 |- ( ( A crect B ) \\ ( { Q } u. { P } ) ) = ( ( ( A crect B ) \\ { Q } ) \\ { P } )')
            out.append('n76g:n76e,n76f:eqtri |- ( ( A crect B ) \\ { P , Q } ) = ( ( ( A crect B ) \\ { Q } ) \\ { P } )')
            l = 's76:n76g,n76a:eqsstrid |- ( %s -> ( ( A crect B ) \\ { P , Q } ) C_ ( dom ( CC _D F ) \\ { P } ) )' % NA
        elif lab in ('s77', 's78'):
            l = l.replace('( ( A crect B ) \\ { P } ) C_ dom ( CC _D ( z e. D', '( ( A crect B ) \\ { P , Q } ) C_ dom ( CC _D ( z e. D')
        elif lab == 'i79':
            l = 'i79::z6gour2'
        elif lab == 's80':
            l = l.replace('s80:s1,s2,s78,i79:syl3anc', 's80:s1,n1,s78,i79:syl3anc')
        out.append(l)
    w = W('z6cau2', '')
    w.write = lambda: open(os.path.join(MM.WSDIR, 'z6cau2.mmp'), 'w').write('\n'.join(out))
    return w


if __name__ == '__main__':
    lin.FASTPATH = True
    for fn in [z6gsub, z6gour2h, z6gour2v, z6gour2a, z6cneq, z6gour2, z6cau2]:
        if want(fn.__name__):
            run(fn())
