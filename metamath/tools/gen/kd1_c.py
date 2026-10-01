"""Sortie KD1: integration by parts for the Taylor coefficient integrals (kdibp)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def sqctx(w, A0, pc, rp):
    """corners in CC, P inside, corner order; returns dict"""
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    A, B = QLO('P', 'R'), QHI('P', 'R')
    rr = s([rp], 'rpred', 'R e. RR')
    rc = s([rr], 'recnd', 'R e. CC')
    ic = s([], 'ax-icn', '_i e. CC') if False else w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)
    irc = s([ic, rc], 'mulcld', '( _i x. R ) e. CC')
    ri = s([rc, irc], 'addcld', '( R + ( _i x. R ) ) e. CC')
    ac = s([pc, ri], 'subcld', '%s e. CC' % A)
    bc = s([pc, ri], 'addcld', '%s e. CC' % B)
    ab = s([ac, bc], 'jca', '( %s e. CC /\\ %s e. CC )' % (A, B))
    # P inside: sqint with U = C = P
    z0 = s([pc], 'subidd', '( P - P ) = 0')
    a0 = s([z0], 'fveq2d', '( abs ` ( P - P ) ) = ( abs ` 0 )')
    ab0 = w.s([w.s([], 'abs0', '( abs ` 0 ) = 0')], 'a1i', '( %s -> ( abs ` 0 ) = 0 )' % A0)
    a00 = s([a0, ab0], 'eqtrd', '( abs ` ( P - P ) ) = 0')
    r0 = s([rp], 'rpgt0d', '0 < R')
    lt = s([a00, r0], 'eqbrtrd', '( abs ` ( P - P ) ) < R')
    INT = '( P e. CC /\\ ( ( ( Re ` %s ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` %s ) ) ) )' % (A, B, A, B)
    j1 = s([pc, rr], 'jca', '( P e. CC /\\ R e. RR )')
    j2 = s([pc, lt], 'jca', '( P e. CC /\\ ( abs ` ( P - P ) ) < R )')
    inn = s([j1, j2, w.inst('sqint')], 'syl2anc', INT)
    # order
    rl = s([inn], 'simprd', '( ( ( Re ` %s ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` %s ) ) /\\ ( ( Im ` %s ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` %s ) ) )' % (A, B, A, B))
    re_ = s([rl], 'simpld', '( ( Re ` %s ) < ( Re ` P ) /\\ ( Re ` P ) < ( Re ` %s ) )' % (A, B))
    im_ = s([rl], 'simprd', '( ( Im ` %s ) < ( Im ` P ) /\\ ( Im ` P ) < ( Im ` %s ) )' % (A, B))
    ra = s([ac], 'recld', '( Re ` %s ) e. RR' % A); rb = s([bc], 'recld', '( Re ` %s ) e. RR' % B)
    ia = s([ac], 'imcld', '( Im ` %s ) e. RR' % A); ib = s([bc], 'imcld', '( Im ` %s ) e. RR' % B)
    rpr = s([pc], 'recld', '( Re ` P ) e. RR'); ipr = s([pc], 'imcld', '( Im ` P ) e. RR')
    r1 = s([re_], 'simpld', '( Re ` %s ) < ( Re ` P )' % A); r2 = s([re_], 'simprd', '( Re ` P ) < ( Re ` %s )' % B)
    i1 = s([im_], 'simpld', '( Im ` %s ) < ( Im ` P )' % A); i2 = s([im_], 'simprd', '( Im ` P ) < ( Im ` %s )' % B)
    rlt = s([ra, rpr, rb, r1, r2], 'lttrd', '( Re ` %s ) < ( Re ` %s )' % (A, B))
    ilt = s([ia, ipr, ib, i1, i2], 'lttrd', '( Im ` %s ) < ( Im ` %s )' % (A, B))
    rle = s([ra, rb, rlt], 'ltled', '( Re ` %s ) <_ ( Re ` %s )' % (A, B))
    ile = s([ia, ib, ilt], 'ltled', '( Im ` %s ) <_ ( Im ` %s )' % (A, B))
    ordr = s([rle, ile], 'jca', '( ( Re ` %s ) <_ ( Re ` %s ) /\\ ( Im ` %s ) <_ ( Im ` %s ) )' % (A, B, A, B))
    inp = s([ab, inn], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ %s )' % (A, B, INT))
    fr = s([inp, w.inst('crectfrp')], 'syl', '%s C_ ( %s \\ { P } )' % (FRM(A, B), SQ('P', 'R')))
    return dict(A=A, B=B, ac=ac, bc=bc, ab=ab, INT=INT, inn=inn, ordr=ordr, fr=fr, rr=rr, rc=rc, inp=inp)


def gen_ibp():
    w = W('kdibp', 'Integration by parts for the Taylor coefficients on a square: ` TC ( F \' , k ) = ( k + 1 ) TC ( F , k + 1 ) ` .  The primitive ` F / ( z - P ) ^ ( k + 1 ) ` is holomorphic off ` P ` , so its derivative integrates to zero over the frame ( ` kdftc ` ).')
    A0 = S['kdibp'].split(' -> ')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    hf = s([], 'simp1', HOLF('F', 'D'))
    pc = s([], 'simp21', 'P e. CC'); rp = s([], 'simp22', 'R e. RR+'); sqd = s([], 'simp23', '%s C_ D' % SQ('P', 'R'))
    kk = s([], 'simp3', 'K e. NN0')
    k1 = s([kk, w.inst('nn0p1nn')], 'syl', '( K + 1 ) e. NN')
    k1c = s([k1], 'nncnd', '( K + 1 ) e. CC')
    kc = s([kk], 'nn0cnd', 'K e. CC')
    q = sqctx(w, A0, pc, rp)
    A, B = q['A'], q['B']
    fcn = s([hf, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )')
    dop = s([hf, w.inst('holopn')], 'syl', 'D e. %s' % TOP)
    dcc = s([fcn, w.inst('cncfrss')], 'syl', 'D C_ CC')
    U = '( D \\ { P } )'
    # U open
    je = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    hs = w.s([je], 'cnfldhaus', '%s e. Haus' % TOP)
    un = w.s([], 'unicntop', 'CC = U. %s' % TOP)
    pu = s([pc, w.s([un], 'a1i', '( %s -> CC = U. %s )' % (A0, TOP))], 'eleqtrd', 'P e. U. %s' % TOP)
    scl = s([w.s([hs], 'a1i', '( %s -> %s e. Haus )' % (A0, TOP)), pu, w.inst('sncld')], 'syl2anc', '{ P } e. ( Clsd ` %s )' % TOP)
    uop = s([dop, scl, w.s([un], 'difopn', '( ( D e. %s /\\ { P } e. ( Clsd ` %s ) ) -> %s e. %s )' % (TOP, TOP, U, TOP))], 'syl2anc', '%s e. %s' % (U, TOP))
    ud = w.s([], 'difss', '%s C_ D' % U); udd = w.s([ud], 'a1i', '( %s -> %s C_ D )' % (A0, U))
    ucc = s([udd, dcc], 'sstrd', '%s C_ CC' % U)
    ucp = s([dcc, w.inst('ssdif')], 'syl', '%s C_ ( CC \\ { P } )' % U)
    frs = s([q['fr'], s([sqd, w.inst('ssdif')], 'syl', '( %s \\ { P } ) C_ %s' % (SQ('P', 'R'), U))], 'sstrd', '%s C_ %s' % (FRM(A, B), U))
    # holomorphic pieces on U
    Fu = '( x e. %s |-> ( F ` x ) )' % U
    Fz = '( z e. %s |-> ( F ` z ) )' % U
    Pwz = '( z e. %s |-> ( ( z - P ) ^ ( K + 1 ) ) )' % U
    cz1 = w.s([w.s([], 'fveq2', '( z = x -> ( F ` z ) = ( F ` x ) )')], 'cbvmptv', '%s = %s' % (Fz, Fu))
    cz2 = w.s([w.s([w.s([], 'oveq1', '( z = x -> ( z - P ) = ( x - P ) )')], 'oveq1d', '( z = x -> ( ( z - P ) ^ ( K + 1 ) ) = ( ( x - P ) ^ ( K + 1 ) ) )')], 'cbvmptv', '%s = %s' % (Pwz, '( x e. %s |-> ( ( x - P ) ^ ( K + 1 ) ) )' % U))
    Pw = '( x e. %s |-> ( ( x - P ) ^ ( K + 1 ) ) )' % U
    Pwy = '( y e. %s |-> ( ( y - P ) ^ ( K + 1 ) ) )' % U
    hfz = s([hf, s([uop, udd], 'jca', '( %s e. %s /\\ %s C_ D )' % (U, TOP, U)), w.inst('zl2hres')], 'syl2anc', HOLF(Fz, U))
    hfu = s([hfz, holeq(w, A0, w.s([cz1], 'a1i', '( %s -> %s = %s )' % (A0, Fz, Fu)), Fz, Fu, U)], 'mpbid', HOLF(Fu, U))
    ouc = s([uop, ucc], 'jca', '( %s e. %s /\\ %s C_ CC )' % (U, TOP, U))
    pk = s([pc, k1], 'jca', '( P e. CC /\\ ( K + 1 ) e. NN )')
    hpy = s([ouc, pk, w.inst('holpowp')], 'syl2anc', HOLF(Pwy, U))
    cb1 = w.s([], 'oveq1', '( y = x -> ( y - P ) = ( x - P ) )')
    cb2 = w.s([cb1], 'oveq1d', '( y = x -> ( ( y - P ) ^ ( K + 1 ) ) = ( ( x - P ) ^ ( K + 1 ) ) )')
    cbv = w.s([cb2], 'cbvmptv', '%s = %s' % (Pwy, Pw))
    hpe = holeq(w, A0, w.s([cbv], 'a1i', '( %s -> %s = %s )' % (A0, Pwy, Pw)), Pwy, Pw, U)
    hpw = s([hpy, hpe], 'mpbid', HOLF(Pw, U))
    # pointwise facts under ( A0 /\ v e. U )
    def ptw(v):
        Av = '( %s /\\ %s e. %s )' % (A0, v, U)
        t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
        vu = t([], 'simpr', '%s e. %s' % (v, U))
        vcp = t([w.s([ucp], 'adantr', '( %s -> %s C_ ( CC \\ { P } ) )' % (Av, U)), vu], 'sseldd', '%s e. ( CC \\ { P } )' % v)
        vc = t([vcp, w.inst('eldifi')], 'syl', '%s e. CC' % v)
        vne = t([vcp, w.inst('eldifsni')], 'syl', '%s =/= P' % v)
        pca = w.s([pc], 'adantr', '( %s -> P e. CC )' % Av)
        dvp = t([vc, pca], 'subcld', '( %s - P ) e. CC' % v)
        dne = t([vc, pca, vne], 'subne0d', '( %s - P ) =/= 0' % v)
        kka = w.s([kk], 'adantr', '( %s -> K e. NN0 )' % Av)
        k1a = t([kka, w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')
        pwc = t([dvp, k1a], 'expcld', '( ( %s - P ) ^ ( K + 1 ) ) e. CC' % v)
        pwn = t([dvp, dne, w.s([k1a], 'nn0zd', '( %s -> ( K + 1 ) e. ZZ )' % Av)], 'expne0d', '( ( %s - P ) ^ ( K + 1 ) ) =/= 0' % v)
        e1 = w.s([], 'oveq1', '( x = %s -> ( x - P ) = ( %s - P ) )' % (v, v))
        e2 = w.s([e1], 'oveq1d', '( x = %s -> ( ( x - P ) ^ ( K + 1 ) ) = ( ( %s - P ) ^ ( K + 1 ) ) )' % (v, v))
        pv = t([e2, vu, pwc], 'fvmptd3', '( %s ` %s ) = ( ( %s - P ) ^ ( K + 1 ) )' % (Pw, v, v)) if False else \
            t([w.s([w.s([], 'eqid', '%s = %s' % (Pw, Pw))], 'a1i', '( %s -> %s = %s )' % (Av, Pw, Pw)),
               w.s([e2], 'adantl', '( ( %s /\\ x = %s ) -> ( ( x - P ) ^ ( K + 1 ) ) = ( ( %s - P ) ^ ( K + 1 ) ) )' % (Av, v, v)),
               vu, pwc], 'fvmptd', '( %s ` %s ) = ( ( %s - P ) ^ ( K + 1 ) )' % (Pw, v, v))
        return dict(Av=Av, vu=vu, vc=vc, dvp=dvp, dne=dne, pwc=pwc, pwn=pwn, pv=pv, kka=kka)
    pv_ = ptw('v')
    ne = w.s([pv_['pv'], pv_['pwn']], 'eqnetrd', '( %s -> ( %s ` v ) =/= 0 )' % (pv_['Av'], Pw))
    nev = w.s([ne], 'ralrimiva', '( %s -> A. v e. %s ( %s ` v ) =/= 0 )' % (A0, U, Pw))
    Phi = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (U, Fu, Pw)
    hphi = s([hfu, hpw, nev, w.inst('holdiv')], 'syl3anc', HOLF(Phi, U))
    phicn = s([hphi, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (Phi, U))
    phif = s([phicn, w.inst('cncff')], 'syl', '%s : %s --> CC' % (Phi, U))
    dphi = s([hphi, w.inst('ef2dvh')], 'syl', HOLF('( CC _D %s )' % Phi, U))
    dphicn = s([dphi, w.inst('simpl')], 'syl', '( CC _D %s ) e. ( %s -cn-> CC )' % (Phi, U))
    geq = s([phif, w.s([w.s([], 'eqid', '( CC _D %s ) = ( CC _D %s )' % (Phi, Phi))], 'a1i', '( %s -> ( CC _D %s ) = ( CC _D %s ) )' % (A0, Phi, Phi))],
            'jca', '( %s : %s --> CC /\\ ( CC _D %s ) = ( CC _D %s ) )' % (Phi, U, Phi, Phi))
    fj = s([dphicn, frs], 'jca', '( ( CC _D %s ) e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (Phi, U, FRM(A, B), U))
    gf = s([geq, fj], 'jca', '( ( %s : %s --> CC /\\ ( CC _D %s ) = ( CC _D %s ) ) /\\ ( ( CC _D %s ) e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (
        Phi, U, Phi, Phi, Phi, U, FRM(A, B), U))
    RI = lambda G: '( %s rectint <. %s , %s >. )' % (G, A, B)
    ftc = s([q['ab'], q['ordr'], gf, w.inst('kdftc')], 'syl3anc', '%s = 0' % RI('( CC _D %s )' % Phi))
    # explicit derivative (dvmptdiv) on U
    Az = '( %s /\\ z e. %s )' % (A0, U)
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Az, f))
    zu = t([], 'simpr', 'z e. %s' % U)
    fuf = s([s([hfu, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (Fu, U)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (Fu, U))
    fuc = t([w.s([fuf], 'adantr', '( %s -> %s : %s --> CC )' % (Az, Fu, U)), zu], 'ffvelcdmd', '( %s ` z ) e. CC' % Fu)
    fvx = lambda X: w.s([w.s([], 'fvex', '( %s ` z ) e. _V' % X)], 'a1i', '( %s -> ( %s ` z ) e. _V )' % (Az, X))
    daF = s([hfu, w.inst('holdv')], 'syl', '( CC _D ( z e. %s |-> ( %s ` z ) ) ) = ( z e. %s |-> ( ( CC _D %s ) ` z ) )' % (U, Fu, U, Fu))
    pz = ptw('z')
    pwz = t([pz['pv'], pz['pwn']], 'eqnetrd', '( %s ` z ) =/= 0' % Pw)
    pwzc = t([pz['pv'], pz['pwc']], 'eqeltrd', '( %s ` z ) e. CC' % Pw)
    pwz0 = t([pwzc, pwz, w.inst('eldifsn')], 'sylanbrc', '( %s ` z ) e. ( CC \\ { 0 } )' % Pw) if False else \
        w.s([w.s([pwzc, pwz], 'jca', '( %s -> ( ( %s ` z ) e. CC /\\ ( %s ` z ) =/= 0 ) )' % (Az, Pw, Pw)),
             w.s([], 'eldifsn', '( ( %s ` z ) e. ( CC \\ { 0 } ) <-> ( ( %s ` z ) e. CC /\\ ( %s ` z ) =/= 0 ) )' % (Pw, Pw, Pw))],
            'sylibr', '( %s -> ( %s ` z ) e. ( CC \\ { 0 } ) )' % (Az, Pw))
    dpf = s([hpw, w.inst('holf')], 'syl', '( CC _D %s ) : %s --> CC' % (Pw, U))
    dpc = t([w.s([dpf], 'adantr', '( %s -> ( CC _D %s ) : %s --> CC )' % (Az, Pw, U)), zu], 'ffvelcdmd', '( ( CC _D %s ) ` z ) e. CC' % Pw)
    daP = s([hpw, w.inst('holdv')], 'syl', '( CC _D ( z e. %s |-> ( %s ` z ) ) ) = ( z e. %s |-> ( ( CC _D %s ) ` z ) )' % (U, Pw, U, Pw))
    cpr = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
    NUM = '( ( ( ( CC _D %s ) ` z ) x. ( %s ` z ) ) - ( ( ( CC _D %s ) ` z ) x. ( %s ` z ) ) )' % (Fu, Pw, Pw, Fu)
    DPHI = '( z e. %s |-> ( %s / ( ( %s ` z ) ^ 2 ) ) )' % (U, NUM, Pw)
    dvd = s([cpr, fuc, fvx('( CC _D %s )' % Fu), daF, pwz0, dpc, daP], 'dvmptdiv',
            '( CC _D ( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) ) ) = %s' % (U, Fu, Pw, DPHI))
    # the two explicit derivatives of the pieces
    ce = w.s([w.s([], 'cnelprrecn', 'CC e. { RR , CC }')], 'a1i', '( %s -> CC e. { RR , CC } )' % A0)
    Ad = '( %s /\\ z e. D )' % A0
    zd = w.s([], 'simpr', '( %s -> z e. D )' % Ad)
    fdf = s([fcn, w.inst('cncff')], 'syl', 'F : D --> CC')
    fzc = w.s([w.s([fdf], 'adantr', '( %s -> F : D --> CC )' % Ad), zd], 'ffvelcdmd', '( %s -> ( F ` z ) e. CC )' % Ad)
    fdx = w.s([w.s([], 'fvex', '( ( CC _D F ) ` z ) e. _V')], 'a1i', '( %s -> ( ( CC _D F ) ` z ) e. _V )' % Ad)
    hdv = s([hf, w.inst('holdv')], 'syl', '( CC _D ( z e. D |-> ( F ` z ) ) ) = ( z e. D |-> ( ( CC _D F ) ` z ) )')
    jr = w.s([w.s([], 'cnrestid', '( %s |`t CC ) = %s' % (TOP, TOP))], 'eqcomi', '%s = ( %s |`t CC )' % (TOP, TOP))
    ej = w.s([], 'eqid', '%s = %s' % (TOP, TOP))
    DFU = '( z e. %s |-> ( ( CC _D F ) ` z ) )' % U
    dfz = s([ce, fzc, fdx, hdv, udd, jr, ej, uop], 'dvmptres', '( CC _D %s ) = %s' % (Fz, DFU))
    dfu = s([s([w.s([cz1], 'a1i', '( %s -> %s = %s )' % (A0, Fz, Fu))], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (Fz, Fu)), dfz], 'eqtr3d', '( CC _D %s ) = %s' % (Fu, DFU))
    DPW = '( z e. %s |-> ( ( K + 1 ) x. ( ( z - P ) ^ ( ( K + 1 ) - 1 ) ) ) )' % U
    dpz = s([ouc, pk, w.inst('dvsubexp')], 'syl2anc', '( CC _D %s ) = %s' % (Pwz, DPW))
    dpw = s([s([w.s([cz2], 'a1i', '( %s -> %s = %s )' % (A0, Pwz, Pw))], 'oveq2d', '( CC _D %s ) = ( CC _D %s )' % (Pwz, Pw)), dpz], 'eqtr3d', '( CC _D %s ) = %s' % (Pw, DPW))
    # evaluation on the frame
    FR = FRM(A, B)
    Au = '( %s /\\ u e. %s )' % (A0, FR)
    v = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Au, f))
    ad = lambda st: w.s([st], 'adantr', '( %s -> %s )' % (Au, formula_of(w, st).split(' -> ', 1)[1][:-2]))
    uF = v([], 'simpr', 'u e. %s' % FR)
    uU = v([ad(frs), uF], 'sseldd', 'u e. %s' % U)
    uS = v([ad(q['fr']), uF], 'sseldd', 'u e. ( %s \\ { P } )' % SQ('P', 'R'))
    uc = v([ad(ucc), uU], 'sseldd', 'u e. CC')
    ucp2 = v([ad(ucp), uU], 'sseldd', 'u e. ( CC \\ { P } )')
    une = v([ucp2, w.inst('eldifsni')], 'syl', 'u =/= P')
    pcu = ad(pc)
    W_ = '( u - P )'
    wc = v([uc, pcu], 'subcld', '%s e. CC' % W_)
    wn = v([uc, pcu, une], 'subne0d', '%s =/= 0' % W_)
    kku = ad(kk)
    k1u = v([kku, w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0')
    k2u = v([k1u, w.inst('peano2nn0')], 'syl', '( ( K + 1 ) + 1 ) e. NN0')
    k1cu = v([k1u], 'nn0cnd', '( K + 1 ) e. CC')
    kzu = v([kku], 'nn0zd', 'K e. ZZ')
    k1zu = v([k1u], 'nn0zd', '( K + 1 ) e. ZZ')
    k2zu = v([k2u], 'nn0zd', '( ( K + 1 ) + 1 ) e. ZZ')
    pK = '( %s ^ K )' % W_; p1 = '( %s ^ ( K + 1 ) )' % W_; p2 = '( %s ^ ( ( K + 1 ) + 1 ) )' % W_
    pKc = v([wc, kku], 'expcld', '%s e. CC' % pK)
    p1c = v([wc, k1u], 'expcld', '%s e. CC' % p1)
    p2c = v([wc, k2u], 'expcld', '%s e. CC' % p2)
    pKn = v([wc, wn, kzu], 'expne0d', '%s =/= 0' % pK)
    p1n = v([wc, wn, k1zu], 'expne0d', '%s =/= 0' % p1)
    p2n = v([wc, wn, k2zu], 'expne0d', '%s =/= 0' % p2)
    fdfu = s([hf, w.inst('holf')], 'syl', '( CC _D F ) : D --> CC')
    uD = v([ad(udd), uU], 'sseldd', 'u e. D')
    Fu_ = '( F ` u )'; Fd_ = '( ( CC _D F ) ` u )'
    fuc_ = v([ad(fdf), uD], 'ffvelcdmd', '%s e. CC' % Fu_)
    fdc_ = v([ad(fdfu), uD], 'ffvelcdmd', '%s e. CC' % Fd_)
    # the mapping values at u
    e_fu = w.s([], 'fveq2', '( x = u -> ( F ` x ) = ( F ` u ) )')
    vFu = fvmd(w, Au, Fu, 'u', Fu_, uU, fuc_, e_fu, var='x')
    e_pw1 = w.s([], 'oveq1', '( z = u -> ( z - P ) = ( u - P ) )')
    e_pw = w.s([e_pw1], 'oveq1d', '( z = u -> ( ( z - P ) ^ ( K + 1 ) ) = %s )' % p1)
    e_px = w.s([w.s([], 'oveq1', '( x = u -> ( x - P ) = ( u - P ) )')], 'oveq1d', '( x = u -> ( ( x - P ) ^ ( K + 1 ) ) = %s )' % p1)
    vPw = fvmd(w, Au, Pw, 'u', p1, uU, p1c, e_px, var='x')
    e_df = w.s([], 'fveq2', '( z = u -> ( ( CC _D F ) ` z ) = %s )' % Fd_)
    vDF0 = fvmd(w, Au, DFU, 'u', Fd_, uU, fdc_, e_df)
    vDF = v([w.s([ad(dfu)], 'fveq1d', '( %s -> ( ( CC _D %s ) ` u ) = ( %s ` u ) )' % (Au, Fu, DFU)), vDF0], 'eqtrd', '( ( CC _D %s ) ` u ) = %s' % (Fu, Fd_))
    pKm = '( %s ^ ( ( K + 1 ) - 1 ) )' % W_
    km = v([v([kku], 'nn0cnd', 'K e. CC'), w.s([], '1cnd', '( %s -> 1 e. CC )' % Au)], 'pncand', '( ( K + 1 ) - 1 ) = K')
    pKmc = v([wc, v([km, kku], 'eqeltrd', '( ( K + 1 ) - 1 ) e. NN0')], 'expcld', '%s e. CC' % pKm)
    DPv = '( ( K + 1 ) x. %s )' % pKm
    dpvc = v([k1cu, pKmc], 'mulcld', '%s e. CC' % DPv)
    e_dp1 = w.s([e_pw1], 'oveq1d', '( z = u -> ( ( z - P ) ^ ( ( K + 1 ) - 1 ) ) = %s )' % pKm)
    e_dp = w.s([e_dp1], 'oveq2d', '( z = u -> ( ( K + 1 ) x. ( ( z - P ) ^ ( ( K + 1 ) - 1 ) ) ) = %s )' % DPv)
    vDP0 = fvmd(w, Au, DPW, 'u', DPv, uU, dpvc, e_dp)
    vDP = v([w.s([ad(dpw)], 'fveq1d', '( %s -> ( ( CC _D %s ) ` u ) = ( %s ` u ) )' % (Au, Pw, DPW)), vDP0], 'eqtrd', '( ( CC _D %s ) ` u ) = %s' % (Pw, DPv))
    NUMu = '( ( %s x. %s ) - ( %s x. %s ) )' % (Fd_, p1, DPv, Fu_)
    Hval = '( %s / ( %s ^ 2 ) )' % (NUMu, p1)
    numc = v([v([fdc_, p1c], 'mulcld', '( %s x. %s ) e. CC' % (Fd_, p1)), v([dpvc, fuc_], 'mulcld', '( %s x. %s ) e. CC' % (DPv, Fu_))],
             'subcld', '%s e. CC' % NUMu)
    hvc = v([numc, v([p1c], 'sqcld', '( %s ^ 2 ) e. CC' % p1), v([p1c, p1n, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % Au)], 'expne0d', '( %s ^ 2 ) =/= 0' % p1)],
            'divcld', '%s e. CC' % Hval)
    # ( CC _D Phi ) ` u = Hval
    NUMz = NUM
    NUMg = '( ( ( ( CC _D %s ) ` u ) x. ( %s ` u ) ) - ( ( ( CC _D %s ) ` u ) x. ( %s ` u ) ) )' % (Fu, Pw, Pw, Fu)
    Hg = '( %s / ( ( %s ` u ) ^ 2 ) )' % (NUMg, Pw)
    c1 = w.s([], 'fveq2', '( z = u -> ( ( CC _D %s ) ` z ) = ( ( CC _D %s ) ` u ) )' % (Fu, Fu))
    c2 = w.s([], 'fveq2', '( z = u -> ( %s ` z ) = ( %s ` u ) )' % (Pw, Pw))
    c3 = w.s([], 'fveq2', '( z = u -> ( ( CC _D %s ) ` z ) = ( ( CC _D %s ) ` u ) )' % (Pw, Pw))
    c4 = w.s([], 'fveq2', '( z = u -> ( %s ` z ) = ( %s ` u ) )' % (Fu, Fu))
    c12 = w.s([c1, c2], 'oveq12d', '( z = u -> ( ( ( CC _D %s ) ` z ) x. ( %s ` z ) ) = ( ( ( CC _D %s ) ` u ) x. ( %s ` u ) ) )' % (Fu, Pw, Fu, Pw))
    c34 = w.s([c3, c4], 'oveq12d', '( z = u -> ( ( ( CC _D %s ) ` z ) x. ( %s ` z ) ) = ( ( ( CC _D %s ) ` u ) x. ( %s ` u ) ) )' % (Pw, Fu, Pw, Fu))
    cn_ = w.s([c12, c34], 'oveq12d', '( z = u -> %s = %s )' % (NUMz, NUMg))
    c2s = w.s([c2], 'oveq1d', '( z = u -> ( ( %s ` z ) ^ 2 ) = ( ( %s ` u ) ^ 2 ) )' % (Pw, Pw))
    cH = w.s([cn_, c2s], 'oveq12d', '( z = u -> ( %s / ( ( %s ` z ) ^ 2 ) ) = %s )' % (NUMz, Pw, Hg))
    # Hg = Hval by the value lemmas
    g1 = v([vDF, vPw], 'oveq12d', '( ( ( CC _D %s ) ` u ) x. ( %s ` u ) ) = ( %s x. %s )' % (Fu, Pw, Fd_, p1))
    g2 = v([vDP, vFu], 'oveq12d', '( ( ( CC _D %s ) ` u ) x. ( %s ` u ) ) = ( %s x. %s )' % (Pw, Fu, DPv, Fu_))
    g3 = v([g1, g2], 'oveq12d', '%s = %s' % (NUMg, NUMu))
    g4 = v([vPw], 'oveq1d', '( ( %s ` u ) ^ 2 ) = ( %s ^ 2 )' % (Pw, p1))
    g5 = v([g3, g4], 'oveq12d', '%s = %s' % (Hg, Hval))
    hgc = v([g5, hvc], 'eqeltrd', '%s e. CC' % Hg)
    vH0 = fvmd(w, Au, DPHI, 'u', Hg, uU, hgc, cH)
    vH1 = v([w.s([ad(dvd)], 'fveq1d', '( %s -> ( ( CC _D %s ) ` u ) = ( %s ` u ) )' % (Au, Phi, DPHI)), vH0], 'eqtrd', '( ( CC _D %s ) ` u ) = %s' % (Phi, Hg))
    vH = v([vH1, g5], 'eqtrd', '( ( CC _D %s ) ` u ) = %s' % (Phi, Hval))
    # algebra: Hval = ( Fd / p1 ) - ( ( K + 1 ) x. ( Fu / p2 ) )
    sq = v([p1c], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (p1, p1, p1))
    A1 = '( %s x. %s )' % (Fd_, p1); A2 = '( %s x. %s )' % (DPv, Fu_)
    PP = '( %s x. %s )' % (p1, p1)
    ppn = v([p1c, p1c, p1n, p1n], 'mulne0d', '%s =/= 0' % PP)
    ppc = v([p1c, p1c], 'mulcld', '%s e. CC' % PP)
    h1 = v([sq], 'oveq2d', '%s = ( %s / %s )' % (Hval, NUMu, PP))
    h2 = v([v([fdc_, p1c], 'mulcld', '%s e. CC' % A1), v([dpvc, fuc_], 'mulcld', '%s e. CC' % A2), ppc, ppn], 'divsubdird',
           '( %s / %s ) = ( ( %s / %s ) - ( %s / %s ) )' % (NUMu, PP, A1, PP, A2, PP))
    h3 = v([fdc_, p1c, p1c, p1n, p1n], 'divcan5rd', '( %s / %s ) = ( %s / %s )' % (A1, PP, Fd_, p1))
    # second term: ( ( K+1 ) p^(K+1-1) Fu ) / ( p1 p1 ) = ( K+1 ) ( Fu / p2 )
    kmK = v([km], 'oveq2d', '%s = %s' % (pKm, pK))
    A2b = '( ( ( K + 1 ) x. %s ) x. %s )' % (pK, Fu_)
    h4 = v([v([kmK], 'oveq2d', '%s = ( ( K + 1 ) x. %s )' % (DPv, pK))], 'oveq1d', '%s = %s' % (A2, A2b))
    # p1 p1 = pK ( p2 ): p1 = pK w, p2 = p1 w
    p1e_ = v([wc, kku], 'expp1d', '%s = ( %s x. %s )' % (p1, pK, W_))
    p2e_ = v([wc, k1u], 'expp1d', '%s = ( %s x. %s )' % (p2, p1, W_))
    # pK x. p2 = pK x. ( p1 x. W ) = ( pK x. W ) x. p1 = p1 x. p1
    t1 = v([p2e_], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (pK, p2, pK, p1, W_))
    t2 = v([pKc, p1c, wc], 'mul12d', '( %s x. ( %s x. %s ) ) = ( %s x. ( %s x. %s ) )' % (pK, p1, W_, p1, pK, W_))
    t3 = v([p1e_], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (p1, p1, p1, pK, W_))
    t4 = v([t1, t2], 'eqtrd', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (pK, p2, p1, pK, W_))
    t5 = v([t4, t3], 'eqtr4d', '( %s x. %s ) = %s' % (pK, p2, PP))
    KF = '( ( K + 1 ) x. %s )' % Fu_
    kfc = v([k1cu, fuc_], 'mulcld', '%s e. CC' % KF)
    t6 = v([k1cu, pKc, fuc_], 'mul32d', '%s = ( ( ( K + 1 ) x. %s ) x. %s )' % (A2b, Fu_, pK)) if False else \
        v([k1cu, pKc, fuc_], 'mulassd', '%s = ( ( K + 1 ) x. ( %s x. %s ) )' % (A2b, pK, Fu_))
    t7 = v([k1cu, pKc, fuc_], 'mul12d', '( ( K + 1 ) x. ( %s x. %s ) ) = ( %s x. %s )' % (pK, Fu_, pK, KF))
    t8 = v([h4, t6, t7], 'eqtr3d', 'T.') if False else v([v([h4, t6], 'eqtrd', '%s = ( ( K + 1 ) x. ( %s x. %s ) )' % (A2, pK, Fu_)), t7], 'eqtrd', '%s = ( %s x. %s )' % (A2, pK, KF))
    t9 = v([t8, v([t5], 'eqcomd', '%s = ( %s x. %s )' % (PP, pK, p2))], 'oveq12d', '( %s / %s ) = ( ( %s x. %s ) / ( %s x. %s ) )' % (A2, PP, pK, KF, pK, p2))
    t10 = v([kfc, p2c, pKc, p2n, pKn], 'divcan5d', '( ( %s x. %s ) / ( %s x. %s ) ) = ( %s / %s )' % (pK, KF, pK, p2, KF, p2))
    t11 = v([k1cu, fuc_, p2c, p2n], 'divassd', '( %s / %s ) = ( ( K + 1 ) x. ( %s / %s ) )' % (KF, p2, Fu_, p2))
    t12 = v([v([t9, t10], 'eqtrd', '( %s / %s ) = ( %s / %s )' % (A2, PP, KF, p2)), t11], 'eqtrd', '( %s / %s ) = ( ( K + 1 ) x. ( %s / %s ) )' % (A2, PP, Fu_, p2))
    I1v = '( %s / %s )' % (Fd_, p1); I2v = '( %s / %s )' % (Fu_, p2)
    h5 = v([h3, t12], 'oveq12d', '( ( %s / %s ) - ( %s / %s ) ) = ( %s - ( ( K + 1 ) x. %s ) )' % (A1, PP, A2, PP, I1v, I2v))
    hv2 = v([v([h1, h2], 'eqtrd', '%s = ( ( %s / %s ) - ( %s / %s ) )' % (Hval, A1, PP, A2, PP)), h5], 'eqtrd', '%s = ( %s - ( ( K + 1 ) x. %s ) )' % (Hval, I1v, I2v))
    i1c = v([fdc_, p1c, p1n], 'divcld', '%s e. CC' % I1v)
    i2c = v([fuc_, p2c, p2n], 'divcld', '%s e. CC' % I2v)
    ki2 = v([k1cu, i2c], 'mulcld', '( ( K + 1 ) x. %s ) e. CC' % I2v)
    # I1v = ( K + 1 ) I2v + Hval
    hv3 = v([vH, hv2], 'eqtrd', '( ( CC _D %s ) ` u ) = ( %s - ( ( K + 1 ) x. %s ) )' % (Phi, I1v, I2v))
    npc = v([i1c, ki2], 'pncan3d', '( ( ( K + 1 ) x. %s ) + ( %s - ( ( K + 1 ) x. %s ) ) ) = %s' % (I2v, I1v, I2v, I1v))
    # integrand values
    I1 = TCI('( CC _D F )', 'P', 'R', 'K')
    I2y = '( y e. %s |-> ( ( F ` y ) / ( ( y - P ) ^ ( ( K + 1 ) + 1 ) ) ) )' % U
    e_i1 = w.s([e_df, e_pw], 'oveq12d', '( z = u -> ( ( ( CC _D F ) ` z ) / ( ( z - P ) ^ ( K + 1 ) ) ) = %s )' % I1v)
    vI1 = fvmd(w, Au, I1, 'u', I1v, uS, i1c, e_i1)
    e_y1 = w.s([], 'fveq2', '( y = u -> ( F ` y ) = %s )' % Fu_)
    e_y2 = w.s([w.s([], 'oveq1', '( y = u -> ( y - P ) = ( u - P ) )')], 'oveq1d', '( y = u -> ( ( y - P ) ^ ( ( K + 1 ) + 1 ) ) = %s )' % p2)
    e_i2 = w.s([e_y1, e_y2], 'oveq12d', '( y = u -> ( ( F ` y ) / ( ( y - P ) ^ ( ( K + 1 ) + 1 ) ) ) = %s )' % I2v)
    vI2 = fvmd(w, Au, I2y, 'u', I2v, uU, i2c, e_i2, var='y')
    rel0 = v([vI2], 'oveq2d', '( ( K + 1 ) x. ( %s ` u ) ) = ( ( K + 1 ) x. %s )' % (I2y, I2v))
    rel1 = v([rel0, hv3], 'oveq12d', '( ( ( K + 1 ) x. ( %s ` u ) ) + ( ( CC _D %s ) ` u ) ) = ( ( ( K + 1 ) x. %s ) + ( %s - ( ( K + 1 ) x. %s ) ) )' % (I2y, Phi, I2v, I1v, I2v))
    rel2 = v([rel1, npc], 'eqtrd', '( ( ( K + 1 ) x. ( %s ` u ) ) + ( ( CC _D %s ) ` u ) ) = %s' % (I2y, Phi, I1v))
    rel = v([vI1, rel2], 'eqtr4d', '( %s ` u ) = ( ( ( K + 1 ) x. ( %s ` u ) ) + ( ( CC _D %s ) ` u ) )' % (I1, I2y, Phi))
    relall = w.s([rel], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( ( ( K + 1 ) x. ( %s ` u ) ) + ( ( CC _D %s ) ` u ) ) )' % (A0, FR, I1, I2y, Phi))
    # rectintlce
    i2cn = s([s([fcn, udd], 'jca', '( F e. ( D -cn-> CC ) /\\ %s C_ D )' % U), s([pc, ucp], 'jca', '( P e. CC /\\ %s C_ ( CC \\ { P } ) )' % U),
              s([kk, w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0') and s([s([kk, w.inst('peano2nn0')], 'syl', '( K + 1 ) e. NN0'), w.inst('peano2nn0')], 'syl', '( ( K + 1 ) + 1 ) e. NN0'),
              w.inst('cfcn')], 'syl3anc', '%s e. ( %s -cn-> CC )' % (I2y, U))
    ssid_ = w.s([w.s([], 'ssid', '%s C_ %s' % (FR, FR))], 'a1i', '( %s -> %s C_ %s )' % (A0, FR, FR))
    L1 = s([q['ab'], ssid_], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ %s C_ %s )' % (A, B, FR, FR))
    SQD = '( %s \\ { P } )' % SQ('P', 'R')
    sqx = s([w.s([], 'ovex', '%s e. _V' % SQ('P', 'R')) and w.s([w.s([], 'ovex', '%s e. _V' % SQ('P', 'R'))], 'difexg', '%s e. _V' % SQD)], 'a1i' if False else 'id', 'T.') if False else \
        w.s([w.s([w.s([], 'ovex', '%s e. _V' % SQ('P', 'R')), w.inst('difexg')], 'ax-mp', '%s e. _V' % SQD)], 'a1i', '( %s -> %s e. _V )' % (A0, SQD))
    i1x = w.s([sqx], 'mptexd', '( %s -> %s e. _V )' % (A0, I1))
    i2 = TCI('F', 'P', 'R', '( K + 1 )')
    i2x = w.s([sqx], 'mptexd', '( %s -> %s e. _V )' % (A0, i2))
    uvx = w.s([w.s([w.s([], 'ovex', '%s e. _V' % '( D \\ { P } )') if False else w.s([], 'difexg', '( D e. _V -> %s e. _V )' % U) and None], 'id', 'T.')], 'id', 'T.') if False else None
    L2 = s([i1x, k1c, s([i2cn, dphicn, frs], '3jca', '( %s e. ( %s -cn-> CC ) /\\ ( CC _D %s ) e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (I2y, U, Phi, U, FR, U))],
           '3jca', '( %s e. _V /\\ ( K + 1 ) e. CC /\\ ( %s e. ( %s -cn-> CC ) /\\ ( CC _D %s ) e. ( %s -cn-> CC ) /\\ %s C_ %s ) )' % (I1, I2y, U, Phi, U, FR, U))
    RI = lambda G: '( %s rectint <. %s , %s >. )' % (G, A, B)
    lce = s([L1, L2, relall, w.inst('rectintlce')], 'syl3anc', '%s = ( ( ( K + 1 ) x. %s ) + %s )' % (RI(I1), RI(I2y), RI('( CC _D %s )' % Phi)))
    # I2y and the TC integrand agree on the frame
    e_z1 = w.s([], 'fveq2', '( z = u -> ( F ` z ) = %s )' % Fu_)
    e_z2 = w.s([e_pw1], 'oveq1d', '( z = u -> ( ( z - P ) ^ ( ( K + 1 ) + 1 ) ) = %s )' % p2)
    e_i2z = w.s([e_z1, e_z2], 'oveq12d', '( z = u -> ( ( F ` z ) / ( ( z - P ) ^ ( ( K + 1 ) + 1 ) ) ) = %s )' % I2v)
    vI2z = fvmd(w, Au, i2, 'u', I2v, uS, i2c, e_i2z)
    agr = v([vI2, vI2z], 'eqtr4d', '( %s ` u ) = ( %s ` u )' % (I2y, i2))
    agrall = w.s([agr], 'ralrimiva', '( %s -> A. u e. %s ( %s ` u ) = ( %s ` u ) )' % (A0, FR, I2y, i2))
    uX = w.s([w.s([w.s([], 'difss', '%s C_ D' % U)], 'a1i', '( %s -> %s C_ D )' % (A0, U))], 'id', '( %s -> %s C_ D )' % (A0, U))
    i2yx = s([s([dop, w.inst('elex')], 'syl', 'D e. _V') and s([s([dop, w.inst('elex')], 'syl', 'D e. _V'), w.inst('difexg')], 'syl', '%s e. _V' % U)], 'mptexd', '%s e. _V' % I2y)
    eqe = s([L1, s([i2yx, i2x], 'jca', '( %s e. _V /\\ %s e. _V )' % (I2y, i2)), agrall, w.inst('rectinteqe')], 'syl3anc', '%s = %s' % (RI(I2y), RI(i2)))
    lce2 = s([lce, s([eqe], 'oveq2d', '( ( K + 1 ) x. %s ) = ( ( K + 1 ) x. %s )' % (RI(I2y), RI(i2)))], 'eqtrd', 'T.') if False else None
    ri2c = s([s([q['ac'], q['bc']], 'jca', '( %s e. CC /\\ %s e. CC )' % (A, B)), s([i2cn, frs], 'jca', '( %s e. ( %s -cn-> CC ) /\\ %s C_ %s )' % (I2y, U, FR, U)), w.inst('rectintcle')],
          'syl2anc', '%s e. CC' % RI(I2y))
    kr = s([k1c, ri2c], 'mulcld', '( ( K + 1 ) x. %s ) e. CC' % RI(I2y))
    z1 = s([ftc], 'oveq2d', '( ( ( K + 1 ) x. %s ) + %s ) = ( ( ( K + 1 ) x. %s ) + 0 )' % (RI(I2y), RI('( CC _D %s )' % Phi), RI(I2y)))
    z2 = s([kr], 'addridd', '( ( ( K + 1 ) x. %s ) + 0 ) = ( ( K + 1 ) x. %s )' % (RI(I2y), RI(I2y)))
    m1 = s([lce, z1, z2], 'eqtrd' if False else '3eqtrd', '%s = ( ( K + 1 ) x. %s )' % (RI(I1), RI(I2y)))
    m2 = s([m1, s([eqe], 'oveq2d', '( ( K + 1 ) x. %s ) = ( ( K + 1 ) x. %s )' % (RI(I2y), RI(i2)))], 'eqtrd', '%s = ( ( K + 1 ) x. %s )' % (RI(I1), RI(i2)))
    TPI = '( 2 x. ( _i x. _pi ) )'
    tpc = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI)], 'a1i', '( %s -> %s e. CC )' % (A0, TPI))
    tpn = w.s([w.s([], '2pire', '( 2 x. _pi ) e. RR') and w.s([], 'ine0', '_i =/= 0')], 'id', 'T.') if False else None
    tpn = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'),
                    w.s([], '2ne0', '2 =/= 0'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], 'ine0', '_i =/= 0'), w.s([], 'pine0', '_pi =/= 0')], 'mulne0i', '( _i x. _pi ) =/= 0')],
                   'mulne0i', '%s =/= 0' % TPI)], 'a1i', '( %s -> %s =/= 0 )' % (A0, TPI))
    ri2 = s([ri2c, eqe], 'eqeltrd', '%s e. CC' % RI(i2)) if False else s([eqe, ri2c], 'eqeltrrd', '%s e. CC' % RI(i2))
    d1 = s([m2], 'oveq1d', '( %s / %s ) = ( ( ( K + 1 ) x. %s ) / %s )' % (RI(I1), TPI, RI(i2), TPI))
    d2 = s([k1c, ri2, tpc, tpn], 'divassd', '( ( ( K + 1 ) x. %s ) / %s ) = ( ( K + 1 ) x. ( %s / %s ) )' % (RI(i2), TPI, RI(i2), TPI))
    w.qed([d1, d2], 'eqtrd', S['kdibp'])
    return run(w)


if __name__ == '__main__':
    gen_ibp()
