"""Sortie KD1: Cauchy's formula for the iterated derivatives on a square (kdcdn)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of
from kd1_c import sqctx

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def FI(i): return '( ( CC Dn F ) ` %s )' % i
def PS(x): return 'A. i e. NN0 ( %s ` P ) = ( ( ! ` %s ) x. %s )' % (FI('( i + %s )' % x), x, TC(FI('i'), 'P', 'R', x))


def gen_cdn():
    w = W('kdcdn', 'Cauchy\'s formula for the ` K ` -th derivative on a square: ` ( ( CC Dn F ) ` K ) ` P ) = K ! TC ( F , P , R , K ) ` for ` F ` holomorphic on ` D ` containing the square ` SQ ( P , R ) ` (induction on ` K ` over all iterates, base ` rectintcau ` , step ` kdibp ` ).')
    H = HOLF('F', 'D')
    SQH_ = '( P e. CC /\\ R e. RR+ /\\ %s C_ D )' % SQ('P', 'R')
    ph = '( %s /\\ %s )' % (H, SQH_)
    subs = {}
    for nm, t in (('0', '0'), ('y', 'n'), ('y1', '( n + 1 )'), ('K', 'K')):
        idx = w.s([], 'id', '( x = %s -> x = %s )' % (t, t))
        st, new = w.wcongr(PS('x'), {'x': t}, 'x = %s' % t, {'x': idx})
        assert new == PS(t), (new, PS(t))
        subs[nm] = st
    # ---- base
    Ab = '( %s /\\ i e. NN0 )' % ph
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Ab, f))
    hf = b([], 'simpll', H)
    sqh = b([], 'simplr', SQH_)
    pc = b([sqh], 'simp1d', 'P e. CC'); rp = b([sqh], 'simp2d', 'R e. RR+'); sqd = b([sqh], 'simp3d', '%s C_ D' % SQ('P', 'R'))
    ii = b([], 'simpr', 'i e. NN0')
    hi = b([hf, ii, w.inst('kdholdn')], 'syl2anc', HOLF(FI('i'), 'D'))
    q = sqctx(w, Ab, pc, rp)
    A, B = q['A'], q['B']
    icn = b([hi, w.inst('simpl')], 'syl', '%s e. ( D -cn-> CC )' % FI('i'))
    ids = b([hi, w.inst('simpr')], 'syl', 'D C_ dom ( CC _D %s )' % FI('i'))
    sqdm = b([sqd, ids], 'sstrd', '%s C_ dom ( CC _D %s )' % (SQ('P', 'R'), FI('i')))
    RI = lambda G: '( %s rectint <. %s , %s >. )' % (G, A, B)
    ICAU = '( z e. ( %s \\ { P } ) |-> ( ( %s ` z ) / ( z - P ) ) )' % (SQ('P', 'R'), FI('i'))
    TPI = '( 2 x. ( _i x. _pi ) )'
    cau = b([q['ab'], q['inn'], b([icn, sqdm], 'jca', '( %s e. ( D -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (FI('i'), SQ('P', 'R'), FI('i'))),
             w.inst('rectintcau')], 'syl3anc', '%s = ( %s x. ( %s ` P ) )' % (RI(ICAU), TPI, FI('i')))
    # the integrand with exponent ( 0 + 1 ) is the Cauchy integrand
    I0 = TCI(FI('i'), 'P', 'R', '0')
    Az = '( %s /\\ z e. ( %s \\ { P } ) )' % (Ab, SQ('P', 'R'))
    zin = w.s([], 'simpr', '( %s -> z e. ( %s \\ { P } ) )' % (Az, SQ('P', 'R')))
    zc = w.s([w.s([w.s([w.s([], 'difss', '( %s \\ { P } ) C_ %s' % (SQ('P', 'R'), SQ('P', 'R')))], 'a1i',
                        '( %s -> ( %s \\ { P } ) C_ %s )' % (Az, SQ('P', 'R'), SQ('P', 'R'))),
                   w.s([w.s([sqd, w.s([hf, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % Ab)], 'id', '( %s -> %s C_ D )' % (Ab, SQ('P', 'R'))) if False else
                        w.s([sqd, w.s([w.s([hf, w.inst('simpl')], 'syl', '( %s -> F e. ( D -cn-> CC ) )' % Ab), w.inst('cncfrss')], 'syl', '( %s -> D C_ CC )' % Ab)], 'sstrd', '( %s -> %s C_ CC )' % (Ab, SQ('P', 'R')))],
                       'adantr', '( %s -> %s C_ CC )' % (Az, SQ('P', 'R')))], 'sstrd', '( %s -> ( %s \\ { P } ) C_ CC )' % (Az, SQ('P', 'R'))), zin],
             'sseldd', '( %s -> z e. CC )' % Az)
    zp = w.s([zc, w.s([pc], 'adantr', '( %s -> P e. CC )' % Az)], 'subcld', '( %s -> ( z - P ) e. CC )' % Az)
    e01 = w.s([w.s([w.s([], '0p1e1', '( 0 + 1 ) = 1')], 'oveq2i', '( ( z - P ) ^ ( 0 + 1 ) ) = ( ( z - P ) ^ 1 )')], 'a1i',
              '( %s -> ( ( z - P ) ^ ( 0 + 1 ) ) = ( ( z - P ) ^ 1 ) )' % Az)
    ex1 = w.s([zp], 'exp1d', '( %s -> ( ( z - P ) ^ 1 ) = ( z - P ) )' % Az)
    e0 = w.s([e01, ex1], 'eqtrd', '( %s -> ( ( z - P ) ^ ( 0 + 1 ) ) = ( z - P ) )' % Az)
    e0b = w.s([e0], 'oveq2d', '( %s -> ( ( %s ` z ) / ( ( z - P ) ^ ( 0 + 1 ) ) ) = ( ( %s ` z ) / ( z - P ) ) )' % (Az, FI('i'), FI('i')))
    mq = b([e0b], 'mpteq2dva', '%s = %s' % (I0, ICAU))
    r0 = b([mq], 'oveq1d', '%s = %s' % (RI(I0), RI(ICAU)))
    r1 = b([r0, cau], 'eqtrd', '%s = ( %s x. ( %s ` P ) )' % (RI(I0), TPI, FI('i')))
    tpc = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI)],
              'a1i', '( %s -> %s e. CC )' % (Ab, TPI))
    tpn = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'),
                    w.s([], '2ne0', '2 =/= 0'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], 'ine0', '_i =/= 0'), w.s([], 'pine0', '_pi =/= 0')], 'mulne0i', '( _i x. _pi ) =/= 0')],
                   'mulne0i', '%s =/= 0' % TPI)], 'a1i', '( %s -> %s =/= 0 )' % (Ab, TPI))
    ff = b([icn, w.inst('cncff')], 'syl', '%s : D --> CC' % FI('i'))
    pS = b([q['inp'], w.inst('crectinp')], 'syl', 'P e. %s' % SQ('P', 'R'))
    pD = b([sqd, pS], 'sseldd', 'P e. D')
    fpc = b([ff, pD], 'ffvelcdmd', '( %s ` P ) e. CC' % FI('i'))
    tc0 = b([b([r1], 'oveq1d', '( %s / %s ) = ( ( %s x. ( %s ` P ) ) / %s )' % (RI(I0), TPI, TPI, FI('i'), TPI)),
             b([fpc, tpc, tpn], 'divcan3d', '( ( %s x. ( %s ` P ) ) / %s ) = ( %s ` P )' % (TPI, FI('i'), TPI, FI('i')))],
            'eqtrd', '%s = ( %s ` P )' % (TC(FI('i'), 'P', 'R', '0'), FI('i')))
    f0 = w.s([w.s([], 'fac0', '( ! ` 0 ) = 1')], 'a1i', '( %s -> ( ! ` 0 ) = 1 )' % Ab)
    tcc = b([tc0, fpc], 'eqeltrd', '%s e. CC' % TC(FI('i'), 'P', 'R', '0'))
    rhs0 = b([b([f0], 'oveq1d', '( ( ! ` 0 ) x. %s ) = ( 1 x. %s )' % (TC(FI('i'), 'P', 'R', '0'), TC(FI('i'), 'P', 'R', '0'))),
              b([tcc], 'mullidd', '( 1 x. %s ) = %s' % (TC(FI('i'), 'P', 'R', '0'), TC(FI('i'), 'P', 'R', '0'))), tc0],
             '3eqtrd', '( ( ! ` 0 ) x. %s ) = ( %s ` P )' % (TC(FI('i'), 'P', 'R', '0'), FI('i')))
    lhs0 = b([b([b([ii], 'nn0cnd', 'i e. CC')], 'addridd', '( i + 0 ) = i')], 'fveq2d', '%s = %s' % (FI('( i + 0 )'), FI('i')))
    lhs0b = b([lhs0], 'fveq1d', '( %s ` P ) = ( %s ` P )' % (FI('( i + 0 )'), FI('i')))
    base1 = b([lhs0b, rhs0], 'eqtr4d', '( %s ` P ) = ( ( ! ` 0 ) x. %s )' % (FI('( i + 0 )'), TC(FI('i'), 'P', 'R', '0')))
    base = w.s([base1], 'ralrimiva', '( %s -> %s )' % (ph, PS('0')))
    # ---- step (induction variable n)
    A1 = '( ( %s /\\ n e. NN0 ) /\\ %s )' % (ph, PS('n'))
    As = '( %s /\\ j e. NN0 )' % A1
    t = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (As, f))
    hf = w.s([], 'simp-4l', '( %s -> %s )' % (As, H))
    sqh = w.s([], 'simp-4r', '( %s -> %s )' % (As, SQH_))
    nn = w.s([], 'simpllr', '( %s -> n e. NN0 )' % As)
    ih = w.s([], 'simplr', '( %s -> %s )' % (As, PS('n')))
    ii = t([], 'simpr', 'j e. NN0')
    i1 = t([ii, w.inst('peano2nn0')], 'syl', '( j + 1 ) e. NN0')
    body = lambda iv: '( %s ` P ) = ( ( ! ` n ) x. %s )' % (FI('( %s + n )' % iv), TC(FI(iv), 'P', 'R', 'n'))
    idx = w.s([], 'id', '( i = ( j + 1 ) -> i = ( j + 1 ) )')
    cst, cnew = w.wcongr(body('i'), {'i': '( j + 1 )'}, 'i = ( j + 1 )', {'i': idx})
    assert cnew == body('( j + 1 )'), cnew
    rs = w.s([cst], 'rspcv', '( ( j + 1 ) e. NN0 -> ( %s -> %s ) )' % (PS('n'), body('( j + 1 )')))
    ihi = t([i1, ih, rs], 'sylc', body('( j + 1 )'))
    icc = t([ii], 'nn0cnd', 'j e. CC'); ncc = t([nn], 'nn0cnd', 'n e. CC')
    one = w.s([], '1cnd', '( %s -> 1 e. CC )' % As)
    a1 = t([icc, one, ncc], 'addassd', '( ( j + 1 ) + n ) = ( j + ( 1 + n ) )')
    a2 = t([t([one, ncc], 'addcomd', '( 1 + n ) = ( n + 1 )')], 'oveq2d', '( j + ( 1 + n ) ) = ( j + ( n + 1 ) )')
    a3 = t([a1, a2], 'eqtrd', '( ( j + 1 ) + n ) = ( j + ( n + 1 ) )')
    l1 = t([t([a3], 'fveq2d', '%s = %s' % (FI('( ( j + 1 ) + n )'), FI('( j + ( n + 1 ) )')))], 'fveq1d',
           '( %s ` P ) = ( %s ` P )' % (FI('( ( j + 1 ) + n )'), FI('( j + ( n + 1 ) )')))
    pm, _ = pmcc(w, As, hf, 'F', 'D')
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % As)
    dn1 = t([ccs, pm, ii, w.inst('dvnp1')], 'syl3anc', '%s = ( CC _D %s )' % (FI('( j + 1 )'), FI('j')))
    EQF = '%s = ( CC _D %s )' % (FI('( j + 1 )'), FI('j'))
    ide = w.s([], 'id', '( %s -> %s )' % (EQF, EQF))
    tcr0, tnew = w.congr(TC(FI('( j + 1 )'), 'P', 'R', 'n'), {}, EQF, {}, rules={FI('( j + 1 )'): ('( CC _D %s )' % FI('j'), ide)})
    assert tnew == TC('( CC _D %s )' % FI('j'), 'P', 'R', 'n'), tnew
    tcr = t([dn1, tcr0], 'syl', '%s = %s' % (TC(FI('( j + 1 )'), 'P', 'R', 'n'), tnew))
    hi = t([hf, ii, w.inst('kdholdn')], 'syl2anc', HOLF(FI('j'), 'D'))
    T1 = TC(FI('j'), 'P', 'R', '( n + 1 )')
    ibp = t([hi, sqh, nn, w.inst('kdibp')], 'syl3anc', '%s = ( ( n + 1 ) x. %s )' % (TC('( CC _D %s )' % FI('j'), 'P', 'R', 'n'), T1))
    tce = t([tcr, ibp], 'eqtrd', '%s = ( ( n + 1 ) x. %s )' % (TC(FI('( j + 1 )'), 'P', 'R', 'n'), T1))
    fy = t([nn, w.inst('faccl')], 'syl', '( ! ` n ) e. NN')
    fyc = t([fy], 'nncnd', '( ! ` n ) e. CC')
    n1c = t([ncc, one], 'addcld', '( n + 1 ) e. CC')
    # T1 e. CC through rectintccl (binder y) and cbvmptv
    pc = t([sqh], 'simp1d', 'P e. CC'); rp = t([sqh], 'simp2d', 'R e. RR+'); sqd = t([sqh], 'simp3d', '%s C_ D' % SQ('P', 'R'))
    q2 = sqctx(w, As, pc, rp)
    RI2 = lambda G: '( %s rectint <. %s , %s >. )' % (G, q2['A'], q2['B'])
    icn2 = t([hi, w.inst('simpl')], 'syl', '%s e. ( D -cn-> CC )' % FI('j'))
    ids2 = t([hi, w.inst('simpr')], 'syl', 'D C_ dom ( CC _D %s )' % FI('j'))
    sqdm2 = t([sqd, ids2], 'sstrd', '%s C_ dom ( CC _D %s )' % (SQ('P', 'R'), FI('j')))
    n2 = t([t([nn, w.inst('peano2nn0')], 'syl', '( n + 1 ) e. NN0'), w.inst('peano2nn0')], 'syl', '( ( n + 1 ) + 1 ) e. NN0')
    Iy = '( y e. ( %s \\ { P } ) |-> ( ( %s ` y ) / ( ( y - P ) ^ ( ( n + 1 ) + 1 ) ) ) )' % (SQ('P', 'R'), FI('j'))
    Iz = TCI(FI('j'), 'P', 'R', '( n + 1 )')
    jho = t([icn2, sqdm2], 'jca', '( %s e. ( D -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) )' % (FI('j'), SQ('P', 'R'), FI('j')))
    jall = t([q2['ab'], q2['inn'], jho], '3jca', '( ( %s e. CC /\\ %s e. CC ) /\\ %s /\\ ( %s e. ( D -cn-> CC ) /\\ %s C_ dom ( CC _D %s ) ) )' % (q2['A'], q2['B'], q2['INT'], FI('j'), SQ('P', 'R'), FI('j')))
    rcc = w.inst('rectintccl')
    c1 = t([jall, n2, rcc], 'syl2anc', '%s e. CC' % RI2(Iy))
    cbe = w.s([w.s([w.s([], 'fveq2', '( y = z -> ( %s ` y ) = ( %s ` z ) )' % (FI('j'), FI('j'))),
                    w.s([w.s([], 'oveq1', '( y = z -> ( y - P ) = ( z - P ) )')], 'oveq1d', '( y = z -> ( ( y - P ) ^ ( ( n + 1 ) + 1 ) ) = ( ( z - P ) ^ ( ( n + 1 ) + 1 ) ) )')],
                   'oveq12d', '( y = z -> ( ( %s ` y ) / ( ( y - P ) ^ ( ( n + 1 ) + 1 ) ) ) = ( ( %s ` z ) / ( ( z - P ) ^ ( ( n + 1 ) + 1 ) ) ) )' % (FI('j'), FI('j')))],
              'cbvmptv', '%s = %s' % (Iy, Iz))
    c2 = t([t([w.s([cbe], 'a1i', '( %s -> %s = %s )' % (As, Iy, Iz))], 'oveq1d', '%s = %s' % (RI2(Iy), RI2(Iz))), c1], 'eqeltrrd', '%s e. CC' % RI2(Iz))
    TPI = '( 2 x. ( _i x. _pi ) )'
    tpc = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC')], 'mulcli', '%s e. CC' % TPI)],
              'a1i', '( %s -> %s e. CC )' % (As, TPI))
    tpn = w.s([w.s([w.s([], '2cn', '2 e. CC'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC')], 'mulcli', '( _i x. _pi ) e. CC'),
                    w.s([], '2ne0', '2 =/= 0'), w.s([w.s([], 'ax-icn', '_i e. CC'), w.s([], 'picn', '_pi e. CC'), w.s([], 'ine0', '_i =/= 0'), w.s([], 'pine0', '_pi =/= 0')], 'mulne0i', '( _i x. _pi ) =/= 0')],
                   'mulne0i', '%s =/= 0' % TPI)], 'a1i', '( %s -> %s =/= 0 )' % (As, TPI))
    t1c = t([c2, tpc, tpn], 'divcld', '%s e. CC' % T1)
    # chain
    r1 = t([tce], 'oveq2d', '( ( ! ` n ) x. %s ) = ( ( ! ` n ) x. ( ( n + 1 ) x. %s ) )' % (TC(FI('( j + 1 )'), 'P', 'R', 'n'), T1))
    r2 = t([fyc, n1c, t1c], 'mulassd', '( ( ( ! ` n ) x. ( n + 1 ) ) x. %s ) = ( ( ! ` n ) x. ( ( n + 1 ) x. %s ) )' % (T1, T1))
    r3 = t([t([nn, w.inst('facp1')], 'syl', '( ! ` ( n + 1 ) ) = ( ( ! ` n ) x. ( n + 1 ) )')], 'oveq1d',
           '( ( ! ` ( n + 1 ) ) x. %s ) = ( ( ( ! ` n ) x. ( n + 1 ) ) x. %s )' % (T1, T1))
    r4 = t([r3, r2], 'eqtrd', '( ( ! ` ( n + 1 ) ) x. %s ) = ( ( ! ` n ) x. ( ( n + 1 ) x. %s ) )' % (T1, T1))
    r5 = t([ihi, r1], 'eqtrd', '( %s ` P ) = ( ( ! ` n ) x. ( ( n + 1 ) x. %s ) )' % (FI('( ( j + 1 ) + n )'), T1))
    r6 = t([r5, r4], 'eqtr4d', '( %s ` P ) = ( ( ! ` ( n + 1 ) ) x. %s )' % (FI('( ( j + 1 ) + n )'), T1))
    r7 = t([l1, r6], 'eqtr3d', '( %s ` P ) = ( ( ! ` ( n + 1 ) ) x. %s )' % (FI('( j + ( n + 1 ) )'), T1))
    PSJ = PS('( n + 1 )').replace('A. i e. NN0', 'A. j e. NN0').replace(FI('( i + ( n + 1 ) )'), FI('( j + ( n + 1 ) )')).replace(FI('i'), FI('j'))
    stj = w.s([r7], 'ralrimiva', '( %s -> %s )' % (A1, PSJ))
    idj = w.s([], 'id', '( i = j -> i = j )')
    bj = lambda iv: '( %s ` P ) = ( ( ! ` ( n + 1 ) ) x. %s )' % (FI('( %s + ( n + 1 ) )' % iv), TC(FI(iv), 'P', 'R', '( n + 1 )'))
    cj, nj = w.wcongr(bj('i'), {'i': 'j'}, 'i = j', {'i': idj})
    assert nj == bj('j'), nj
    cbr = w.s([cj], 'cbvralvw', '( %s <-> %s )' % (PS('( n + 1 )'), PSJ))
    step = w.s([stj, cbr], 'sylibr', '( %s -> %s )' % (A1, PS('( n + 1 )')))

    ind = w.s([subs['0'], subs['y'], subs['y1'], subs['K'], base, step], 'nn0indd', '( ( %s /\\ K e. NN0 ) -> %s )' % (ph, PS('K')))
    A0 = S['kdcdn'].split(' -> ( ( ( CC Dn')[0][2:]
    f = lambda h, r, fm: w.s(h, r, '( %s -> %s )' % (A0, fm))
    h1 = f([], 'simp1', H); h2 = f([], 'simp2', SQH_); kk = f([], 'simp3', 'K e. NN0')
    pk = f([f([h1, h2], 'jca', ph), kk], 'jca', '( %s /\\ K e. NN0 )' % ph)
    psk = f([pk, ind], 'syl', PS('K'))
    bodyK = lambda iv: '( %s ` P ) = ( ( ! ` K ) x. %s )' % (FI('( %s + K )' % iv), TC(FI(iv), 'P', 'R', 'K'))
    idx0 = w.s([], 'id', '( i = 0 -> i = 0 )')
    c0, n0 = w.wcongr(bodyK('i'), {'i': '0'}, 'i = 0', {'i': idx0})
    assert n0 == bodyK('0'), n0
    rs0 = w.s([c0], 'rspcv', '( 0 e. NN0 -> ( %s -> %s ) )' % (PS('K'), bodyK('0')))
    z0 = w.s([w.s([], '0nn0', '0 e. NN0')], 'a1i', '( %s -> 0 e. NN0 )' % A0)
    b0 = f([z0, psk, rs0], 'sylc', bodyK('0'))
    pm, _ = pmcc(w, A0, h1, 'F', 'D')
    ccs = w.s([w.s([], 'ssid', 'CC C_ CC')], 'a1i', '( %s -> CC C_ CC )' % A0)
    d0 = f([ccs, pm, w.inst('dvn0')], 'syl2anc', '%s = F' % FI('0'))
    k0 = f([f([kk], 'nn0cnd', 'K e. CC')], 'addlidd', '( 0 + K ) = K')
    cl1, nl1 = w.congr('( %s ` P )' % FI('( 0 + K )'), {}, A0, {}, rules={'( 0 + K )': ('K', k0)})
    cr1, nr1 = w.congr('( ( ! ` K ) x. %s )' % TC(FI('0'), 'P', 'R', 'K'), {}, A0, {}, rules={FI('0'): ('F', d0)})
    w.qed([cl1, b0, cr1], '3eqtr3d', S['kdcdn'])
    return run(w)


if __name__ == '__main__':
    gen_cdn()
