"""Sortie KD1: the K-th derivative of the Landau remainder at s0 (kdrepg)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_repg():
    w = W('kdrepg', 'Lean ` KDerivDetect.kderiv_representation ` : the ` K ` -th derivative of the Landau remainder ` g ` at ` s0 = ( 1 + E ) + i T ` is the termwise one of ` -u sum chi Lam k ^ -u z - sum m / ( z - q ) ` ( ` kdtcs ` on the square ` SQ ( s0 , E / 2 ) ` in ` Re > 1 + E / 4 ` ).')
    A0 = S['kdrepg'].split(' -> ( ( ( CC Dn g )')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    kd = s([], 'simpl', KDH); hgp = s([], 'simpr', HGP())
    chi = s([kd], 'simpld', CHI)
    tek = s([kd], 'simprd', '( T e. RR /\\ ( E e. RR+ /\\ E <_ %s ) /\\ K e. NN0 )' % R120)
    tr = s([tek], 'simp1d', 'T e. RR'); ee = s([tek], 'simp2d', '( E e. RR+ /\\ E <_ %s )' % R120); kk = s([tek], 'simp3d', 'K e. NN0')
    ep = s([ee], 'simpld', 'E e. RR+'); er = s([ep], 'rpred', 'E e. RR'); e0 = s([ep], 'rpgt0d', '0 < E'); e20 = s([ee], 'simprd', 'E <_ %s' % R120)
    GID = 'A. z e. %s ( ( %s ` z ) =/= 0 -> ( g ` z ) = ( ( ( ( CC _D %s ) ` z ) / ( %s ` z ) ) - sum_ q e. %s ( %s / ( z - q ) ) ) )' % (O13, LFN, LFN, LFN, ZD(), MU())
    hg = s([hgp], 'simpld', HOLF('g', O13)); gid = s([hgp], 'simprd', GID)
    nx = s([chi], 'simpld', NXH)
    E2 = '( E / 2 )'; T1 = '( 1 + ( E / 4 ) )'; Bs = '( E / ; 1 6 )'; Cs = '( 1 / %s )' % Bs
    SS = S0()
    c = Closure(w, A0, {'T': ('RR', tr), 'E': ('RR', er)})
    e2p = s([ep], 'rphalfcld', '%s e. RR+' % E2)
    bsp = s([ep, c.mem('; 1 6', 'RR+')], 'rpdivcld', '%s e. RR+' % Bs)
    bsr = s([bsp], 'rpred', '%s e. RR' % Bs)
    csr = s([bsp], 'rprecred', '%s e. RR' % Cs)
    s0c = s([s([s([w.s([], '1red', '( %s -> 1 e. RR )' % A0), er], 'readdcld', '( 1 + E ) e. RR')], 'recnd', '( 1 + E ) e. CC'),
             s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SS)
    # geometry at R = 2 / 5
    r25 = s([s([c.mem('( 2 / 5 )', 'RR'), linarith(w, A0, [], '( 1 / 3 ) <_ ( 2 / 5 )', closure=c), linarith(w, A0, [], '( 2 / 5 ) <_ ( 2 / 5 )', closure=c)], '3jca',
                '( ( 2 / 5 ) e. RR /\\ ( 1 / 3 ) <_ ( 2 / 5 ) /\\ ( 2 / 5 ) <_ ( 2 / 5 ) )'),
             s([c.mem('( 1 / 3 )', 'RR'), c.mem('( 2 / 5 )', 'RR'), w.inst('elicc2')], 'syl2anc', '( ( 2 / 5 ) e. ( ( 1 / 3 ) [,] ( 2 / 5 ) ) <-> ( ( 2 / 5 ) e. RR /\\ ( 1 / 3 ) <_ ( 2 / 5 ) /\\ ( 2 / 5 ) <_ ( 2 / 5 ) ) )')],
            'mpbird', '( 2 / 5 ) e. ( ( 1 / 3 ) [,] ( 2 / 5 ) )')
    GEO = tsub(S['kdgeo'], {'R': '( 2 / 5 )'})
    ga, gc = split_imp(GEO)
    geo = s([tr, ee, r25, w.inst('kdgeo')], 'syl3anc', gc)
    g2 = s([geo], 'simprd', top_and(gc)[1])
    SQE = SQ(SS, E2)
    g3 = s([g2], 'simpld', '%s C_ %s' % (SQE, O13)); g4 = s([g2], 'simprd', '%s C_ %s' % (SQE, HP(T1)))
    # ef2ddl for the nonvanishing on Re > 1
    DDs = stmt('ef2ddl').split(' -> ', 1)[1][:-2]
    dd = s([chi, w.inst('ef2ddl')], 'syl', DDs)
    nv = s([s([dd], 'simp3d', top_and(DDs)[2])], 'simprd', top_and(top_and(DDs)[2])[1])
    NV = top_and(top_and(DDs)[2])[1]
    HP0_ = HP0
    # for z in HP(T1): LFN z =/= 0
    def nonzero(ante, zst_hp, zname='z'):
        a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (ante, f))
        L = lambda st: lift(w, st, ante)
        HT1 = HP(T1)
        ez = a([zst_hp, a([L(c.mem(T1, 'RR')), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ %s < ( Re ` %s ) ) )' % (zname, HT1, zname, T1, zname))], 'mpbid', '( %s e. CC /\\ %s < ( Re ` %s ) )' % (zname, T1, zname))
        zc = a([ez], 'simpld', '%s e. CC' % zname); zl = a([ez], 'simprd', '%s < ( Re ` %s )' % (T1, zname))
        cz = Closure(w, ante, {'E': ('RR', L(er)), '( Re ` %s )' % zname: ('RR', a([zc], 'recld', '( Re ` %s ) e. RR' % zname))})
        cz.atom('( Re ` %s )' % zname)
        z1 = linarith(w, ante, [zl, L(e0)], '1 < ( Re ` %s )' % zname, closure=cz)
        z0 = linarith(w, ante, [zl, L(e0)], '0 < ( Re ` %s )' % zname, closure=cz)
        zh = a([a([zc, z0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (zname, zname)), a([w.s([], '0red', '( %s -> 0 e. RR )' % ante), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (zname, HP0_, zname, zname))],
               'mpbird', '%s e. %s' % (zname, HP0_))
        idw = w.s([], 'id', '( w = %s -> w = %s )' % (zname, zname))
        cw, nw = w.wcongr('( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN, {'w': zname}, 'w = %s' % zname, {'w': idw})
        lz = a([a([zh, L(nv), w.s([cw], 'rspcv', '( %s e. %s -> ( %s -> %s ) )' % (zname, HP0_, NV, nw))], 'sylc', nw), z1], 'mpd', '( %s ` %s ) =/= 0' % (LFN, zname))
        return dict(zc=zc, z1=z1, lz=lz, zh=zh)
    INST = tsub(S['kdtcs'], {'G': 'g', 'D': O13, 'P': SS, 'R': E2, 'A': CVM, 'C': Cs, 'B': Bs, 'T': T1, 'Z': ZD(), 'W': WMM})
    ia, ic = split_imp(INST)
    assert ic == S['kdrepg'].split(' -> ', 1)[1][:-2] or True
    H1f, H2f, H3f = top_and(ia)
    # H1
    H1 = s([hg, s([s0c, e2p, g3], '3jca', top_and(H1f)[1])], 'jca', H1f)
    # H2: growth of chi Lam
    AGRf, ZHf = top_and(H2f)
    AGR1, TC1 = top_and(AGRf)
    Am = '( %s /\\ m e. NN )' % A0
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Am, f))
    L = lambda st: lift(w, st, Am)
    mn = a([], 'simpr', 'm e. NN')
    chm = a([a([L(nx), mn], 'jca', '( %s /\\ m e. NN )' % NXH), w.inst('lchrcl')], 'syl', '%s e. CC' % CHV('m'))
    lam = a([mn, w.inst('vmacl')], 'syl', '( Lam ` m ) e. RR')
    cvv = a([chm, a([lam], 'recnd', '( Lam ` m ) e. CC')], 'mulcld', '( %s x. ( Lam ` m ) ) e. CC' % CHV('m'))
    idn = w.s([], 'id', '( n = m -> n = m )')
    cn, vn = w.congr('( %s x. ( Lam ` n ) )' % CHV('n'), {'n': 'm'}, 'n = m', {'n': idn})
    cvm = fvmd(w, Am, CVM, 'm', vn, mn, cvv, cn, var='n')
    ab1 = a([chm, a([lam], 'recnd', '( Lam ` m ) e. CC')], 'absmuld', '( abs ` ( %s x. ( Lam ` m ) ) ) = ( ( abs ` %s ) x. ( abs ` ( Lam ` m ) ) )' % (CHV('m'), CHV('m')))
    lam0 = a([mn, w.inst('vmage0')], 'syl', '0 <_ ( Lam ` m )')
    ab2 = a([a([lam, lam0], 'absidd', '( abs ` ( Lam ` m ) ) = ( Lam ` m )')], 'oveq2d', '( ( abs ` %s ) x. ( abs ` ( Lam ` m ) ) ) = ( ( abs ` %s ) x. ( Lam ` m ) )' % (CHV('m'), CHV('m')))
    chb = a([a([L(nx), mn], 'jca', '( %s /\\ m e. NN )' % NXH), w.inst('lchrabs')], 'syl', '( abs ` %s ) <_ 1' % CHV('m'))
    l1 = a([a([chm], 'abscld', '( abs ` %s ) e. RR' % CHV('m')), w.s([], '1red', '( %s -> 1 e. RR )' % Am), lam, lam0, chb], 'lemul1ad', '( ( abs ` %s ) x. ( Lam ` m ) ) <_ ( 1 x. ( Lam ` m ) )' % CHV('m'))
    l2 = a([l1, a([a([lam], 'recnd', '( Lam ` m ) e. CC')], 'mullidd', '( 1 x. ( Lam ` m ) ) = ( Lam ` m )')], 'breqtrd', '( ( abs ` %s ) x. ( Lam ` m ) ) <_ ( Lam ` m )' % CHV('m'))
    l3 = a([a([ab1, ab2], 'eqtrd', '( abs ` ( %s x. ( Lam ` m ) ) ) = ( ( abs ` %s ) x. ( Lam ` m ) )' % (CHV('m'), CHV('m'))), l2], 'eqbrtrd', '( abs ` ( %s x. ( Lam ` m ) ) ) <_ ( Lam ` m )' % CHV('m'))
    l4 = a([mn, w.inst('vmalelog')], 'syl', '( Lam ` m ) <_ ( log ` m )')
    lp = a([L(bsp), w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % Am), mn, w.inst('kdlogpow')], 'syl3anc',
           '( ( log ` m ) ^ 1 ) <_ ( ( ( ! ` 1 ) x. ( m ^c %s ) ) / ( %s ^ 1 ) )' % (Bs, Bs))
    lmc = a([a([a([mn], 'nnrpd', 'm e. RR+')], 'relogcld', '( log ` m ) e. RR')], 'recnd', '( log ` m ) e. CC')
    mb = a([a([mn], 'nnrpd', 'm e. RR+'), L(bsr)], 'rpcxpcld', '( m ^c %s ) e. RR+' % Bs)
    mbc = a([mb], 'rpcnd', '( m ^c %s ) e. CC' % Bs)
    bsc = a([L(bsr)], 'recnd', '%s e. CC' % Bs); bsn = a([L(bsp)], 'rpne0d', '%s =/= 0' % Bs)
    x1 = a([lmc], 'exp1d', '( ( log ` m ) ^ 1 ) = ( log ` m )')
    x2 = a([bsc], 'exp1d', '( %s ^ 1 ) = %s' % (Bs, Bs))
    x3 = a([w.s([w.s([], 'fac1', '( ! ` 1 ) = 1')], 'a1i', '( %s -> ( ! ` 1 ) = 1 )' % Am)], 'oveq1d', '( ( ! ` 1 ) x. ( m ^c %s ) ) = ( 1 x. ( m ^c %s ) )' % (Bs, Bs))
    x4 = a([x3, a([mbc], 'mullidd', '( 1 x. ( m ^c %s ) ) = ( m ^c %s )' % (Bs, Bs))], 'eqtrd', '( ( ! ` 1 ) x. ( m ^c %s ) ) = ( m ^c %s )' % (Bs, Bs))
    x5 = a([x4, x2], 'oveq12d', '( ( ( ! ` 1 ) x. ( m ^c %s ) ) / ( %s ^ 1 ) ) = ( ( m ^c %s ) / %s )' % (Bs, Bs, Bs, Bs))
    x6 = a([mbc, bsc, bsn], 'divrec2d', '( ( m ^c %s ) / %s ) = ( %s x. ( m ^c %s ) )' % (Bs, Bs, Cs, Bs))
    lp2 = a([lp, x1, a([x5, x6], 'eqtrd', '( ( ( ! ` 1 ) x. ( m ^c %s ) ) / ( %s ^ 1 ) ) = ( %s x. ( m ^c %s ) )' % (Bs, Bs, Cs, Bs))], '3brtr3d', '( log ` m ) <_ ( %s x. ( m ^c %s ) )' % (Cs, Bs))
    cmr = a([L(csr), a([mb], 'rpred', '( m ^c %s ) e. RR' % Bs)], 'remulcld', '( %s x. ( m ^c %s ) ) e. RR' % (Cs, Bs))
    lgr = a([a([mn], 'nnrpd', 'm e. RR+')], 'relogcld', '( log ` m ) e. RR')
    l5 = a([a([cvv], 'abscld', '( abs ` ( %s x. ( Lam ` m ) ) ) e. RR' % CHV('m')), lam, lgr, l3, l4], 'letrd', '( abs ` ( %s x. ( Lam ` m ) ) ) <_ ( log ` m )' % CHV('m'))
    l6 = a([a([cvv], 'abscld', '( abs ` ( %s x. ( Lam ` m ) ) ) e. RR' % CHV('m')), lgr, cmr, l5, lp2], 'letrd', '( abs ` ( %s x. ( Lam ` m ) ) ) <_ ( %s x. ( m ^c %s ) )' % (CHV('m'), Cs, Bs))
    l7 = a([a([cvm], 'fveq2d', '( abs ` ( %s ` m ) ) = ( abs ` ( %s x. ( Lam ` m ) ) )' % (CVM, CHV('m'))), l6], 'eqbrtrd', '( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c %s ) )' % (CVM, Cs, Bs))
    gall = s([l7], 'ralrimiva', 'A. m e. NN ( abs ` ( %s ` m ) ) <_ ( %s x. ( m ^c %s ) )' % (CVM, Cs, Bs))
    An = '( %s /\\ n e. NN )' % A0
    nn_ = w.s([], 'simpr', '( %s -> n e. NN )' % An)
    cvf = s([w.s([w.s([w.s([lift(w, nx, An), nn_], 'jca', '( %s -> ( %s /\\ n e. NN ) )' % (An, NXH)), w.inst('lchrcl')], 'syl', '( %s -> %s e. CC )' % (An, CHV('n'))),
                   w.s([w.s([nn_, w.inst('vmacl')], 'syl', '( %s -> ( Lam ` n ) e. RR )' % An)], 'recnd', '( %s -> ( Lam ` n ) e. CC )' % An)], 'mulcld', '( %s -> ( %s x. ( Lam ` n ) ) e. CC )' % (An, CHV('n')))],
            'fmptd', '%s : NN --> CC' % CVM)
    agr = s([cvf, csr, s([bsp, gall], 'jca', top_and(AGR1)[2])], '3jca', AGR1)
    tc1 = s([c.mem(T1, 'RR'), linarith(w, A0, [e0], '( 1 + ( 2 x. %s ) ) < %s' % (Bs, T1), closure=c)], 'jca', TC1)
    # ZH
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    lzp = top_and(lzc)
    zfin = s([lz], 'simp1d', lzp[0]); zord = s([lz], 'simp2d', lzp[1])
    SQ13 = SQ(CT('T'), R138)
    from kd1_q import corners
    cct = s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
            'addcld', '%s e. CC' % CT('T'))
    RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
    ric = s([s([c.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([c.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
            'addcld', '%s e. CC' % RI_)
    sqcc = s([s([s([cct, ric], 'subcld', '%s e. CC' % A13), s([cct, ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
    zdcc = s([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (A0, ZD(), SQ13)), sqcc], 'sstrd', '%s C_ CC' % ZD())
    Ap = '( %s /\\ p e. %s )' % (A0, ZD())
    pp = w.s([], 'simpr', '( %s -> p e. %s )' % (Ap, ZD()))
    cmp = w.s([w.s([], 'oveq2', '( q = p -> %s = %s )' % (MU('q'), MU('p')))], 'eleq1d', '( q = p -> ( %s e. NN <-> %s e. NN ) )' % (MU('q'), MU('p')))
    mpn = w.s([pp, lift(w, zord, Ap), w.s([cmp], 'rspcv', '( p e. %s -> ( %s -> %s e. NN ) )' % (ZD(), lzp[1], MU('p')))], 'sylc', '( %s -> %s e. NN )' % (Ap, MU('p')))
    wf = s([w.s([mpn], 'nncnd', '( %s -> %s e. CC )' % (Ap, MU('p')))], 'fmptd', '%s : %s --> CC' % (WMM, ZD()))
    zh = s([zfin, zdcc, wf], '3jca', ZHf)
    H2 = s([s([agr, tc1], 'jca', AGRf), zh], 'jca', H2f)
    # H3
    VS, ALLf, KF = top_and(H3f)
    Av = '( %s /\\ v e. %s )' % (A0, SQE)
    b = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Av, f))
    Lv = lambda st: lift(w, st, Av)
    vin = b([], 'simpr', 'v e. %s' % SQE)
    vht = b([Lv(g4), vin], 'sseldd', 'v e. %s' % HP(T1))
    nzv = nonzero(Av, vht, 'v')
    ely = w.s([w.s([], 'fveqeq2', '( r = v -> ( ( %s ` r ) = 0 <-> ( %s ` v ) = 0 ) )' % (LFN, LFN))], 'elrab', '( v e. %s <-> ( v e. %s /\\ ( %s ` v ) = 0 ) )' % (ZD(), SQ13, LFN))
    nzd = b([b([nzv['lz']], 'neneqd', '-. ( %s ` v ) = 0' % LFN), w.s([w.s([ely], 'simprbi', '( v e. %s -> ( %s ` v ) = 0 )' % (ZD(), LFN))], 'con3i', '( -. ( %s ` v ) = 0 -> -. v e. %s )' % (LFN, ZD()))],
            'syl', '-. v e. %s' % ZD())
    VSv = VS.split(' C_ ', 1)[1]
    vvs = b([b([vht, nzd], 'jca', '( v e. %s /\\ -. v e. %s )' % (HP(T1), ZD())), w.s([], 'eldif', '( v e. %s <-> ( v e. %s /\\ -. v e. %s ) )' % (VSv, HP(T1), ZD()))], 'sylibr', 'v e. %s' % VSv)
    vss = s([w.s([vvs], 'ex', '( %s -> ( v e. %s -> v e. %s ) )' % (A0, SQE, VSv))], 'ssrdv', VS)
    # g v = PSINST(0, v)
    vo = b([Lv(g3), vin], 'sseldd', 'v e. %s' % O13)
    RZ = GID[len('A. z e. %s ' % O13):]
    idzv = w.s([], 'id', '( z = v -> z = v )')
    czv, rv = w.wcongr(RZ, {'z': 'v'}, 'z = v', {'z': idzv})
    gv0 = b([vo, Lv(gid), w.s([czv], 'rspcv', '( v e. %s -> ( %s -> %s ) )' % (O13, GID, rv))], 'sylc', rv)
    gv1 = b([nzv['lz'], gv0], 'mpd', split_imp(rv)[1])
    LDv = '( ( ( CC _D %s ) ` v ) / ( %s ` v ) )' % (LFN, LFN)
    SV = 'sum_ k e. NN ( ( %s x. ( Lam ` k ) ) x. ( k ^c -u v ) )' % CHV('k')
    ld = b([Lv(chi), b([nzv['zc'], nzv['z1']], 'jca', '( v e. CC /\\ 1 < ( Re ` v ) )'), w.inst('kdlogdv')], 'syl2anc', '%s = -u %s' % (LDv, SV))
    PS0 = tsub(S['kdps0'], {'z': 'v'})
    pa, pc_ = split_imp(PS0)
    ps0 = b([b([b([Lv(chi), Lv(tr)], 'jca', '( %s /\\ T e. RR )' % CHI), nzv['zc']], 'jca', '( ( %s /\\ T e. RR ) /\\ v e. CC )' % CHI), nzd, w.inst('kdps0')], 'syl2anc', pc_)
    SQv = 'sum_ q e. %s ( %s / ( v - q ) )' % (ZD(), MU())
    gv2 = b([gv1, b([ld], 'oveq1d', '( %s - %s ) = ( -u %s - %s )' % (LDv, SQv, SV, SQv))], 'eqtrd', '( g ` v ) = ( -u %s - %s )' % (SV, SQv))
    PSv = PSINST('0', 'v')
    gv3 = b([gv2, ps0], 'eqtr4d', '( g ` v ) = %s' % PSv)
    allv = s([gv3], 'ralrimiva', 'A. v e. %s ( g ` v ) = %s' % (SQE, PSv))
    BZ = ALLf[len('A. z e. %s ' % SQE):]
    idz2 = w.s([], 'id', '( z = v -> z = v )')
    cz2, bv2 = w.wcongr(BZ, {'z': 'v'}, 'z = v', {'z': idz2})
    assert bv2 == '( g ` v ) = %s' % PSv, (bv2[:200], PSv[:200])
    allz = s([allv, w.s([cz2], 'cbvralvw', '( %s <-> A. v e. %s %s )' % (ALLf, SQE, bv2))], 'sylibr', ALLf)
    H3 = s([vss, allz, kk], '3jca', H3f)
    w.qed([H1, H2, H3, w.inst('kdtcs')], 'syl3anc', S['kdrepg'])
    return run(w)




if __name__ == '__main__':
    gen_repg()
