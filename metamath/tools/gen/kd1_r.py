"""Sortie KD1: the Landau remainder g = L'/L - sum_rho m/(z - rho) is holomorphic on the open 13/8 square (kdrem)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift
from lin import linarith

only = sys.argv[1:]
TOP = '( TopOpen ` CCfld )'


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def stmt_tree(label):
    return stmt(label)


def gen_rem():
    w = W('kdrem', 'Lean ` KDerivDetect.exists_logDeriv_remainder ` (identity part): for ` chi ` nonprincipal, ` g = h \' / h ` for ZC1\'s cofactor ` h ` ( ` zdfac ` ) is holomorphic on the open ` 13 / 8 ` square about ` 2 + i T ` and equals ` L \' / L - sum m / ( z - q ) ` at every non-zero of ` L ` there (EF2 ` ef2lds ` ).')
    A0 = '( %s /\\ T e. RR )' % CHI
    s = lambda h_, r, f: w.s(h_, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI); tr = s([], 'simpr', 'T e. RR')
    DDs = stmt('ef2ddl').split(' -> ', 1)[1][:-2]
    dd = s([chi, w.inst('ef2ddl')], 'syl', DDs)
    from cl import split_imp
    def conj3(f):
        from c9lib import top_and
        return top_and(f)
    from c9lib import top_and
    parts = top_and(DDs)
    hol = s([dd], 'simp1d', parts[0]); nn1 = s([dd], 'simp2d', parts[1]); rest = s([dd], 'simp3d', parts[2])
    nv = s([rest], 'simprd', top_and(parts[2])[1])
    HP0_ = HP0
    CC_ = CT('T')
    c0 = Closure(w, A0, {'T': ('RR', tr)})
    ccc = s([s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CC_)], 'id', 'T.') if False else \
        s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % CC_)
    rc = s([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % A0), tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = 2' % CC_)
    c0.leaf('( Re ` %s )' % CC_, 'RR', s([ccc], 'recld', '( Re ` %s ) e. RR' % CC_)); c0.atom('( Re ` %s )' % CC_)
    cgt0 = linarith(w, A0, [rc], '0 < ( Re ` %s )' % CC_, closure=c0)
    cgt1 = linarith(w, A0, [rc], '1 < ( Re ` %s )' % CC_, closure=c0)
    chp = s([s([ccc, cgt0], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (CC_, CC_)), s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (CC_, HP0_, CC_, CC_))],
            'mpbird', '%s e. %s' % (CC_, HP0_))
    NVs = top_and(parts[2])[1]  # A. w e. HP0 ( 1 < ( Re ` w ) -> ( LFN ` w ) =/= 0 )
    body = NVs.split(' ( 1 < ', 1)[1]
    idw = w.s([], 'id', '( w = %s -> w = %s )' % (CC_, CC_))
    cw, nw = w.wcongr('( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN, {'w': CC_}, 'w = %s' % CC_, {'w': idw})
    fc = s([s([chp, nv, w.s([cw], 'rspcv', '( %s e. %s -> ( %s -> %s ) )' % (CC_, HP0_, NVs, nw))], 'sylc', nw), cgt1], 'mpd', '( %s ` %s ) =/= 0' % (LFN, CC_))
    from c8lib import tsub
    ZDF = tsub(stmt('zdfac'), {'F': LFN})
    ZA, ZC = ZDF[2:-2].split(' -> ', 1) if False else (None, None)
    from cl import split_imp
    za, zc = split_imp(ZDF)
    ex_h = s([hol, tr, fc, w.inst('zdfac')], 'syl3anc', zc)
    Hh = zc[len('E. h '):]
    Ah = '( %s /\\ %s )' % (A0, Hh)
    t = lambda h_, r, f: w.s(h_, r, '( %s -> %s )' % (Ah, f))
    L = lambda st: lift(w, st, Ah)
    hp = top_and(Hh)
    hh = t([], 'simp1' if False else 'simpr', Hh)
    hhol = t([hh], 'simp1d', hp[0]); hfac = t([hh], 'simp2d', hp[1]); hnz = t([hh], 'simp3d', hp[2])
    A_, B_ = A13, B13
    k13 = Closure(w, Ah, {'T': ('RR', L(tr))})
    r13 = k13.mem(R138, 'RR')
    from kd1_q import corners
    K = corners(w, Ah, CC_, R138, L(ccc), L(rc), t([w.s([w.s([], '2re', '2 e. RR')], 'a1i', '( %s -> 2 e. RR )' % Ah), L(tr), w.inst('crim')], 'syl2anc', '( Im ` %s ) = T' % CC_), r13)
    k13.leaf('( Re ` %s )' % A_, 'RR', t([K['lo']], 'recld', '( Re ` %s ) e. RR' % A_)); k13.atom('( Re ` %s )' % A_)
    ra0 = linarith(w, Ah, [K['ReA']], '0 < ( Re ` %s )' % A_, closure=k13)
    SQ13 = SQ(CC_, R138)
    rhp = t([t([K['lo'], K['hi']], 'jca', '( %s e. CC /\\ %s e. CC )' % (A_, B_)), ra0, w.inst('ef2rhp')], 'syl2anc', '( %s C_ %s /\\ %s C_ ( CC \\ { 0 } ) )' % (SQ13, HP0_, SQ13))
    sqhp = t([rhp], 'simpld', '%s C_ %s' % (SQ13, HP0_))
    osq = t([K['lo'], K['hi'], w.inst('orectss')], 'syl2anc', '%s C_ %s' % (O13, SQ13))
    ohp = t([osq, sqhp], 'sstrd', '%s C_ %s' % (O13, HP0_))
    oop = w.s([w.s([], 'orectopn', '%s e. %s' % (O13, TOP))], 'a1i', '( %s -> %s e. %s )' % (Ah, O13, TOP))
    Hz = '( z e. %s |-> ( h ` z ) )' % O13; Hx = '( x e. %s |-> ( h ` x ) )' % O13
    Hdz = '( z e. %s |-> ( ( CC _D h ) ` z ) )' % O13; Hdx = '( x e. %s |-> ( ( CC _D h ) ` x ) )' % O13
    oj = t([oop, ohp], 'jca', '( %s e. %s /\\ %s C_ %s )' % (O13, TOP, O13, HP0_))
    hz = t([hhol, oj, w.inst('zl2hres')], 'syl2anc', HOLF(Hz, O13))
    hdh = t([hhol, w.inst('ef2dvh')], 'syl', HOLF('( CC _D h )', HP0_))
    hdz = t([hdh, oj, w.inst('zl2hres')], 'syl2anc', HOLF(Hdz, O13))
    cb1 = w.s([w.s([], 'fveq2', '( z = x -> ( h ` z ) = ( h ` x ) )')], 'cbvmptv', '%s = %s' % (Hz, Hx))
    cb2 = w.s([w.s([], 'fveq2', '( z = x -> ( ( CC _D h ) ` z ) = ( ( CC _D h ) ` x ) )')], 'cbvmptv', '%s = %s' % (Hdz, Hdx))
    hx = t([hz, holeq(w, Ah, w.s([cb1], 'a1i', '( %s -> %s = %s )' % (Ah, Hz, Hx)), Hz, Hx, O13)], 'mpbid', HOLF(Hx, O13))
    hdx = t([hdz, holeq(w, Ah, w.s([cb2], 'a1i', '( %s -> %s = %s )' % (Ah, Hdz, Hdx)), Hdz, Hdx, O13)], 'mpbid', HOLF(Hdx, O13))
    # values of Hx, Hdx at a point y of O
    def vals(ante, y, yin):
        a = lambda h_, r, f: w.s(h_, r, '( %s -> %s )' % (ante, f))
        M = lambda st: lift(w, st, ante)
        ysq = a([M(osq), yin], 'sseldd', '%s e. %s' % (y, SQ13))
        yhp = a([M(ohp), yin], 'sseldd', '%s e. %s' % (y, HP0_))
        hf = a([a([M(hhol), w.inst('simpl')], 'syl', 'h e. ( %s -cn-> CC )' % HP0_), w.inst('cncff')], 'syl', 'h : %s --> CC' % HP0_)
        hy = a([hf, yhp], 'ffvelcdmd', '( h ` %s ) e. CC' % y)
        hdf = a([M(hhol), w.inst('holf')], 'syl', '( CC _D h ) : %s --> CC' % HP0_)
        hdy = a([hdf, yhp], 'ffvelcdmd', '( ( CC _D h ) ` %s ) e. CC' % y)
        v1 = fvmd(w, ante, Hx, y, '( h ` %s )' % y, yin, hy, w.s([], 'fveq2', '( x = %s -> ( h ` x ) = ( h ` %s ) )' % (y, y)), var='x')
        v2 = fvmd(w, ante, Hdx, y, '( ( CC _D h ) ` %s )' % y, yin, hdy, w.s([], 'fveq2', '( x = %s -> ( ( CC _D h ) ` x ) = ( ( CC _D h ) ` %s ) )' % (y, y)), var='x')
        hn = a([M(hnz), ysq, w.s([w.s([], 'fveq2', '( z = %s -> ( h ` z ) = ( h ` %s ) )' % (y, y))], 'neeq1d', '( z = %s -> ( ( h ` z ) =/= 0 <-> ( h ` %s ) =/= 0 ) )' % (y, y)) and
                w.s([w.s([w.s([], 'fveq2', '( z = %s -> ( h ` z ) = ( h ` %s ) )' % (y, y))], 'neeq1d', '( z = %s -> ( ( h ` z ) =/= 0 <-> ( h ` %s ) =/= 0 ) )' % (y, y))], 'rspcv',
                    '( %s e. %s -> ( A. z e. %s ( h ` z ) =/= 0 -> ( h ` %s ) =/= 0 ) )' % (y, SQ13, SQ13, y))], 'T.', 'T.') if False else \
            a([ysq, M(hnz), w.s([w.s([w.s([], 'fveq2', '( z = %s -> ( h ` z ) = ( h ` %s ) )' % (y, y))], 'neeq1d', '( z = %s -> ( ( h ` z ) =/= 0 <-> ( h ` %s ) =/= 0 ) )' % (y, y))], 'rspcv',
                                   '( %s e. %s -> ( A. z e. %s ( h ` z ) =/= 0 -> ( h ` %s ) =/= 0 ) )' % (y, SQ13, SQ13, y))], 'sylc', '( h ` %s ) =/= 0' % y)
        return dict(v1=v1, v2=v2, hn=hn, hy=hy, hdy=hdy, ysq=ysq)
    Av = '( %s /\\ v e. %s )' % (Ah, O13)
    vv = vals(Av, 'v', w.s([], 'simpr', '( %s -> v e. %s )' % (Av, O13)))
    xnz = w.s([vv['v1'], vv['hn']], 'eqnetrd', '( %s -> ( %s ` v ) =/= 0 )' % (Av, Hx))
    xall = t([xnz], 'ralrimiva', 'A. v e. %s ( %s ` v ) =/= 0' % (O13, Hx))
    G0 = '( z e. %s |-> ( ( %s ` z ) / ( %s ` z ) ) )' % (O13, Hdx, Hx)
    hg0 = t([hdx, hx, xall, w.inst('holdiv')], 'syl3anc', HOLF(G0, O13))
    G0z = G0
    G0 = '( w e. %s |-> ( ( %s ` w ) / ( %s ` w ) ) )' % (O13, Hdx, Hx)
    cbg = w.s([w.s([w.s([], 'fveq2', '( z = w -> ( %s ` z ) = ( %s ` w ) )' % (Hdx, Hdx)), w.s([], 'fveq2', '( z = w -> ( %s ` z ) = ( %s ` w ) )' % (Hx, Hx))], 'oveq12d',
                   '( z = w -> ( ( %s ` z ) / ( %s ` z ) ) = ( ( %s ` w ) / ( %s ` w ) ) )' % (Hdx, Hx, Hdx, Hx))], 'cbvmptv', '%s = %s' % (G0z, G0))
    hg = t([hg0, holeq(w, Ah, w.s([cbg], 'a1i', '( %s -> %s = %s )' % (Ah, G0z, G0)), G0z, G0, O13)], 'mpbid', HOLF(G0, O13))
    # the identity at a non-zero y of O
    LFNj = LFN.replace('sum_ k e. NN', 'sum_ j e. NN').replace('( 1 ... k )', '( 1 ... j )').replace('( k ^c -u s )', '( j ^c -u s )').replace('( ( k + 1 ) ^c -u s )', '( ( j + 1 ) ^c -u s )')
    bodyk = LFN.split(' |-> ', 1)[1][:-2]
    idkj = w.s([], 'id', '( k = j -> k = j )')
    ckj, nkj = w.congr(bodyk.split('sum_ k e. NN ', 1)[1], {'k': 'j'}, 'k = j', {'k': idkj})
    sj = w.s([ckj], 'cbvsumv', '%s = sum_ j e. NN %s' % (bodyk, nkj))
    eqL = w.s([sj], 'mpteq2i', '%s = %s' % (LFN, LFNj))
    assert '( s e. %s |-> sum_ j e. NN %s )' % (HP0_, nkj) == LFNj, (LFNj, nkj)
    EQ = '%s = %s' % (LFN, LFNj); EQb = '%s = %s' % (LFNj, LFN)
    ide = w.s([], 'id', '( %s -> %s )' % (EQ, EQ)); ideb = w.s([], 'id', '( %s -> %s )' % (EQb, EQb))
    eqLr = w.s([eqL], 'eqcomi', EQb)
    cdd, ddj_f = w.wcongr(DDs, {}, EQ, {}, rules={LFN: (LFNj, ide)})
    ddj = t([L(dd), w.s([w.s([eqL, cdd], 'ax-mp', '( %s <-> %s )' % (DDs, ddj_f))], 'a1i', '( %s -> ( %s <-> %s ) )' % (Ah, DDs, ddj_f))], 'mpbid', ddj_f)
    chh, hhj_f = w.wcongr(Hh, {}, EQ, {}, rules={LFN: (LFNj, ide)})
    hhj = t([hh, w.s([w.s([eqL, chh], 'ax-mp', '( %s <-> %s )' % (Hh, hhj_f))], 'a1i', '( %s -> ( %s <-> %s ) )' % (Ah, Hh, hhj_f))], 'mpbid', hhj_f)
    LDS = tsub(stmt('ef2lds'), {'F': LFNj, 'A': 'N'})
    la, lcj = split_imp(LDS)
    ldsj = t([t([ddj, L(tr)], 'jca', top_and(la)[0]), hhj, w.inst('ef2lds')], 'syl2anc', lcj)
    Ay = '( ( %s /\\ y e. %s ) /\\ ( %s ` y ) =/= 0 )' % (Ah, O13, LFN)
    u = lambda h_, r, f: w.s(h_, r, '( %s -> %s )' % (Ay, f))
    M = lambda st: lift(w, st, Ay)
    yin = w.s([w.s([], 'simpr', '( ( %s /\\ y e. %s ) -> y e. %s )' % (Ah, O13, O13))], 'adantr', '( %s -> y e. %s )' % (Ay, O13))
    lny = u([], 'simpr', '( %s ` y ) =/= 0' % LFN)
    vy = vals(Ay, 'y', yin)
    ZDs = ZD()
    ely = w.s([w.s([], 'fveqeq2', '( r = y -> ( ( %s ` r ) = 0 <-> ( %s ` y ) = 0 ) )' % (LFN, LFN))], 'elrab', '( y e. %s <-> ( y e. %s /\\ ( %s ` y ) = 0 ) )' % (ZDs, SQ13, LFN))
    nz1 = u([lny], 'neneqd', '-. ( %s ` y ) = 0' % LFN)
    nz2 = u([nz1, w.s([ely, w.inst('simprbi')], 'syl', '( y e. %s -> ( %s ` y ) = 0 )' % (ZDs, LFN))], 'T.', 'T.') if False else \
        u([w.s([w.s([ely], 'simprbi', '( y e. %s -> ( %s ` y ) = 0 )' % (ZDs, LFN))], 'con3i', '( -. ( %s ` y ) = 0 -> -. y e. %s )' % (LFN, ZDs)), nz1], 'T.', 'T.') if False else \
        u([nz1, w.s([w.s([ely], 'simprbi', '( y e. %s -> ( %s ` y ) = 0 )' % (ZDs, LFN))], 'con3i', '( -. ( %s ` y ) = 0 -> -. y e. %s )' % (LFN, ZDs))], 'syl', '-. y e. %s' % ZDs)
    ydf = u([u([vy['ysq'], nz2], 'jca', '( y e. %s /\\ -. y e. %s )' % (SQ13, ZDs)), w.s([], 'eldif', '( y e. ( %s \\ %s ) <-> ( y e. %s /\\ -. y e. %s ) )' % (SQ13, ZDs, SQ13, ZDs))],
            'sylibr', 'y e. ( %s \\ %s )' % (SQ13, ZDs))
    ZDj = ZDs.replace(LFN, LFNj)
    cyd, yd_j = w.wcongr('y e. ( %s \\ %s )' % (SQ13, ZDs), {}, EQ, {}, rules={LFN: (LFNj, ide)})
    ydfj = u([ydf, w.s([w.s([eqL, cyd], 'ax-mp', '( y e. ( %s \\ %s ) <-> %s )' % (SQ13, ZDs, yd_j))], 'a1i', '( %s -> ( y e. ( %s \\ %s ) <-> %s ) )' % (Ay, SQ13, ZDs, yd_j))], 'mpbid', yd_j)
    Xz = 'A. z e. ( %s \\ %s ) ' % (SQ13, ZDj)
    assert lcj.startswith(Xz), lcj[:200]
    bz = lcj[len(Xz):]
    idy = w.s([], 'id', '( z = y -> z = y )')
    cz, byj = w.wcongr(bz, {'z': 'y'}, 'z = y', {'z': idy})
    iyj = u([ydfj, M(ldsj), w.s([cz], 'rspcv', '( %s -> ( %s -> %s ) )' % (yd_j, lcj, byj))], 'sylc', byj)
    SKj = 'sum_ k e. %s ( ( %s holord k ) / ( y - k ) )' % (ZDj, LFNj)
    SQj = 'sum_ q e. %s ( ( %s holord q ) / ( y - q ) )' % (ZDj, LFNj)
    idk = w.s([], 'id', '( k = q -> k = q )')
    ck, nk = w.congr('( ( %s holord k ) / ( y - k ) )' % LFNj, {'k': 'q'}, 'k = q', {'k': idk})
    cbs = w.s([ck], 'cbvsumv', '%s = %s' % (SKj, SQj))
    LDj = '( ( ( CC _D %s ) ` y ) / ( %s ` y ) )' % (LFNj, LFNj)
    HD = '( ( ( CC _D h ) ` y ) / ( h ` y ) )'
    assert byj == '%s = ( %s + %s )' % (LDj, SKj, HD), byj
    iyq = u([iyj, u([w.s([cbs], 'a1i', '( %s -> %s = %s )' % (Ay, SKj, SQj))], 'oveq1d', '( %s + %s ) = ( %s + %s )' % (SKj, HD, SQj, HD))], 'eqtrd', '%s = ( %s + %s )' % (LDj, SQj, HD))
    FJ = '%s = ( %s + %s )' % (LDj, SQj, HD)
    cfb, fb_ = w.wcongr(FJ, {}, EQb, {}, rules={LFNj: (LFN, ideb)})
    SQs = 'sum_ q e. %s ( %s / ( y - q ) )' % (ZDs, MU())
    LD = '( ( ( CC _D %s ) ` y ) / ( %s ` y ) )' % (LFN, LFN)
    assert fb_ == '%s = ( %s + %s )' % (LD, SQs, HD), fb_
    iy2 = u([iyq, w.s([w.s([eqLr, cfb], 'ax-mp', '( %s <-> %s )' % (FJ, fb_))], 'a1i', '( %s -> ( %s <-> %s ) )' % (Ay, FJ, fb_))], 'mpbid', fb_)
    # SQs e. CC
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = u([u([M(chi), M(tr)], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    lzp = top_and(lzc)
    zfn = u([lz], 'simp1d', lzp[0]); zord = u([lz], 'simp2d', lzp[1])
    Ayq = '( %s /\\ p e. %s )' % (Ay, ZDs)
    qq = w.s([], 'simpr', '( %s -> p e. %s )' % (Ayq, ZDs))
    qsq = w.s([qq, w.s([], 'ssrab2', '%s C_ %s' % (ZDs, SQ13)) and w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZDs, SQ13))], 'a1i', '( %s -> %s C_ %s )' % (Ayq, ZDs, SQ13))], 'T.', 'T.') if False else \
        w.s([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZDs, SQ13))], 'a1i', '( %s -> %s C_ %s )' % (Ayq, ZDs, SQ13)), qq], 'sseldd', '( %s -> p e. %s )' % (Ayq, SQ13))
    sqcc = w.s([w.s([lift(w, K['lo'], Ayq), lift(w, K['hi'], Ayq)], 'jca', '( %s -> ( %s e. CC /\\ %s e. CC ) )' % (Ayq, A_, B_)), w.inst('crectss')], 'syl', '( %s -> %s C_ CC )' % (Ayq, SQ13))
    qc = w.s([sqcc, qsq], 'sseldd', '( %s -> p e. CC )' % Ayq)
    yc = w.s([w.s([lift(w, sqcc, Ayq) if False else sqcc, w.s([vy['ysq']], 'adantr', '( %s -> y e. %s )' % (Ayq, SQ13))], 'sseldd', '( %s -> y e. CC )' % Ayq)], 'id', 'T.') if False else \
        w.s([sqcc, w.s([vy['ysq']], 'adantr', '( %s -> y e. %s )' % (Ayq, SQ13))], 'sseldd', '( %s -> y e. CC )' % Ayq)
    # y =/= q: q is a zero, y is not
    qz0 = w.s([qq, w.s([w.s([], 'fveqeq2', '( r = p -> ( ( %s ` r ) = 0 <-> ( %s ` p ) = 0 ) )' % (LFN, LFN))], 'elrab', '( p e. %s <-> ( p e. %s /\\ ( %s ` p ) = 0 ) )' % (ZDs, SQ13, LFN)) and
               w.s([w.s([w.s([], 'fveqeq2', '( r = p -> ( ( %s ` r ) = 0 <-> ( %s ` p ) = 0 ) )' % (LFN, LFN))], 'elrab', '( p e. %s <-> ( p e. %s /\\ ( %s ` p ) = 0 ) )' % (ZDs, SQ13, LFN))], 'simprbi', '( p e. %s -> ( %s ` p ) = 0 )' % (ZDs, LFN))],
              'syl', '( %s -> ( %s ` p ) = 0 )' % (Ayq, LFN))
    # ( LFN ` y ) =/= ( LFN ` q ) hence y =/= q
    lnq = w.s([w.s([lny], 'adantr', '( %s -> ( %s ` y ) =/= 0 )' % (Ayq, LFN)), qz0], 'neeqtrrd', '( %s -> ( %s ` y ) =/= ( %s ` p ) )' % (Ayq, LFN, LFN))
    ynq = w.s([lnq, w.s([], 'fveq2', '( y = p -> ( %s ` y ) = ( %s ` p ) )' % (LFN, LFN))], 'T.', 'T.') if False else \
        w.s([lnq], 'fvneq2d' if False else 'T.', 'T.') if False else \
        w.s([w.s([w.s([], 'fveq2', '( y = p -> ( %s ` y ) = ( %s ` p ) )' % (LFN, LFN))], 'necon3i', '( ( %s ` y ) =/= ( %s ` p ) -> y =/= p )' % (LFN, LFN)) and
             w.s([w.s([], 'fveq2', '( y = p -> ( %s ` y ) = ( %s ` p ) )' % (LFN, LFN))], 'necon3i', '( ( %s ` y ) =/= ( %s ` p ) -> y =/= p )' % (LFN, LFN)), lnq][::-1], 'T.', 'T.') if False else \
        w.s([lnq, w.s([w.s([], 'fveq2', '( y = p -> ( %s ` y ) = ( %s ` p ) )' % (LFN, LFN))], 'necon3i', '( ( %s ` y ) =/= ( %s ` p ) -> y =/= p )' % (LFN, LFN))], 'syl', '( %s -> y =/= p )' % Ayq)
    MUq = MU('p')
    cmp = w.s([w.s([], 'oveq2', '( q = p -> %s = %s )' % (MU('q'), MU('p')))], 'eleq1d', '( q = p -> ( %s e. NN <-> %s e. NN ) )' % (MU('q'), MU('p')))
    zoq = w.s([qq, w.s([zord], 'adantr', '( %s -> %s )' % (Ayq, lzp[1])), w.s([cmp], 'rspcv', '( p e. %s -> ( %s -> %s e. NN ) )' % (ZDs, lzp[1], MU('p')))], 'sylc', '( %s -> %s e. NN )' % (Ayq, MUq))
    tq = w.s([w.s([zoq], 'nncnd', '( %s -> %s e. CC )' % (Ayq, MUq)), w.s([yc, qc], 'subcld', '( %s -> ( y - p ) e. CC )' % Ayq), w.s([yc, qc, ynq], 'subne0d', '( %s -> ( y - p ) =/= 0 )' % Ayq)],
             'divcld', '( %s -> ( %s / ( y - p ) ) e. CC )' % (Ayq, MUq))
    SQp = 'sum_ p e. %s ( %s / ( y - p ) )' % (ZDs, MU('p'))
    idqp = w.s([], 'id', '( q = p -> q = p )')
    cqp, nqp = w.congr('( %s / ( y - q ) )' % MU('q'), {'q': 'p'}, 'q = p', {'q': idqp})
    cbqp = w.s([cqp], 'cbvsumv', '%s = %s' % (SQs, SQp))
    sqc = u([w.s([cbqp], 'a1i', '( %s -> %s = %s )' % (Ay, SQs, SQp)), u([zfn, tq], 'fsumcl', '%s e. CC' % SQp)], 'eqeltrd', '%s e. CC' % SQs)
    hdc = u([vy['hdy'], vy['hy'], vy['hn']], 'divcld', '%s e. CC' % HD)
    e1 = u([sqc, hdc], 'pncan2d', '( ( %s + %s ) - %s ) = %s' % (SQs, HD, SQs, HD))
    e2 = u([iy2], 'oveq1d', '( %s - %s ) = ( ( %s + %s ) - %s )' % (LD, SQs, SQs, HD, SQs))
    e3 = u([e2, e1], 'eqtrd', '( %s - %s ) = %s' % (LD, SQs, HD))
    gv0 = fvmd(w, Ay, G0, 'y', '( ( %s ` y ) / ( %s ` y ) )' % (Hdx, Hx), yin, u([u([vy['v2'], vy['hdy']], 'eqeltrd', '( %s ` y ) e. CC' % Hdx), u([vy['v1'], vy['hy']], 'eqeltrd', '( %s ` y ) e. CC' % Hx),
                                                                                   u([vy['v1'], vy['hn']], 'eqnetrd', '( %s ` y ) =/= 0' % Hx)], 'divcld', '( ( %s ` y ) / ( %s ` y ) ) e. CC' % (Hdx, Hx)),
               w.s([w.s([], 'fveq2', '( w = y -> ( %s ` w ) = ( %s ` y ) )' % (Hdx, Hdx)), w.s([], 'fveq2', '( w = y -> ( %s ` w ) = ( %s ` y ) )' % (Hx, Hx))], 'oveq12d',
                   '( w = y -> ( ( %s ` w ) / ( %s ` w ) ) = ( ( %s ` y ) / ( %s ` y ) ) )' % (Hdx, Hx, Hdx, Hx)), var='w')
    gv1 = u([gv0, u([vy['v2'], vy['v1']], 'oveq12d', '( ( %s ` y ) / ( %s ` y ) ) = %s' % (Hdx, Hx, HD))], 'eqtrd', '( %s ` y ) = %s' % (G0, HD))
    gv = u([gv1, e3], 'eqtr4d', '( %s ` y ) = ( %s - %s )' % (G0, LD, SQs))
    RY = '( ( %s ` y ) =/= 0 -> ( %s ` y ) = ( %s - %s ) )' % (LFN, G0, LD, SQs)
    gex = w.s([gv], 'ex', '( ( %s /\\ y e. %s ) -> %s )' % (Ah, O13, RY))
    gall = t([gex], 'ralrimiva', 'A. y e. %s %s' % (O13, RY))
    RZ = '( ( %s ` z ) =/= 0 -> ( %s ` z ) = ( ( ( ( CC _D %s ) ` z ) / ( %s ` z ) ) - sum_ q e. %s ( %s / ( z - q ) ) ) )' % (LFN, G0, LFN, LFN, ZDs, MU('q'))
    idzy = w.s([], 'id', '( z = y -> z = y )')
    czy, nzy = w.wcongr(RZ, {'z': 'y'}, 'z = y', {'z': idzy})
    assert nzy == RY, (nzy, RY)
    zall = t([gall, w.s([czy], 'cbvralvw', '( A. z e. %s %s <-> A. y e. %s %s )' % (O13, RZ, O13, RY))], 'sylibr', 'A. z e. %s %s' % (O13, RZ))
    CH = '( %s /\\ A. z e. %s %s )' % (HOLF(G0, O13), O13, RZ)
    ch = t([hg, zall], 'jca', CH)
    PS = S['kdrem'].split(' -> E. g ')[1][:-2]
    idg = w.s([], 'id', '( g = %s -> g = %s )' % (G0, G0))
    cg, ng = w.wcongr(PS, {'g': G0}, 'g = %s' % G0, {'g': idg})
    assert ng == CH, (ng[:300], CH[:300])
    exg = t([t([hg], 'simpld', '%s e. ( %s -cn-> CC )' % (G0, O13)), ch, cg], 'spcedv', 'E. g %s' % PS)
    w.qed([ex_h, exg], 'exlimddv', S['kdrem'])
    return run(w)




if __name__ == '__main__':
    gen_rem()
