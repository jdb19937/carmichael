"""Sortie LD2, section 6 part 3: the family (ld2mrds ld2mmass ld2hp6 ld2mvu ld2mvw ld2int ld2trs ld2lim) and the finish
(ld2cexp ld2num ld2ssq).  Run: MM_DB=sorties/ld2.mm MM_ENGINE=mmatch python3 tools/gen/ld2_d.py [LABEL ...]"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ld2lib import *
from ld2_c import hab0, ptwfacts_light

only = sys.argv[1:]
want = lambda l: not only or l in only
L = LOGD
IS = '( Im ` S )'; RS = '( Re ` S )'
D2 = '( 2 x. D )'
FZM = '( 1 ... %s )' % M2D
BVL = lambda d: '( ( D bvLam ( 2 x. D ) ) ` %s )' % d
AFB = lambda d: '( %s x. ( %s ^c -u ( 1 / 2 ) ) )' % (BVL(d), d)
YU = lambda U: '( q e. F |-> ( ( Im ` ( Y ` q ) ) + %s ) )' % U
LOG3F = LOG3


def rrss(w, A):
    return a1(w, A, 'ax-resscn', 'RR C_ CC')


from cl import ante_path


def child(w, ante, c, leaves=None):
    """a closure at ANTE (which contains c.ante as a right-nested conjunct) whose missing facts
    are lifted from c through one intermediate closure per level (Closure's parent = one adantr)"""
    path = ante_path(c.ante, ante)
    assert path is not None, (c.ante, ante)
    cur = c
    for i, (lemma, a) in enumerate(path):
        assert lemma == 'adantr', (lemma, a)
        cur = Closure(w, a, leaves if i == len(path) - 1 else None, parent=cur)
    if not path:
        cur = Closure(w, ante, leaves, parent=None)
    return cur


def cxvald(w, An, nstep, X, n):
    """( An -> ( CX(X) ` n ) = CHV(X, n) )"""
    ex = a1(w, An, 'fvex', '%s e. _V' % CHV(X, n))
    return fvmd(w, An, 'a', 'NN', CHV(X, 'a'), n, nstep, ex)


def ld2mrds():
    w = W('ld2mrds', 'Lean ` hMr ` of ` sum_sq_norm_Mr_le ` : on the half line the mollifier ` Mr ( S + ( 1/2 - Re S ) + i u ) ` is MV\'s Dirichlet polynomial with the coefficients ` bvLam ( n ) n ^ -1/2 ` , the character values and the frequency ` Im S + u ` (~ dshmr1 , ~ ld1cpow , ~ cbvsumv ).')
    A = ante('ld2mrds'); P = parts(w, A)
    dr, d1, nn, xb, sc, ur = P['D e. RR'], P['1 < D'], P['N e. NN'], P['X e. %s' % DB()], P['S e. CC'], P['U e. RR']
    c = Closure(w, A, {'D': [('RR', dr), ('gt1', d1)], 'S': ('CC', sc), 'U': ('RR', ur), 'N': ('NN', nn), '_i': ('CC', a1(w, A, 'ax-icn', '_i e. CC'))})
    c.leaf(RS, 'RR', dst(w, A, [sc], 'recld', '%s e. RR' % RS)); c.leaf(IS, 'RR', dst(w, A, [sc], 'imcld', '%s e. RR' % IS))
    h0 = hab0(w, A, c, dr, d1)
    CXX = CX()
    lif = ap(w, A, 'zl1lif', [J(w, A, nn, xb)], concl('zl1lif'))
    Q = parts(w, A, top=body(w, lif, A), step=lif)
    cxf = Q['%s : NN --> CC' % CXX]
    Z = '( S + %s )' % HLU('U')
    zc = c.mem(Z, 'CC')
    mr = ap(w, A, 'dshmr1', [h0, J(w, A, cxf, zc)], subst(concl('dshmr1'), {'A': 'D', 'B': D2, 'C': CXX, 'S': Z}))
    SUMD = 'sum_ d e. %s ( ( %s x. ( %s ` d ) ) x. ( d ^c -u %s ) )' % (FZM, BVL('d'), CXX, Z)
    assert body(w, mr, A).endswith(SUMD), body(w, mr, A)[-200:]
    # Re Z = 1/2, Im Z = Im S + U
    hlr = c.mem(HL, 'RR')
    rez = eqt(w, A, dst(w, A, [sc, c.mem(HLU('U'), 'CC')], 'readdd', '( Re ` %s ) = ( %s + ( Re ` %s ) )' % (Z, RS, HLU('U'))),
              eqt(w, A, dst(w, A, [dst(w, A, [hlr, ur], 'crred', '( Re ` %s ) = %s' % (HLU('U'), HL))], 'oveq2d', '( %s + ( Re ` %s ) ) = ( %s + %s )' % (RS, HLU('U'), RS, HL)), ringeq(w, A, '( %s + %s )' % (RS, HL), '( 1 / 2 )', c)))
    imz = eqt(w, A, dst(w, A, [sc, c.mem(HLU('U'), 'CC')], 'imaddd', '( Im ` %s ) = ( %s + ( Im ` %s ) )' % (Z, IS, HLU('U'))),
              dst(w, A, [dst(w, A, [hlr, ur], 'crimd', '( Im ` %s ) = U' % HLU('U'))], 'oveq2d', '( %s + ( Im ` %s ) ) = ( %s + U )' % (IS, HLU('U'), IS)))
    # rename the summation variable d -> n first (the coefficient map AF binds d), then transform the summand
    TD0 = '( ( %s x. ( %s ` d ) ) x. ( d ^c -u %s ) )' % (BVL('d'), CXX, Z)
    cg0, TN0 = w.congr(TD0, {'d': 'n'}, 'd = n', {'d': w.s([], 'id', '( d = n -> d = n )')})
    cs0 = w.s([cg0], 'cbvsumv', '%s = sum_ n e. %s %s' % (SUMD, FZM, TN0))
    mr2 = eqt(w, A, mr, w.s([cs0], 'a1i', '( %s -> %s = sum_ n e. %s %s )' % (A, SUMD, FZM, TN0)))
    An = '( %s /\\ n e. %s )' % (A, FZM)
    nN = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZM))], 'n e. NN')
    cn = Closure(w, An, {'D': [('RR', lift(w, dr, An)), ('gt1', lift(w, d1, An))], 'S': ('CC', lift(w, sc, An)), 'U': ('RR', lift(w, ur, An)), 'n': ('NN', nN), '_i': ('CC', a1(w, An, 'ax-icn', '_i e. CC'))})
    cn.leaf(RS, 'RR', lift(w, c.mem(RS, 'RR'), An)); cn.leaf(IS, 'RR', lift(w, c.mem(IS, 'RR'), An))
    cn.have('D', 'gt0', linarith(w, An, [lift(w, d1, An)], '0 < D', closure=Closure(w, An, {'D': ('RR', lift(w, dr, An))})))
    rp3 = J(w, An, cn.mem('D', 'RR+'), cn.mem(D2, 'RR+'), linarith(w, An, [lift(w, d1, An)], 'D < %s' % D2, closure=cn))
    cn.leaf(BVL('n'), 'RR', ap(w, An, 'bvlamre', [rp3, nN], '%s e. RR' % BVL('n')))
    cxv = cxvald(w, An, nN, 'X', 'n')
    cn.leaf(CHV('X', 'n'), 'CC', dst(w, An, [cxv, dst(w, An, [lift(w, cxf, An), nN], 'ffvelcdmd', '( %s ` n ) e. CC' % CXX)], 'eqeltrrd', '%s e. CC' % CHV('X', 'n')))
    cp = ap(w, An, 'ld1cpow', [nN, lift(w, zc, An)], '( n ^c -u %s ) = ( ( n ^c -u ( Re ` %s ) ) x. %s )' % (Z, Z, NEX('n', '( Im ` %s )' % Z)))
    NX = NEX('n', '( %s + U )' % IS)
    cp2 = eqt(w, An, cp, dst(w, An, [dst(w, An, [dst(w, An, [lift(w, rez, An)], 'negeqd', '-u ( Re ` %s ) = -u ( 1 / 2 )' % Z)], 'oveq2d', '( n ^c -u ( Re ` %s ) ) = ( n ^c -u ( 1 / 2 ) )' % Z),
                                    dst(w, An, [dst(w, An, [dst(w, An, [lift(w, imz, An)], 'oveq2d', '( -u ( log ` n ) x. ( Im ` %s ) ) = ( -u ( log ` n ) x. ( %s + U ) )' % (Z, IS))], 'oveq2d',
                                                          '( _i x. ( -u ( log ` n ) x. ( Im ` %s ) ) ) = ( _i x. ( -u ( log ` n ) x. ( %s + U ) ) )' % (Z, IS))], 'fveq2d', '%s = %s' % (NEX('n', '( Im ` %s )' % Z), NX))],
                              'oveq12d', '( ( n ^c -u ( Re ` %s ) ) x. %s ) = ( ( n ^c -u ( 1 / 2 ) ) x. %s )' % (Z, NEX('n', '( Im ` %s )' % Z), NX)))
    cn.leaf(NX, 'CC', cn.mem(NX, 'CC')); cn.leaf('( n ^c -u ( 1 / 2 ) )', 'CC', cn.mem('( n ^c -u ( 1 / 2 ) )', 'CC'))
    t1 = dst(w, An, [dst(w, An, [cxv], 'oveq2d', '( %s x. ( %s ` n ) ) = ( %s x. %s )' % (BVL('n'), CXX, BVL('n'), CHV('X', 'n'))), cp2], 'oveq12d',
             '%s = ( ( %s x. %s ) x. ( ( n ^c -u ( 1 / 2 ) ) x. %s ) )' % (TN0, BVL('n'), CHV('X', 'n'), NX))
    afv = fvmd(w, An, 'd', 'NN', AFB('d'), 'n', nN, cn.mem(AFB('n'), 'CC'))
    rg = ringeq(w, An, '( ( %s x. %s ) x. ( ( n ^c -u ( 1 / 2 ) ) x. %s ) )' % (BVL('n'), CHV('X', 'n'), NX), '( ( %s x. %s ) x. %s )' % (AFB('n'), CHV('X', 'n'), NX), cn)
    TN = '( ( ( %s ` n ) x. %s ) x. %s )' % (AF, CHV('X', 'n'), NX)
    t2 = eqt(w, An, t1, eqt(w, An, rg, dst(w, An, [dst(w, An, [eqc(w, An, afv)], 'oveq1d', '( %s x. %s ) = ( ( %s ` n ) x. %s )' % (AFB('n'), CHV('X', 'n'), AF, CHV('X', 'n')))], 'oveq1d',
                                             '( ( %s x. %s ) x. %s ) = %s' % (AFB('n'), CHV('X', 'n'), NX, TN))))
    assert 'sum_ n e. %s %s' % (FZM, TN) == DSX('X', '( %s + U )' % IS), TN
    se = dst(w, A, [t2], 'sumeq2dv', 'sum_ n e. %s %s = %s' % (FZM, TN0, DSX('X', '( %s + U )' % IS)))
    eqt(w, A, mr2, se)
    return fin(w)


def ld2mmass():
    w = W('ld2mmass', 'Lean ` mollifier_mass_le ` : ` sum_ ( n <_ 2 D ) ( 1 + log ^ 2 n ) abs ( bvLam ( n ) n ^ -1/2 ) ^ 2 <_ 2 log ^ 3 D ` for ` log D >_ 40 ` (~ z5lamabs , ~ harmonicubnd , ~ log2le1 ).')
    A = HZH; P = parts(w, A); c, F = basecl(w, A, P)
    dr, d1, dl = F['dr'], F['d1'], F['dl']
    c.leaf(L, 'ge0', linarith(w, A, [dl], '0 <_ %s' % L, closure=c))
    h0 = hab0(w, A, c, dr, d1)
    LD2 = '( log ` %s )' % D2
    c.leaf(LD2, 'RR', c.mem(LD2, 'RR'))
    An = '( %s /\\ n e. %s )' % (A, FZM)
    nin = w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZM))
    nN = ap(w, An, 'elfznn', [nin], 'n e. NN')
    cn = Closure(w, An, {'D': [('RR+', lift(w, F['rp'], An)), ('gt1', lift(w, d1, An))], 'n': ('NN', nN), L: [('RR', lift(w, F['lr'], An)), ('ge0', lift(w, c.ge0(L), An))]})
    cn.leaf(LD2, 'RR', lift(w, c.mem(LD2, 'RR'), An))
    rp3 = J(w, An, cn.mem('D', 'RR+'), cn.mem(D2, 'RR+'), linarith(w, An, [lift(w, d1, An)], 'D < %s' % D2, closure=cn))
    bl = ap(w, An, 'bvlamre', [rp3, nN], '%s e. RR' % BVL('n')); cn.leaf(BVL('n'), 'RR', bl)
    afv = fvmd(w, An, 'd', 'NN', AFB('d'), 'n', nN, cn.mem(AFB('n'), 'CC'))
    cn.leaf('( %s ` n )' % AF, 'CC', dst(w, An, [afv, cn.mem(AFB('n'), 'CC')], 'eqeltrd', '( %s ` n ) e. CC' % AF))
    NH = '( n ^c -u ( 1 / 2 ) )'
    cn.leaf(NH, 'RR+', cn.mem(NH, 'RR+'))
    ab = eqt(w, An, dst(w, An, [afv], 'fveq2d', '( abs ` ( %s ` n ) ) = ( abs ` %s )' % (AF, AFB('n'))),
             eqt(w, An, dst(w, An, [cn.mem(BVL('n'), 'CC'), cn.mem(NH, 'CC')], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (AFB('n'), BVL('n'), NH)),
                 dst(w, An, [dst(w, An, [cn.mem(NH, 'RR'), cn.ge0(NH)], 'absidd', '( abs ` %s ) = %s' % (NH, NH))], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. %s )' % (BVL('n'), NH, BVL('n'), NH))))
    ABL = '( abs ` %s )' % BVL('n')
    cn.leaf(ABL, 'RR', cn.mem(ABL, 'RR')); cn.leaf(ABL, 'ge0', cn.ge0(ABL))
    la = ap(w, An, 'z5lamabs', [lift(w, h0, An), nN], '%s <_ 1' % ABL)
    sq = eqt(w, An, dst(w, An, [ab], 'oveq1d', '( ( abs ` ( %s ` n ) ) ^ 2 ) = ( ( %s x. %s ) ^ 2 )' % (AF, ABL, NH)), dst(w, An, [cn.mem(ABL, 'CC'), cn.mem(NH, 'CC')], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (ABL, NH, ABL, NH)))
    l1 = dst(w, An, [ap(w, An, 'le2sq2', [J(w, An, cn.mem(ABL, 'RR'), cn.ge0(ABL)), J(w, An, w.s([], '1red', '( %s -> 1 e. RR )' % An), la)], '( %s ^ 2 ) <_ ( 1 ^ 2 )' % ABL), a1(w, An, 'sq1', '( 1 ^ 2 ) = 1')], 'breqtrd', '( %s ^ 2 ) <_ 1' % ABL)
    # ( n ^c -1/2 ) ^ 2 = 1 / n
    e1 = ap(w, An, 'cxpexp', [cn.mem(NH, 'CC'), a1(w, An, '2nn0', '2 e. NN0')], '( %s ^c 2 ) = ( %s ^ 2 )' % (NH, NH))
    e2 = ap(w, An, 'cxpmul', [cn.mem('n', 'RR+'), cn.mem('-u ( 1 / 2 )', 'RR'), cn.mem('2', 'CC')], '( n ^c ( -u ( 1 / 2 ) x. 2 ) ) = ( %s ^c 2 )' % NH)
    e3 = dst(w, An, [ringeq(w, An, '( -u ( 1 / 2 ) x. 2 )', '-u 1', cn)], 'oveq2d', '( n ^c ( -u ( 1 / 2 ) x. 2 ) ) = ( n ^c -u 1 )')
    e4 = ap(w, An, 'cxpneg', [cn.mem('n', 'CC'), cn.ne0('n'), w.s([], '1cnd', '( %s -> 1 e. CC )' % An)], '( n ^c -u 1 ) = ( 1 / ( n ^c 1 ) )')
    e5 = dst(w, An, [ap(w, An, 'cxp1', [cn.mem('n', 'CC')], '( n ^c 1 ) = n')], 'oveq2d', '( 1 / ( n ^c 1 ) ) = ( 1 / n )')
    nh2 = eqt(w, An, eqc(w, An, e1), eqt(w, An, eqc(w, An, e2), eqt(w, An, e3, eqt(w, An, e4, e5))))
    sq2 = eqt(w, An, sq, dst(w, An, [nh2], 'oveq2d', '( ( %s ^ 2 ) x. ( %s ^ 2 ) ) = ( ( %s ^ 2 ) x. ( 1 / n ) )' % (ABL, NH, ABL)))
    RN = '( 1 / n )'
    cn.leaf(RN, 'RR+', cn.mem(RN, 'RR+'))
    b1 = dst(w, An, [cn.mem('( %s ^ 2 )' % ABL, 'RR'), w.s([], '1red', '( %s -> 1 e. RR )' % An), cn.mem(RN, 'RR'), cn.ge0(RN), l1], 'lemul1ad', '( ( %s ^ 2 ) x. %s ) <_ ( 1 x. %s )' % (ABL, RN, RN))
    b2 = dst(w, An, [dst(w, An, [sq2, b1], 'eqbrtrd', '( ( abs ` ( %s ` n ) ) ^ 2 ) <_ ( 1 x. %s )' % (AF, RN)), dst(w, An, [cn.mem(RN, 'CC')], 'mullidd', '( 1 x. %s ) = %s' % (RN, RN))], 'breqtrd', '( ( abs ` ( %s ` n ) ) ^ 2 ) <_ %s' % (AF, RN))
    # log n <_ log 2D
    nle = ap(w, An, 'elfzle2', [nin], 'n <_ %s' % M2D)
    fl = ap(w, An, 'flle', [cn.mem(D2, 'RR')], '%s <_ %s' % (M2D, D2))
    m2r = dst(w, An, [ap(w, An, 'flcl', [cn.mem(D2, 'RR')], '%s e. ZZ' % M2D)], 'zred', '%s e. RR' % M2D)
    nle2 = dst(w, An, [cn.mem('n', 'RR'), m2r, cn.mem(D2, 'RR'), nle, fl], 'letrd', 'n <_ %s' % D2)
    lg = dst(w, An, [nle2, dst(w, An, [cn.mem('n', 'RR+'), cn.mem(D2, 'RR+')], 'logled', '( n <_ %s <-> ( log ` n ) <_ %s )' % (D2, LD2))], 'mpbid', '( log ` n ) <_ %s' % LD2)
    LN = '( log ` n )'
    cn.leaf(LN, 'RR', cn.mem(LN, 'RR'))
    ln0 = ap(w, An, 'logge0', [J(w, An, cn.mem('n', 'RR'), dst(w, An, [nN], 'nnge1d', '1 <_ n'))], '0 <_ %s' % LN)
    lsq = ap(w, An, 'le2sq2', [J(w, An, cn.mem(LN, 'RR'), ln0), J(w, An, cn.mem(LD2, 'RR'), lg)], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LN, LD2))
    P1 = '( 1 + ( %s ^ 2 ) )' % LN; P2 = '( 1 + ( %s ^ 2 ) )' % LD2
    cn.leaf('( %s ^ 2 )' % LN, 'RR', cn.mem('( %s ^ 2 )' % LN, 'RR')); cn.leaf('( %s ^ 2 )' % LD2, 'RR', cn.mem('( %s ^ 2 )' % LD2, 'RR'))
    p12 = linarith(w, An, [lsq], '%s <_ %s' % (P1, P2), closure=cn)
    AF2 = '( ( abs ` ( %s ` n ) ) ^ 2 )' % AF
    cn.leaf(AF2, 'RR', cn.mem(AF2, 'RR')); cn.leaf(AF2, 'ge0', cn.ge0(AF2))
    p1g = linarith(w, An, [cn.ge0('( %s ^ 2 )' % LN)], '0 <_ %s' % P1, closure=cn)
    pt = dst(w, An, [cn.mem(P1, 'RR'), cn.mem(P2, 'RR'), cn.mem(AF2, 'RR'), cn.mem(RN, 'RR'), p1g, cn.ge0(AF2), p12, b2], 'lemul12ad', '( %s x. %s ) <_ ( %s x. %s )' % (P1, AF2, P2, RN))
    fi = dst(w, A, [], 'fzfid', '%s e. Fin' % FZM)
    s1 = dst(w, A, [fi, cn.mem('( %s x. %s )' % (P1, AF2), 'RR'), cn.mem('( %s x. %s )' % (P2, RN), 'RR'), pt], 'fsumle', '%s <_ sum_ n e. %s ( %s x. %s )' % (SLA, FZM, P2, RN))
    s2 = dst(w, A, [fi, c.mem(P2, 'CC'), cn.mem(RN, 'CC')], 'fsummulc2', '( %s x. sum_ n e. %s %s ) = sum_ n e. %s ( %s x. %s )' % (P2, FZM, RN, FZM, P2, RN))
    # the harmonic sum
    hb = ap(w, A, 'harmonicubnd', [J(w, A, c.mem(D2, 'RR'), linarith(w, A, [d1], '1 <_ %s' % D2, closure=c))], 'sum_ m e. %s ( 1 / m ) <_ ( %s + 1 )' % (FZM, LD2))
    cg, _ = w.congr('( 1 / m )', {'m': 'n'}, 'm = n', {'m': w.s([], 'id', '( m = n -> m = n )')})
    cs = w.s([cg], 'cbvsumv', 'sum_ m e. %s ( 1 / m ) = sum_ n e. %s ( 1 / n )' % (FZM, FZM))
    HS = 'sum_ n e. %s ( 1 / n )' % FZM
    hb2 = dst(w, A, [w.s([cs], 'a1i', '( %s -> sum_ m e. %s ( 1 / m ) = %s )' % (A, FZM, HS)), hb], 'eqbrtrrd', '%s <_ ( %s + 1 )' % (HS, LD2))
    hsr = dst(w, A, [fi, cn.mem(RN, 'RR')], 'fsumrecl', '%s e. RR' % HS)
    c.leaf(HS, 'RR', hsr); c.leaf(HS, 'ge0', dst(w, A, [fi, cn.mem(RN, 'RR'), cn.ge0(RN)], 'fsumge0', '0 <_ %s' % HS))
    p2g = linarith(w, A, [c.ge0('( %s ^ 2 )' % LD2)], '0 <_ %s' % P2, closure=c)
    s3 = dst(w, A, [hsr, c.mem('( %s + 1 )' % LD2, 'RR'), c.mem(P2, 'RR'), p2g, hb2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. ( %s + 1 ) )' % (P2, HS, P2, LD2))
    # log 2D <_ L + 1 and the cubic
    lm = dst(w, A, [c.mem('2', 'RR+'), c.mem('D', 'RR+')], 'relogmuld', '%s = ( ( log ` 2 ) + %s )' % (LD2, L))
    c.leaf('( log ` 2 )', 'RR', c.mem('( log ` 2 )', 'RR'))
    l21 = a1(w, A, 'log2le1', '( log ` 2 ) < 1')
    ld2le = linarith(w, A, [lm, l21], '%s <_ ( %s + 1 )' % (LD2, L), closure=c)
    ld20 = ap(w, A, 'logge0', [J(w, A, c.mem(D2, 'RR'), linarith(w, A, [d1], '1 <_ %s' % D2, closure=c))], '0 <_ %s' % LD2)
    L1 = '( %s + 1 )' % L
    lsq2 = ap(w, A, 'le2sq2', [J(w, A, c.mem(LD2, 'RR'), ld20), J(w, A, c.mem(L1, 'RR'), ld2le)], '( %s ^ 2 ) <_ ( %s ^ 2 )' % (LD2, L1))
    P3 = '( 1 + ( %s ^ 2 ) )' % L1
    c.have('( %s ^ 2 )' % L1, 'RR', c.mem('( %s ^ 2 )' % L1, 'RR')); c.leaf('( %s ^ 2 )' % LD2, 'RR', c.mem('( %s ^ 2 )' % LD2, 'RR'))
    p23 = linarith(w, A, [lsq2], '%s <_ %s' % (P2, P3), closure=c)
    q1 = linarith(w, A, [ld2le], '( %s + 1 ) <_ ( %s + 2 )' % (LD2, L), closure=c)
    q0 = linarith(w, A, [ld20], '0 <_ ( %s + 1 )' % LD2, closure=c)
    s4 = dst(w, A, [c.mem(P2, 'RR'), c.mem(P3, 'RR'), c.mem('( %s + 1 )' % LD2, 'RR'), c.mem('( %s + 2 )' % L, 'RR'), p2g, q0, p23, q1], 'lemul12ad', '( %s x. ( %s + 1 ) ) <_ ( %s x. ( %s + 2 ) )' % (P2, LD2, P3, L))
    # ( 1 + ( L + 1 ) ^ 2 ) ( L + 2 ) <_ 2 L ^ 3 for L >_ 40
    lsq0 = dst(w, A, [c.mem(L, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % L)
    cub = nlinarith(w, A, [dl, c.ge0(L), lsq0], '( %s x. ( %s + 2 ) ) <_ ( 2 x. ( %s ^ 3 ) )' % (P3, L, L), closure=c)
    # chain
    T1 = 'sum_ n e. %s ( %s x. %s )' % (FZM, P2, RN)
    ch1 = dst(w, A, [s1, eqc(w, A, s2)], 'breqtrd', '%s <_ ( %s x. %s )' % (SLA, P2, HS))
    for e_ in (SLA, T1, '( %s x. %s )' % (P2, HS), '( %s x. ( %s + 1 ) )' % (P2, LD2), '( %s x. ( %s + 2 ) )' % (P3, L), '( 2 x. ( %s ^ 3 ) )' % L):
        c.leaf(e_, 'RR', c.mem(e_, 'RR') if e_ != SLA else dst(w, A, [fi, cn.mem('( %s x. %s )' % (P1, AF2), 'RR')], 'fsumrecl', '%s e. RR' % SLA))
    linarith(w, A, [ch1, s3, s4, cub], '%s <_ ( 2 x. ( %s ^ 3 ) )' % (SLA, L), closure=c)
    return fin(w)


def famsetup(w, A):
    """parts, base closure (D, log D, YP, N, V, T) and the family pieces for an antecedent A containing HFAM"""
    P = parts(w, A); c, F = basecl(w, A, P)
    F['nN'] = P['N e. NN']; F['vr'] = P['V e. RR']; F['v2'] = P['2 <_ V']; F['deq'] = P['D = ( N x. ( V + 2 ) )']
    F['tr'] = P['T e. RR']; F['t39'] = P['( ; 3 9 / ; 5 0 ) <_ T']; F['t1'] = P['T <_ 1']
    F['fin'] = P['F e. Fin']; F['kf'] = P['K : F --> %s' % DB()]; F['yf'] = P['Y : F --> CC']; F['pts'] = P[PTS]; F['sep'] = P[SEPY]
    c.leaf('N', 'NN', F['nN']); c.leaf('V', 'RR', F['vr']); c.leaf('T', 'RR', F['tr'])
    c.leaf(L, 'ge0', linarith(w, A, [F['dl']], '0 <_ %s' % L, closure=c))
    F['hfam'] = P[HFAM] if HFAM in P else w.s([], 'id', '( %s -> %s )' % (HFAM, HFAM))
    return P, c, F


def ptsat(w, A, F, Z, zin):
    """PTS at a := Z (step zin: ( A -> Z e. F )): the four facts as a dict"""
    body_ = PTS[len('A. a e. F '):]
    ins, new = inst_forall(w, A, F['pts'], 'a', body_, Z, zin)
    Q = parts(w, A, top=new, step=ins)
    YZ_ = YZ(Z)
    return {'tre': Q['T <_ ( Re ` %s )' % YZ_], 're1': Q['( Re ` %s ) <_ 1' % YZ_], 'im': Q['( abs ` ( Im ` %s ) ) <_ V' % YZ_],
            'ne1': Q['%s =/= 1' % YZ_], 'zero': Q['( ( N DChrLF %s ) ` %s ) = 0' % (KZ(Z), YZ_)]}


def ld2hp6():
    w = W('ld2hp6', 'The per-member hypotheses of the family: at an index ` Z e. F ` the character values ` CX ( K Z ) ` , the L-function ` N DChrLF ( K Z ) ` and the point ` Y Z ` satisfy the pointwise hypotheses ` HP6 ` of Lemma 3.6 (~ zl1lif , ~ zl3cvxh , the family clauses).')
    A = ante('ld2hp6'); P, c, F = famsetup(w, A)
    zin = P['Z e. F']
    KZ_, YZ_ = KZ('Z'), YZ('Z'); CXZ = CX(KZ_); LFZ = LFX(KZ_)
    kz = dst(w, A, [F['kf'], zin], 'ffvelcdmd', '%s e. %s' % (KZ_, DB()))
    yz = dst(w, A, [F['yf'], zin], 'ffvelcdmd', '%s e. CC' % YZ_)
    c.leaf(YZ_, 'CC', yz)
    Q = ptsat(w, A, F, 'Z', zin)
    nx = J(w, A, F['nN'], kz)
    lif1 = ap(w, A, 'zl1lif', [nx], subst(concl('zl1lif'), {'X': KZ_}))
    cvx = ap(w, A, 'zl3cvxh', [nx], subst(concl('zl3cvxh'), {'X': KZ_}))
    QL = parts(w, A, top=body(w, lif1, A), step=lif1)
    CHRBZ = subst(CHRB, {'C': CXZ})
    EHOLZ = subst(EHOL, {'E': LFZ}); E1Z = '( %s ` 1 ) = %s' % (LFZ, subst(RESV, {'C': CXZ}))
    DSERZ = subst(DSER, {'C': CXZ, 'E': LFZ})
    cf = QL['%s : NN --> CC' % CXZ]; cb = QL[subst(CB, {'C': CXZ})]
    lif = J(w, A, J(w, A, QL[EHOLZ], QL[E1Z]), J(w, A, QL[DSERZ], cvx))
    lo = dst(w, A, [c.mem('( ; 3 9 / ; 5 0 )', 'RR'), c.mem('T', 'RR'), c.mem('( Re ` %s )' % YZ_, 'RR'), F['t39'], Q['tre']], 'letrd', '( ; 3 9 / ; 5 0 ) <_ ( Re ` %s )' % YZ_)
    sr = J(w, A, yz, J(w, A, lo, Q['re1']))
    a7 = J(w, A, J(w, A, J(w, A, F['hz'], F['nN']), J(w, A, J(w, A, cf, cb), J(w, A, sr, Q['ne1']))), J(w, A, lif, Q['zero']))
    # HDN: N ( abs Im Y Z + 2 ) <_ N ( V + 2 ) = D
    AI = '( abs ` ( Im ` %s ) )' % YZ_
    c.leaf(AI, 'RR', c.mem(AI, 'RR'))
    h1 = dst(w, A, [c.mem('( %s + 2 )' % AI, 'RR'), c.mem('( V + 2 )', 'RR'), c.mem('N', 'RR'), c.ge0('N'), linarith(w, A, [Q['im']], '( %s + 2 ) <_ ( V + 2 )' % AI, closure=c)], 'lemul2ad',
             '( N x. ( %s + 2 ) ) <_ ( N x. ( V + 2 ) )' % AI)
    hdn = dst(w, A, [h1, eqc(w, A, F['deq'])], 'breqtrd', '( N x. ( %s + 2 ) ) <_ D' % AI)
    hp = J(w, A, a7, J(w, A, hdn, J(w, A, F['tr'], J(w, A, F['t39'], Q['tre']))))
    assert body(w, hp, A) == HP6K('Z'), (body(w, hp, A)[:400], HP6K('Z')[:400])
    return fin(w)


def member(w, Ar, P, c, F, r):
    """under Ar = ( A /\\ r e. F ) (A containing HFAM): HP6K(r) and its parts, the character/point facts"""
    rin = w.s([], 'simpr', '( %s -> %s e. F )' % (Ar, r))
    hp = ap(w, Ar, 'ld2hp6', [J(w, Ar, lift(w, F['hfam'], Ar), rin)], HP6K(r))
    Q = parts(w, Ar, top=HP6K(r), step=hp)
    M = dict(hp=hp, Q=Q, rin=rin)
    KZ_, YZ_ = KZ(r), YZ(r); M['cxz'] = CX(KZ_); M['lfz'] = LFX(KZ_)
    M['kz'] = dst(w, Ar, [lift(w, F['kf'], Ar), rin], 'ffvelcdmd', '%s e. %s' % (KZ_, DB()))
    M['yz'] = dst(w, Ar, [lift(w, F['yf'], Ar), rin], 'ffvelcdmd', '%s e. CC' % YZ_)
    M['cf'] = Q['%s : NN --> CC' % M['cxz']]
    M['a7c'] = Q[subst(A7C, FAM(r))]
    return M


def macl(w, Ar, c, F, M, r, U, ur):
    """( Ar -> MAK(r,U) e. RR ) and 0 <_"""
    Z = subst('( S + %s )' % HLU(U), {'S': YZ(r)})
    c.leaf(YZ(r), 'CC', M['yz']); c.leaf('( Re ` %s )' % YZ(r), 'RR', dst(w, Ar, [M['yz']], 'recld', '( Re ` %s ) e. RR' % YZ(r)))
    c.leaf(U, 'RR', ur)
    c.leaf('_i', 'CC', a1(w, Ar, 'ax-icn', '_i e. CC'))
    h0 = hab0(w, Ar, c, F['dr'], F['d1'])
    mc = ap(w, Ar, 'z5mrcl', [J(w, Ar, h0, a1(w, Ar, '1nn', '1 e. NN')), J(w, Ar, M['cf'], c.mem(Z, 'CC'))], '%s e. CC' % subst(MRU(U), FAM(r)))
    mar = dst(w, Ar, [mc], 'abscld', '%s e. RR' % MAK(r, U)); ma0 = dst(w, Ar, [mc], 'absge0d', '0 <_ %s' % MAK(r, U))
    c.leaf(MAK(r, U), 'RR', mar); c.leaf(MAK(r, U), 'ge0', ma0)
    return mar, ma0


def ld2mvu():
    w = W('ld2mvu', 'Lean ` sum_sq_norm_Mr_le ` (Lemma 3.7 at a fixed ` u ` ): ` sum_ r abs M ( 1/2 + i ( Im rho_r + u ) , chi_r ) ^ 2 <_ 400 D log ^ 3 D ( 3 + abs u ) ` (MV\'s ~ mvdfam at ` T = V + abs u ` with the shifted points, ~ ld2mrds , ~ ld2mmass ).')
    A = ante('ld2mvu'); P, c, F = famsetup(w, A)
    ur = P['U e. RR']; c.leaf('U', 'RR', ur)
    AU = '( abs ` U )'; c.leaf(AU, 'RR', c.mem(AU, 'RR')); c.leaf(AU, 'ge0', c.ge0(AU))
    TU = '( V + %s )' % AU
    YUU = YU('U')
    # HLV
    t2 = linarith(w, A, [F['v2'], c.ge0(AU)], '2 <_ %s' % TU, closure=c)
    m2 = ap(w, A, 'flge0nn0', [J(w, A, c.mem(D2, 'RR'), c.ge0(D2))], '%s e. NN0' % M2D)
    Ak = '( %s /\\ k e. %s )' % (A, FZM)
    kN = ap(w, Ak, 'elfznn', [w.s([], 'simpr', '( %s -> k e. %s )' % (Ak, FZM))], 'k e. NN')
    ck = Closure(w, Ak, {'D': [('RR+', lift(w, F['rp'], Ak)), ('gt1', lift(w, F['d1'], Ak))], 'k': ('NN', kN)})
    rp3 = J(w, Ak, ck.mem('D', 'RR+'), ck.mem(D2, 'RR+'), linarith(w, Ak, [lift(w, F['d1'], Ak)], 'D < %s' % D2, closure=ck))
    ck.leaf(BVL('k'), 'RR', ap(w, Ak, 'bvlamre', [rp3, kN], '%s e. RR' % BVL('k')))
    afk = fvmd(w, Ak, 'd', 'NN', AFB('d'), 'k', kN, ck.mem(AFB('k'), 'CC'))
    akc = dst(w, Ak, [afk, ck.mem(AFB('k'), 'CC')], 'eqeltrd', '( %s ` k ) e. CC' % AF)
    aok = dst(w, A, [akc], 'ralrimiva', 'A. k e. %s ( %s ` k ) e. CC' % (FZM, AF))
    hlv = J(w, A, J(w, A, F['nN'], c.mem(TU, 'RR'), t2), J(w, A, m2, aok))
    # HFAM: YU : F --> RR
    Aq = '( %s /\\ q e. F )' % A
    qin = w.s([], 'simpr', '( %s -> q e. F )' % Aq)
    yq = dst(w, Aq, [lift(w, F['yf'], Aq), qin], 'ffvelcdmd', '( Y ` q ) e. CC')
    yqr = dst(w, Aq, [dst(w, Aq, [yq], 'imcld', '( Im ` ( Y ` q ) ) e. RR'), lift(w, ur, Aq)], 'readdcld', '( ( Im ` ( Y ` q ) ) + U ) e. RR')
    yuf = dst(w, A, [yqr], 'fmpttd', '%s : F --> RR' % YUU)
    hfam = J(w, A, F['fin'], F['kf'], yuf)
    # RNGF and SEPF in the letters c, g (the antecedent binds a, b)
    def yuval(Az, Z, zin):
        yz = dst(w, Az, [lift(w, F['yf'], Az), zin], 'ffvelcdmd', '%s e. CC' % YZ(Z))
        vr = dst(w, Az, [dst(w, Az, [yz], 'imcld', '( Im ` %s ) e. RR' % YZ(Z)), lift(w, ur, Az)], 'readdcld', '( ( Im ` %s ) + U ) e. RR' % YZ(Z))
        return fvmd(w, Az, 'q', 'F', '( ( Im ` ( Y ` q ) ) + U )', Z, zin, dst(w, Az, [vr], 'recnd', '( ( Im ` %s ) + U ) e. CC' % YZ(Z))), yz
    Ac = '( %s /\\ c e. F )' % A
    cin = w.s([], 'simpr', '( %s -> c e. F )' % Ac)
    fvc, yc = yuval(Ac, 'c', cin)
    Qc = ptsat(w, Ac, {'pts': lift(w, F['pts'], Ac)}, 'c', cin)
    cc = Closure(w, Ac, {'V': ('RR', lift(w, F['vr'], Ac)), 'U': ('RR', lift(w, ur, Ac)), YZ('c'): ('CC', yc)})
    IMc = '( Im ` %s )' % YZ('c')
    cc.leaf(IMc, 'RR', cc.mem(IMc, 'RR')); cc.leaf('( abs ` %s )' % IMc, 'RR', cc.mem('( abs ` %s )' % IMc, 'RR')); cc.leaf(AU, 'RR', cc.mem(AU, 'RR'))
    tri = dst(w, Ac, [cc.mem(IMc, 'CC'), cc.mem('U', 'CC')], 'abstrid', '( abs ` ( %s + U ) ) <_ ( ( abs ` %s ) + %s )' % (IMc, IMc, AU))
    cc.leaf('( abs ` ( %s + U ) )' % IMc, 'RR', cc.mem('( abs ` ( %s + U ) )' % IMc, 'RR'))
    rng1 = linarith(w, Ac, [tri, Qc['im']], '( abs ` ( %s + U ) ) <_ %s' % (IMc, TU), closure=cc)
    rng2 = dst(w, Ac, [dst(w, Ac, [fvc], 'fveq2d', '( abs ` ( %s ` c ) ) = ( abs ` ( %s + U ) )' % (YUU, IMc)), rng1], 'eqbrtrd', '( abs ` ( %s ` c ) ) <_ %s' % (YUU, TU))
    rngf = dst(w, A, [rng2], 'ralrimiva', 'A. c e. F ( abs ` ( %s ` c ) ) <_ %s' % (YUU, TU))
    Acg = '( %s /\\ ( c e. F /\\ g e. F ) )' % A
    cin2 = w.s([], 'simprl', '( %s -> c e. F )' % Acg); gin2 = w.s([], 'simprr', '( %s -> g e. F )' % Acg)
    fvc2, yc2 = yuval(Acg, 'c', cin2); fvg2, yg2 = yuval(Acg, 'g', gin2)
    SB = SEPY[len('A. a e. F A. b e. F '):]
    cg1, S1 = w.wcongr(SB, {'a': 'c'}, 'a = c', {'a': w.s([], 'id', '( a = c -> a = c )')})
    cg1b = w.s([cg1], 'ralbidv', '( a = c -> ( A. b e. F %s <-> A. b e. F %s ) )' % (SB, S1))
    sep1 = w.s([cg1b, lift(w, F['sep'], Acg), cin2], 'rspcdva', '( %s -> A. b e. F %s )' % (Acg, S1))
    cg2, S2 = w.wcongr(S1, {'b': 'g'}, 'b = g', {'b': w.s([], 'id', '( b = g -> b = g )')})
    sep2 = w.s([cg2, sep1, gin2], 'rspcdva', '( %s -> %s )' % (Acg, S2))
    IMc2 = '( Im ` %s )' % YZ('c'); IMg2 = '( Im ` %s )' % YZ('g')
    ccg = Closure(w, Acg, {'U': ('RR', lift(w, ur, Acg)), YZ('c'): ('CC', yc2), YZ('g'): ('CC', yg2)})
    dif = dst(w, Acg, [ccg.mem(IMc2, 'CC'), ccg.mem(IMg2, 'CC'), ccg.mem('U', 'CC')], 'pnpcan2d', '( ( %s + U ) - ( %s + U ) ) = ( %s - %s )' % (IMc2, IMg2, IMc2, IMg2))
    dv = eqt(w, Acg, dst(w, Acg, [fvc2, fvg2], 'oveq12d', '( ( %s ` c ) - ( %s ` g ) ) = ( ( %s + U ) - ( %s + U ) )' % (YUU, YUU, IMc2, IMg2)), dif)
    ad = dst(w, Acg, [dv], 'fveq2d', '( abs ` ( ( %s ` c ) - ( %s ` g ) ) ) = ( abs ` ( %s - %s ) )' % (YUU, YUU, IMc2, IMg2))
    bi = dst(w, Acg, [ad], 'breq2d', '( 1 <_ ( abs ` ( ( %s ` c ) - ( %s ` g ) ) ) <-> 1 <_ ( abs ` ( %s - %s ) ) )' % (YUU, YUU, IMc2, IMg2))
    HYP = '( c =/= g /\\ ( K ` c ) = ( K ` g ) )'
    assert S2 == '( %s -> 1 <_ ( abs ` ( %s - %s ) ) )' % (HYP, IMc2, IMg2), S2
    S3 = '( %s -> 1 <_ ( abs ` ( ( %s ` c ) - ( %s ` g ) ) ) )' % (HYP, YUU, YUU)
    sep3 = dst(w, Acg, [sep2, dst(w, Acg, [bi], 'imbi2d', '( %s <-> %s )' % (S3, S2))], 'mpbird', S3)
    sepf = dst(w, A, [sep3], 'ralrimivva', 'A. c e. F A. g e. F %s' % S3)
    # mvdfam
    SUBM = {'S': 'F', 'A': AF, 'M': M2D, 'T': TU, 'Y': YUU, 'a': 'c', 'b': 'g'}
    mv = ap(w, A, 'mvdfam', [J(w, A, hlv, hfam, J(w, A, rngf, sepf))], subst(concl('mvdfam'), SUBM))
    # the summand: DS ( K r , YU r ) = Mr
    Ar = '( %s /\\ r e. F )' % A
    rin = w.s([], 'simpr', '( %s -> r e. F )' % Ar)
    fvr, yr = yuval(Ar, 'r', rin)
    kr = dst(w, Ar, [lift(w, F['kf'], Ar), rin], 'ffvelcdmd', '%s e. %s' % (KZ('r'), DB()))
    DSR = lambda G: subst(DSX('X', G), {'X': KZ('r')})
    IMr = '( Im ` %s )' % YZ('r')
    Arn = '( %s /\\ n e. %s )' % (Ar, FZM)
    fvrn = lift(w, fvr, Arn)
    d1 = dst(w, Arn, [dst(w, Arn, [fvrn], 'oveq2d', '( -u ( log ` n ) x. ( %s ` r ) ) = ( -u ( log ` n ) x. ( %s + U ) )' % (YUU, IMr))], 'oveq2d',
             '( _i x. ( -u ( log ` n ) x. ( %s ` r ) ) ) = ( _i x. ( -u ( log ` n ) x. ( %s + U ) ) )' % (YUU, IMr))
    d2 = dst(w, Arn, [dst(w, Arn, [d1], 'fveq2d', '%s = %s' % (NEX('n', '( %s ` r )' % YUU), NEX('n', '( %s + U )' % IMr)))], 'oveq2d',
             '( ( ( %s ` n ) x. %s ) x. %s ) = ( ( ( %s ` n ) x. %s ) x. %s )' % (AF, CHV(KZ('r'), 'n'), NEX('n', '( %s ` r )' % YUU), AF, CHV(KZ('r'), 'n'), NEX('n', '( %s + U )' % IMr)))
    d3 = dst(w, Ar, [d2], 'sumeq2dv', '%s = %s' % (DSR('( %s ` r )' % YUU), DSR('( %s + U )' % IMr)))
    mrd = ap(w, Ar, 'ld2mrds', [J(w, Ar, J(w, Ar, lift(w, F['dr'], Ar), lift(w, F['d1'], Ar)), J(w, Ar, lift(w, F['nN'], Ar), kr)), J(w, Ar, yr, lift(w, ur, Ar))],
             subst(concl('ld2mrds'), {'X': KZ('r'), 'S': YZ('r')}))
    MRR = subst(MRU('U'), FAM('r'))
    assert body(w, mrd, Ar) == '%s = %s' % (MRR, DSR('( %s + U )' % IMr)), body(w, mrd, Ar)[:300]
    d4 = eqt(w, Ar, d3, eqc(w, Ar, mrd))
    d5 = dst(w, Ar, [dst(w, Ar, [d4], 'fveq2d', '( abs ` %s ) = %s' % (DSR('( %s ` r )' % YUU), MAK('r', 'U')))], 'oveq1d', '( ( abs ` %s ) ^ 2 ) = ( %s ^ 2 )' % (DSR('( %s ` r )' % YUU), MAK('r', 'U')))
    se = dst(w, A, [d5], 'sumeq2dv', 'sum_ r e. F ( ( abs ` %s ) ^ 2 ) = %s' % (DSR('( %s ` r )' % YUU), SQM('U')))
    mv2 = dst(w, A, [eqc(w, A, se), mv], 'eqbrtrd', '%s <_ ( ( ; ; 2 0 0 x. ( %s + ( N x. ( %s + 1 ) ) ) ) x. %s )' % (SQM('U'), M2D, TU, SLA))
    # the count and the mass
    mm = ap(w, A, 'ld2mmass', [F['hz']], concl('ld2mmass'))
    An = '( %s /\\ n e. %s )' % (A, FZM)
    nN = ap(w, An, 'elfznn', [w.s([], 'simpr', '( %s -> n e. %s )' % (An, FZM))], 'n e. NN')
    cn = Closure(w, An, {'D': [('RR+', lift(w, F['rp'], An)), ('gt1', lift(w, F['d1'], An))], 'n': ('NN', nN)})
    rp3 = J(w, An, cn.mem('D', 'RR+'), cn.mem(D2, 'RR+'), linarith(w, An, [lift(w, F['d1'], An)], 'D < %s' % D2, closure=cn))
    cn.leaf(BVL('n'), 'RR', ap(w, An, 'bvlamre', [rp3, nN], '%s e. RR' % BVL('n')))
    afn = fvmd(w, An, 'd', 'NN', AFB('d'), 'n', nN, cn.mem(AFB('n'), 'CC'))
    cn.leaf('( %s ` n )' % AF, 'CC', dst(w, An, [afn, cn.mem(AFB('n'), 'CC')], 'eqeltrd', '( %s ` n ) e. CC' % AF))
    TM = '( ( 1 + ( ( log ` n ) ^ 2 ) ) x. ( ( abs ` ( %s ` n ) ) ^ 2 ) )' % AF
    fi = dst(w, A, [], 'fzfid', '%s e. Fin' % FZM)
    sl0 = dst(w, A, [fi, cn.mem(TM, 'RR'), cn.ge0(TM)], 'fsumge0', '0 <_ %s' % SLA)
    slr = dst(w, A, [fi, cn.mem(TM, 'RR')], 'fsumrecl', '%s e. RR' % SLA)
    c.leaf(SLA, 'RR', slr); c.leaf(SLA, 'ge0', sl0)
    m2r = dst(w, A, [m2], 'nn0red', '%s e. RR' % M2D); m20 = dst(w, A, [m2], 'nn0ge0d', '0 <_ %s' % M2D)
    c.leaf(M2D, 'RR', m2r); c.leaf(M2D, 'ge0', m20)
    fl = ap(w, A, 'flle', [c.mem(D2, 'RR')], '%s <_ %s' % (M2D, D2))
    nd = dst(w, A, [w.s([], '1red', '( %s -> 1 e. RR )' % A), c.mem('( V + 2 )', 'RR'), c.mem('N', 'RR'), c.ge0('N'), linarith(w, A, [F['v2']], '1 <_ ( V + 2 )', closure=c)], 'lemul2ad', '( N x. 1 ) <_ ( N x. ( V + 2 ) )')
    nd2 = dst(w, A, [dst(w, A, [eqc(w, A, dst(w, A, [c.mem('N', 'CC')], 'mulridd', '( N x. 1 ) = N')), nd], 'eqbrtrd', 'N <_ ( N x. ( V + 2 ) )'), eqc(w, A, F['deq'])], 'breqtrd', 'N <_ D')
    nu = dst(w, A, [c.mem('N', 'RR'), c.mem('D', 'RR'), c.mem(AU, 'RR'), c.ge0(AU), nd2], 'lemul1ad', '( N x. %s ) <_ ( D x. %s )' % (AU, AU))
    CNT = '( ; ; 2 0 0 x. ( %s + ( N x. ( %s + 1 ) ) ) )' % (M2D, TU)
    CNT2 = '( ( ; ; 2 0 0 x. D ) x. ( 3 + %s ) )' % AU
    cnt = nlinarith(w, A, [fl, F['deq'], nu, c.ge0('N')], '%s <_ %s' % (CNT, CNT2), closure=c)
    c.have(CNT, 'RR', c.mem(CNT, 'RR'))
    cnt0 = nlinarith(w, A, [m20, c.ge0('N'), c.ge0(AU), F['v2']], '0 <_ %s' % CNT, closure=c)
    pr = dst(w, A, [c.mem(CNT, 'RR'), c.mem(CNT2, 'RR'), c.mem(SLA, 'RR'), c.mem('( 2 x. ( %s ^ 3 ) )' % L, 'RR'), cnt0, sl0, cnt, mm], 'lemul12ad', '( %s x. %s ) <_ ( %s x. ( 2 x. ( %s ^ 3 ) ) )' % (CNT, SLA, CNT2, L))
    rg = ringeq(w, A, '( %s x. ( 2 x. ( %s ^ 3 ) ) )' % (CNT2, L), '( ( ; ; 4 0 0 x. %s ) x. ( 3 + %s ) )' % (LOG3, AU), c)
    mar = macl_(w, Ar, c, F, 'r', 'U', lift(w, ur, Ar), kr, yr)
    sqr = dst(w, Ar, [mar], 'resqcld', '( %s ^ 2 ) e. RR' % MAK('r', 'U'))
    sqm = dst(w, A, [F['fin'], sqr], 'fsumrecl', '%s e. RR' % SQM('U'))
    dst(w, A, [sqm, c.mem('( %s x. %s )' % (CNT, SLA), 'RR'), c.mem('( ( ; ; 4 0 0 x. %s ) x. ( 3 + %s ) )' % (LOG3, AU), 'RR'), mv2,
               dst(w, A, [pr, rg], 'breqtrd', '( %s x. %s ) <_ ( ( ; ; 4 0 0 x. %s ) x. ( 3 + %s ) )' % (CNT, SLA, LOG3, AU))], 'letrd',
        '%s <_ ( ( ; ; 4 0 0 x. %s ) x. ( 3 + %s ) )' % (SQM('U'), LOG3, AU))
    return fin(w)


def macl_(w, Ar, c, F, r, U, ur, kr, yr):
    """( Ar -> MAK(r,U) e. RR ) from the character ( K r ) e. DB and ( Y r ) e. CC"""
    cr = Closure(w, Ar, {'D': [('RR', lift(w, F['dr'], Ar)), ('gt1', lift(w, F['d1'], Ar))], YZ(r): ('CC', yr), U: ('RR', ur), '_i': ('CC', a1(w, Ar, 'ax-icn', '_i e. CC'))})
    cr.leaf('( Re ` %s )' % YZ(r), 'RR', dst(w, Ar, [yr], 'recld', '( Re ` %s ) e. RR' % YZ(r)))
    lif = ap(w, Ar, 'zl1lif', [J(w, Ar, lift(w, F['nN'], Ar), kr)], subst(concl('zl1lif'), {'X': KZ(r)}))
    cf = parts(w, Ar, top=body(w, lif, Ar), step=lif)['%s : NN --> CC' % CX(KZ(r))]
    h0 = hab0(w, Ar, cr, lift(w, F['dr'], Ar), lift(w, F['d1'], Ar))
    Z = subst('( S + %s )' % HLU(U), {'S': YZ(r)})
    mc = ap(w, Ar, 'z5mrcl', [J(w, Ar, h0, a1(w, Ar, '1nn', '1 e. NN')), J(w, Ar, cf, cr.mem(Z, 'CC'))], '%s e. CC' % subst(MRU(U), FAM(r)))
    mar = dst(w, Ar, [mc], 'abscld', '%s e. RR' % MAK(r, U))
    if c is not None and c.ante == Ar:
        c.leaf(MAK(r, U), 'RR', mar)
        c.leaf(MAK(r, U), 'ge0', dst(w, Ar, [mc], 'absge0d', '0 <_ %s' % MAK(r, U)))
    return mar



def ld2mvw():
    w = W('ld2mvw', 'The weighted mean value at a fixed ` u ` : ` e ^ -( abs u / 2 ) sum_ r abs M_r ^ 2 <_ 1600 D log ^ 3 D e ^ -( abs u / 4 ) ` (~ ld2mvu , ~ ld2wlin ).')
    A = ante('ld2mvw'); P, c, F = famsetup(w, A)
    ur = P['U e. RR']; c.leaf('U', 'RR', ur)
    AU = '( abs ` U )'; c.leaf(AU, 'RR', c.mem(AU, 'RR')); c.leaf(AU, 'ge0', c.ge0(AU))
    mv = ap(w, A, 'ld2mvu', [w.s([], 'id', '( %s -> %s )' % (A, A))], concl('ld2mvu'))
    Ar = '( %s /\\ r e. F )' % A
    rin = w.s([], 'simpr', '( %s -> r e. F )' % Ar)
    kr = dst(w, Ar, [lift(w, F['kf'], Ar), rin], 'ffvelcdmd', '%s e. %s' % (KZ('r'), DB()))
    yr = dst(w, Ar, [lift(w, F['yf'], Ar), rin], 'ffvelcdmd', '%s e. CC' % YZ('r'))
    mar = macl_(w, Ar, c, F, 'r', 'U', lift(w, ur, Ar), kr, yr)
    sqr = dst(w, Ar, [mar], 'resqcld', '( %s ^ 2 ) e. RR' % MAK('r', 'U'))
    sqm = dst(w, A, [F['fin'], sqr], 'fsumrecl', '%s e. RR' % SQM('U'))
    c.leaf(SQM('U'), 'RR', sqm)
    for e_ in (WT('U'), WT4('U')):
        c.leaf(e_, 'RR+', dst(w, A, [c.mem(e_[len('( exp ` '):-2], 'RR')], 'rpefcld', '%s e. RR+' % e_))
    B1 = '( ( ; ; 4 0 0 x. %s ) x. ( 3 + %s ) )' % (LOG3, AU)
    m1 = dst(w, A, [sqm, c.mem(B1, 'RR'), c.mem(WT('U'), 'RR'), c.ge0(WT('U')), mv], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (WT('U'), SQM('U'), WT('U'), B1))
    rg1 = ringeq(w, A, '( %s x. %s )' % (WT('U'), B1), '( ( ; ; 4 0 0 x. %s ) x. ( ( 3 + %s ) x. %s ) )' % (LOG3, AU, WT('U')), c)
    wl = ap(w, A, 'ld2wlin', [J(w, A, c.mem(AU, 'RR'), c.ge0(AU))], '( ( 3 + %s ) x. %s ) <_ ( 4 x. %s )' % (AU, WT('U'), WT4('U')))
    Q = '( ; ; 4 0 0 x. %s )' % LOG3
    m2 = dst(w, A, [c.mem('( ( 3 + %s ) x. %s )' % (AU, WT('U')), 'RR'), c.mem('( 4 x. %s )' % WT4('U'), 'RR'), c.mem(Q, 'RR'), c.ge0(Q), wl], 'lemul2ad', '( %s x. ( ( 3 + %s ) x. %s ) ) <_ ( %s x. ( 4 x. %s ) )' % (Q, AU, WT('U'), Q, WT4('U')))
    rg2 = ringeq(w, A, '( %s x. ( 4 x. %s ) )' % (Q, WT4('U')), '( ( ; ; ; 1 6 0 0 x. %s ) x. %s )' % (LOG3, WT4('U')), c)
    t1 = dst(w, A, [m1, rg1], 'breqtrd', '( %s x. %s ) <_ ( %s x. ( ( 3 + %s ) x. %s ) )' % (WT('U'), SQM('U'), Q, AU, WT('U')))
    t2 = dst(w, A, [m2, rg2], 'breqtrd', '( %s x. ( ( 3 + %s ) x. %s ) ) <_ ( ( ; ; ; 1 6 0 0 x. %s ) x. %s )' % (Q, AU, WT('U'), LOG3, WT4('U')))
    dst(w, A, [c.mem('( %s x. %s )' % (WT('U'), SQM('U')), 'RR'), c.mem('( %s x. ( ( 3 + %s ) x. %s ) )' % (Q, AU, WT('U')), 'RR'), c.mem('( ( ; ; ; 1 6 0 0 x. %s ) x. %s )' % (LOG3, WT4('U')), 'RR'), t1, t2], 'letrd',
        '( %s x. %s ) <_ ( ( ; ; ; 1 6 0 0 x. %s ) x. %s )' % (WT('U'), SQM('U'), LOG3, WT4('U')))
    return fin(w)


def cnmember(w, Ar, c, F, M, r):
    """( Ar -> ( u e. RR |-> ( WT x. MAK(r,u) ^ 2 ) ) e. cn ) for the member r"""
    wt = ap(w, Ar, 'ld2wtcn', [lift(w, c.mem('( 1 / 2 )', 'RR'), Ar)], '( u e. RR |-> %s ) e. ( RR -cn-> CC )' % WT('u'))
    ma = ap(w, Ar, 'ld2macn', [J(w, Ar, J(w, Ar, lift(w, F['dr'], Ar), lift(w, F['d1'], Ar)), J(w, Ar, M['cf'], M['yz']))], '( u e. RR |-> %s ) e. ( RR -cn-> CC )' % MAK(r, 'u'))
    Au = '( %s /\\ u e. RR )' % Ar
    ur = w.s([], 'simpr', '( %s -> u e. RR )' % Au)
    cu = Closure(w, Au, {'u': ('RR', ur)})
    mau = macl_(w, Au, cu, F, r, 'u', ur, lift(w, M['kz'], Au), lift(w, M['yz'], Au))
    mac = dst(w, Au, [mau], 'recnd', '%s e. CC' % MAK(r, 'u'))
    sq = dst(w, Au, [mac], 'sqvald', '( %s ^ 2 ) = ( %s x. %s )' % (MAK(r, 'u'), MAK(r, 'u'), MAK(r, 'u')))
    m2 = w.s([ma, ma], 'mulcncf', '( %s -> ( u e. RR |-> ( %s x. %s ) ) e. ( RR -cn-> CC ) )' % (Ar, MAK(r, 'u'), MAK(r, 'u')))
    me = dst(w, Ar, [sq], 'mpteq2dva', '( u e. RR |-> ( %s ^ 2 ) ) = ( u e. RR |-> ( %s x. %s ) )' % (MAK(r, 'u'), MAK(r, 'u'), MAK(r, 'u')))
    m2b = dst(w, Ar, [me, m2], 'eqeltrd', '( u e. RR |-> ( %s ^ 2 ) ) e. ( RR -cn-> CC )' % MAK(r, 'u'))
    return w.s([wt, m2b], 'mulcncf', '( %s -> ( u e. RR |-> ( %s x. ( %s ^ 2 ) ) ) e. ( RR -cn-> CC ) )' % (Ar, WT('u'), MAK(r, 'u'))), mau


def ld2int():
    w = W('ld2int', 'Lean ` hsumint ` of ` sum_sq_EctrHalf_le ` on a truncation: ` sum_ r S. ( -H , H ) e ^ -( abs u / 2 ) abs M_r ^ 2 du <_ 12800 D log ^ 3 D ` (~ itgfsum , ~ itgle with ~ ld2mvw , ~ ld2wint at ` 1 / 4 ` ).')
    A = ante('ld2int'); P, c, F = famsetup(w, A)
    hrp = P['H e. RR+']; c.leaf('H', 'RR+', hrp)
    I = IOH('H')
    nh = c.mem('-u H', 'RR'); hr = c.mem('H', 'RR'); h1 = J(w, A, nh, hr)
    Ar = '( %s /\\ r e. F )' % A
    M = member(w, Ar, P, c, F, 'r')
    TERM = lambda v: '( %s x. ( %s ^ 2 ) )' % (WT(v), MAK('r', v))
    cnr, _ = cnmember(w, Ar, c, F, M, 'r')
    ibr = w.s([lift(w, h1, Ar), cnr], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (Ar, I, TERM('u')))
    Aur = '( %s /\\ ( u e. %s /\\ r e. F ) )' % (A, I)
    uin = w.s([], 'simprl', '( %s -> u e. %s )' % (Aur, I)); rin2 = w.s([], 'simprr', '( %s -> r e. F )' % (Aur, 'F') if False else '( %s -> r e. F )' % Aur)
    ur2 = ap(w, Aur, 'elioore', [uin], 'u e. RR')
    kr2 = dst(w, Aur, [lift(w, F['kf'], Aur), rin2], 'ffvelcdmd', '%s e. %s' % (KZ('r'), DB()))
    yr2 = dst(w, Aur, [lift(w, F['yf'], Aur), rin2], 'ffvelcdmd', '%s e. CC' % YZ('r'))
    cur = child(w, Aur, c, {'u': ('RR', ur2)})
    mar2 = macl_(w, Aur, cur, F, 'r', 'u', ur2, kr2, yr2)
    cur.leaf(WT('u'), 'RR+', dst(w, Aur, [cur.mem('-u ( ( 1 / 2 ) x. ( abs ` u ) )', 'RR')], 'rpefcld', '%s e. RR+' % WT('u')))
    tc = cur.mem(TERM('u'), 'CC')
    fs = w.s([a1(w, A, 'ioombl', '%s e. dom vol' % I), F['fin'], tc, ibr], 'itgfsum', '( %s -> ( ( u e. %s |-> sum_ r e. F %s ) e. L^1 /\\ %s = sum_ r e. F %s ) )' % (A, I, TERM('u'), ITG(I, 'sum_ r e. F %s' % TERM('u'), 'u'), ITG(I, TERM('u'), 'u')))
    ibs = dst(w, A, [fs], 'simpld', '( u e. %s |-> sum_ r e. F %s ) e. L^1' % (I, TERM('u')))
    sw = dst(w, A, [fs], 'simprd', '%s = sum_ r e. F %s' % (ITG(I, 'sum_ r e. F %s' % TERM('u'), 'u'), ITG(I, TERM('u'), 'u')))
    # pointwise: sum_r ( WT x. MAK^2 ) = WT x. sum_r MAK^2 <_ 1600 LOG3 WT4
    Au = '( %s /\\ u e. %s )' % (A, I)
    ur = ap(w, Au, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, I))], 'u e. RR')
    cu = child(w, Au, c, {'u': ('RR', ur)})
    cu.leaf(WT('u'), 'RR+', dst(w, Au, [cu.mem('-u ( ( 1 / 2 ) x. ( abs ` u ) )', 'RR')], 'rpefcld', '%s e. RR+' % WT('u')))
    Aur2 = '( %s /\\ r e. F )' % Au
    rin3 = w.s([], 'simpr', '( %s -> r e. F )' % Aur2)
    kr3 = dst(w, Aur2, [lift(w, F['kf'], Aur2), rin3], 'ffvelcdmd', '%s e. %s' % (KZ('r'), DB()))
    yr3 = dst(w, Aur2, [lift(w, F['yf'], Aur2), rin3], 'ffvelcdmd', '%s e. CC' % YZ('r'))
    cur3 = child(w, Aur2, cu, {'u': ('RR', lift(w, ur, Aur2))})
    mar3 = macl_(w, Aur2, cur3, F, 'r', 'u', lift(w, ur, Aur2), kr3, yr3)
    sq3 = dst(w, Aur2, [mar3], 'resqcld', '( %s ^ 2 ) e. RR' % MAK('r', 'u'))
    fm = dst(w, Au, [lift(w, F['fin'], Au), cu.mem(WT('u'), 'CC'), dst(w, Aur2, [sq3], 'recnd', '( %s ^ 2 ) e. CC' % MAK('r', 'u'))], 'fsummulc2', '( %s x. %s ) = sum_ r e. F %s' % (WT('u'), SQM('u'), TERM('u')))
    mw = ap(w, Au, 'ld2mvw', [J(w, Au, lift(w, F['hfam'], Au), ur)], subst(concl('ld2mvw'), {'U': 'u'}))
    B2 = '( ( ; ; ; 1 6 0 0 x. %s ) x. %s )' % (LOG3, WT4('u'))
    pw = dst(w, Au, [eqc(w, Au, fm), mw], 'eqbrtrd', 'sum_ r e. F %s <_ %s' % (TERM('u'), B2))
    wt4 = ap(w, A, 'ld2wtcn', [c.mem('( 1 / 4 )', 'RR')], '( u e. RR |-> %s ) e. ( RR -cn-> CC )' % WT4('u'))
    ib4 = w.s([h1, wt4], 'ld2rribl', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, WT4('u')))
    cu.leaf(WT4('u'), 'RR+', dst(w, Au, [cu.mem('-u ( ( 1 / 4 ) x. ( abs ` u ) )', 'RR')], 'rpefcld', '%s e. RR+' % WT4('u')))
    C16 = '( ; ; ; 1 6 0 0 x. %s )' % LOG3
    c16c = c.mem(C16, 'CC')
    ibb = w.s([c16c, cu.mem(WT4('u'), 'CC'), ib4], 'iblmulc2', '( %s -> ( u e. %s |-> %s ) e. L^1 )' % (A, I, B2))
    smr = dst(w, Au, [lift(w, F['fin'], Au), cur3.mem(TERM('u'), 'RR')], 'fsumrecl', 'sum_ r e. F %s e. RR' % TERM('u'))
    il = w.s([ibs, ibb, smr, cu.mem(B2, 'RR'), pw], 'itgle', '( %s -> %s <_ %s )' % (A, ITG(I, 'sum_ r e. F %s' % TERM('u'), 'u'), ITG(I, B2, 'u')))
    mc = w.s([c16c, cu.mem(WT4('u'), 'CC'), ib4], 'itgmulc2', '( %s -> ( %s x. %s ) = %s )' % (A, C16, ITG(I, WT4('u'), 'u'), ITG(I, B2, 'u')))
    wi = ap(w, A, 'ld2wint', [c.mem('( 1 / 4 )', 'RR+'), hrp], '%s <_ ( 2 / ( 1 / 4 ) )' % ITG(I, WT4('u'), 'u'))
    q1 = ap(w, A, 'divrec', [c.mem('2', 'CC'), c.mem('( 1 / 4 )', 'CC'), c.ne0('( 1 / 4 )')], '( 2 / ( 1 / 4 ) ) = ( 2 x. ( 1 / ( 1 / 4 ) ) )')
    q2 = dst(w, A, [w.s([], '1cnd', '( %s -> 1 e. CC )' % A), c.mem('4', 'CC'), a1(w, A, 'ax-1ne0', '1 =/= 0'), c.ne0('4')], 'recdivd', '( 1 / ( 1 / 4 ) ) = ( 4 / 1 )')
    q3 = eqt(w, A, q2, dst(w, A, [c.mem('4', 'CC')], 'div1d', '( 4 / 1 ) = 4'))
    q4 = eqt(w, A, q1, eqt(w, A, dst(w, A, [q3], 'oveq2d', '( 2 x. ( 1 / ( 1 / 4 ) ) ) = ( 2 x. 4 )'), num.mul_lits(w, '2', '4') if False else a1(w, A, '2t4e8', '( 2 x. 4 ) = 8')))
    wi2 = dst(w, A, [wi, q4], 'breqtrd', '%s <_ 8' % ITG(I, WT4('u'), 'u'))
    i4r = dst(w, A, [cu.mem(WT4('u'), 'RR'), ib4], 'itgrecl', '%s e. RR' % ITG(I, WT4('u'), 'u'))
    c.leaf(ITG(I, WT4('u'), 'u'), 'RR', i4r)
    m3 = dst(w, A, [i4r, c.mem('8', 'RR'), c.mem(C16, 'RR'), c.ge0(C16), wi2], 'lemul2ad', '( %s x. %s ) <_ ( %s x. 8 )' % (C16, ITG(I, WT4('u'), 'u'), C16))
    rg = ringeq(w, A, '( %s x. 8 )' % C16, '( ; ; ; ; 1 2 8 0 0 x. %s )' % LOG3, c)
    t1 = dst(w, A, [il, eqc(w, A, mc)], 'breqtrd', '%s <_ ( %s x. %s )' % (ITG(I, 'sum_ r e. F %s' % TERM('u'), 'u'), C16, ITG(I, WT4('u'), 'u')))
    t2 = dst(w, A, [m3, rg], 'breqtrd', '( %s x. %s ) <_ ( ; ; ; ; 1 2 8 0 0 x. %s )' % (C16, ITG(I, WT4('u'), 'u'), LOG3))
    isr = dst(w, A, [smr, ibs], 'itgrecl', '%s e. RR' % ITG(I, 'sum_ r e. F %s' % TERM('u'), 'u'))
    t3 = dst(w, A, [isr, c.mem('( %s x. %s )' % (C16, ITG(I, WT4('u'), 'u')), 'RR'), c.mem('( ; ; ; ; 1 2 8 0 0 x. %s )' % LOG3, 'RR'), t1, t2], 'letrd', '%s <_ ( ; ; ; ; 1 2 8 0 0 x. %s )' % (ITG(I, 'sum_ r e. F %s' % TERM('u'), 'u'), LOG3))
    dst(w, A, [eqc(w, A, sw), t3], 'eqbrtrd', 'sum_ r e. F %s <_ ( ; ; ; ; 1 2 8 0 0 x. %s )' % (ITG(I, TERM('u'), 'u'), LOG3))
    return fin(w)


def licl_member(w, Ar, c, F, M, r, H, hrp):
    """( Ar -> LIK(r,H) e. CC ) by ld2licl at the member"""
    I = IOH(H)
    lc = ap(w, Ar, 'ld2licl', [J(w, Ar, M['a7c'], hrp)], subst(concl('ld2licl'), dict(FAM(r), H=H)))
    GV = subst(GRHV('u'), FAM(r))
    ibl = dst(w, Ar, [lc], 'simpld', '( u e. %s |-> %s ) e. L^1' % (I, GV))
    val = dst(w, Ar, [lc], 'simprd', '%s = ( _i x. %s )' % (LIK(r, H), ITG(I, GV, 'u')))
    Au = '( %s /\\ u e. %s )' % (Ar, I)
    gv = a1(w, Au, 'fvex', '%s e. _V' % GV)
    itc = w.s([gv, ibl], 'itgcl', '( %s -> %s e. CC )' % (Ar, ITG(I, GV, 'u')))
    return dst(w, Ar, [val, dst(w, Ar, [a1(w, Ar, 'ax-icn', '_i e. CC'), itc], 'mulcld', '( _i x. %s ) e. CC' % ITG(I, GV, 'u'))], 'eqeltrd', '%s e. CC' % LIK(r, H))


def ld2trs():
    w = W('ld2trs', 'The family bound on a truncation: ` sum_ r ( abs LIK_r ( H ) ) ^ 2 <_ K ^ 2 51200 D log ^ 3 D ` (~ ld2sq1 at each member through ~ ld2hp6 , ~ fsumle , ~ ld2int ).')
    A = ante('ld2trs'); P, c, F = famsetup(w, A)
    hrp = P['H e. RR+']; c.leaf('H', 'RR+', hrp)
    kcr = kcfacts(w, A, c, F, F['tr'])
    I = IOH('H')
    Ar = '( %s /\\ r e. F )' % A
    M = member(w, Ar, P, c, F, 'r')
    sq = ap(w, Ar, 'ld2sq1', [J(w, Ar, M['hp'], lift(w, hrp, Ar))], subst(concl('ld2sq1'), FAM('r')))
    I2r = ITG(I, '( %s x. ( %s ^ 2 ) )' % (WT('u'), MAK('r', 'u')), 'u')
    assert body(w, sq, Ar) == '( ( abs ` %s ) ^ 2 ) <_ ( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (LIK('r', 'H'), KC, I2r), body(w, sq, Ar)[-300:]
    lic = licl_member(w, Ar, c, F, M, 'r', 'H', lift(w, hrp, Ar))
    AL = '( abs ` %s )' % LIK('r', 'H')
    alr = dst(w, Ar, [dst(w, Ar, [lic], 'abscld', '%s e. RR' % AL)], 'resqcld', '( %s ^ 2 ) e. RR' % AL)
    cnr, _ = cnmember(w, Ar, c, F, M, 'r')
    ibr = w.s([J(w, Ar, lift(w, c.mem('-u H', 'RR'), Ar), lift(w, c.mem('H', 'RR'), Ar)), cnr], 'ld2rribl', '( %s -> ( u e. %s |-> ( %s x. ( %s ^ 2 ) ) ) e. L^1 )' % (Ar, I, WT('u'), MAK('r', 'u')))
    Au = '( %s /\\ u e. %s )' % (Ar, I)
    ur = ap(w, Au, 'elioore', [w.s([], 'simpr', '( %s -> u e. %s )' % (Au, I))], 'u e. RR')
    cu = child(w, Au, c, {'u': ('RR', ur)})
    mau = macl_(w, Au, cu, F, 'r', 'u', ur, lift(w, M['kz'], Au), lift(w, M['yz'], Au))
    cu.leaf(WT('u'), 'RR+', dst(w, Au, [cu.mem('-u ( ( 1 / 2 ) x. ( abs ` u ) )', 'RR')], 'rpefcld', '%s e. RR+' % WT('u')))
    i2r = dst(w, Ar, [cu.mem('( %s x. ( %s ^ 2 ) )' % (WT('u'), MAK('r', 'u')), 'RR'), ibr], 'itgrecl', '%s e. RR' % I2r)
    kc2 = c.mem('( %s ^ 2 )' % KC, 'RR'); kc20 = dst(w, A, [c.mem(KC, 'RR')], 'sqge0d', '0 <_ ( %s ^ 2 )' % KC)
    RB = '( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (KC, I2r)
    rbr = dst(w, Ar, [lift(w, kc2, Ar), dst(w, Ar, [i2r], 'x', 'x') if False else dst(w, Ar, [a1(w, Ar, '4re', '4 e. RR'), i2r], 'remulcld', '( 4 x. %s ) e. RR' % I2r)], 'remulcld', '%s e. RR' % RB)
    fl = dst(w, A, [F['fin'], alr, rbr, sq], 'fsumle', 'sum_ r e. F ( ( abs ` %s ) ^ 2 ) <_ sum_ r e. F %s' % (LIK('r', 'H'), RB))
    SI = 'sum_ r e. F %s' % I2r
    f1 = dst(w, A, [F['fin'], c.mem('( %s ^ 2 )' % KC, 'CC'), dst(w, Ar, [dst(w, Ar, [a1(w, Ar, '4re', '4 e. RR'), i2r], 'remulcld', '( 4 x. %s ) e. RR' % I2r)], 'recnd', '( 4 x. %s ) e. CC' % I2r)], 'fsummulc2',
             '( ( %s ^ 2 ) x. sum_ r e. F ( 4 x. %s ) ) = sum_ r e. F %s' % (KC, I2r, RB))
    f2 = dst(w, A, [F['fin'], c.mem('4', 'CC'), dst(w, Ar, [i2r], 'recnd', '%s e. CC' % I2r)], 'fsummulc2', '( 4 x. %s ) = sum_ r e. F ( 4 x. %s )' % (SI, I2r))
    it = ap(w, A, 'ld2int', [w.s([], 'id', '( %s -> %s )' % (A, A))], concl('ld2int'))
    sir = dst(w, A, [F['fin'], i2r], 'fsumrecl', '%s e. RR' % SI)
    c.leaf(SI, 'RR', sir)
    C12 = '( ; ; ; ; 1 2 8 0 0 x. %s )' % LOG3
    m1 = dst(w, A, [sir, c.mem(C12, 'RR'), c.mem('4', 'RR'), c.ge0('4'), it], 'lemul2ad', '( 4 x. %s ) <_ ( 4 x. %s )' % (SI, C12))
    m2 = dst(w, A, [c.mem('( 4 x. %s )' % SI, 'RR'), c.mem('( 4 x. %s )' % C12, 'RR'), kc2, kc20, m1], 'lemul2ad', '( ( %s ^ 2 ) x. ( 4 x. %s ) ) <_ ( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (KC, SI, KC, C12))
    rg = ringeq(w, A, '( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (KC, C12), BV, c)
    e1 = eqt(w, A, dst(w, A, [f2], 'oveq2d', '( ( %s ^ 2 ) x. ( 4 x. %s ) ) = ( ( %s ^ 2 ) x. sum_ r e. F ( 4 x. %s ) )' % (KC, SI, KC, I2r)), f1)
    t1 = dst(w, A, [fl, eqc(w, A, e1)], 'breqtrd', 'sum_ r e. F ( ( abs ` %s ) ^ 2 ) <_ ( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (LIK('r', 'H'), KC, SI))
    t2 = dst(w, A, [m2, rg], 'breqtrd', '( ( %s ^ 2 ) x. ( 4 x. %s ) ) <_ %s' % (KC, SI, BV))
    lsr = dst(w, A, [F['fin'], alr], 'fsumrecl', 'sum_ r e. F ( ( abs ` %s ) ^ 2 ) e. RR' % LIK('r', 'H'))
    dst(w, A, [lsr, c.mem('( ( %s ^ 2 ) x. ( 4 x. %s ) )' % (KC, SI), 'RR'), c.mem(BV, 'RR'), t1, t2], 'letrd', 'sum_ r e. F ( ( abs ` %s ) ^ 2 ) <_ %s' % (LIK('r', 'H'), BV))
    return fin(w)


def ld2lim():
    w = W('ld2lim', 'The family bound passes to the limit ` H -> +oo ` : ` sum_ r ( abs VL_r ) ^ 2 <_ BV ` (~ ld2vlcv at each member, ~ rlimabs , ~ rlimmul , ~ fsumrlim , ~ z6rlimle with ~ ld2trs ).')
    A = ante('ld2lim'); P, c, F = famsetup(w, A)
    kcr = kcfacts(w, A, c, F, F['tr'])
    Ar = '( %s /\\ r e. F )' % A
    M = member(w, Ar, P, c, F, 'r')
    cv = ap(w, Ar, 'ld2vlcv', [M['a7c']], subst(concl('ld2vlcv'), FAM('r')))
    VLFr = subst(VLFH, FAM('r')); VLr = VLK('r'); LIt = LIK('r', 'h')
    assert body(w, cv, Ar) == '%s ~~>r %s' % (VLFr, VLr)
    # rename the truncation letter: the limit VLr binds t, and rlimabs / rlimmul / fsumrlim need $d between the mapping letter and the limit
    cgm, LIt2 = w.congr(LIK('r', 't'), {'t': 'h'}, 't = h', {'t': w.s([], 'id', '( t = h -> t = h )')})
    assert LIt2 == LIt, LIt2[:100]
    VLFh = '( h e. RR+ |-> %s )' % LIt
    ren = w.s([cgm], 'cbvmptv', '%s = %s' % (VLFr, VLFh))
    cv = dst(w, Ar, [w.s([ren], 'a1i', '( %s -> %s = %s )' % (Ar, VLFr, VLFh)), cv], 'eqbrtrrd', '%s ~~>r %s' % (VLFh, VLr))
    At = '( %s /\\ h e. RR+ )' % Ar
    trp = w.s([], 'simpr', '( %s -> h e. RR+ )' % At)
    lv = a1(w, At, 'ovex', '%s e. _V' % LIt)
    ra = w.s([lv, cv], 'rlimabs', '( %s -> ( h e. RR+ |-> ( abs ` %s ) ) ~~>r ( abs ` %s ) )' % (Ar, LIt, VLr))
    av = a1(w, At, 'fvex', '( abs ` %s ) e. _V' % LIt)
    rm = w.s([av, av, ra, ra], 'rlimmul', '( %s -> ( h e. RR+ |-> ( ( abs ` %s ) x. ( abs ` %s ) ) ) ~~>r ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (Ar, LIt, LIt, VLr, VLr))
    lic = licl_member(w, At, c, F, {'a7c': lift(w, M['a7c'], At)}, 'r', 'h', trp)
    alc = dst(w, At, [dst(w, At, [lic], 'abscld', '( abs ` %s ) e. RR' % LIt)], 'recnd', '( abs ` %s ) e. CC' % LIt)
    sq = dst(w, At, [alc], 'sqvald', '( ( abs ` %s ) ^ 2 ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (LIt, LIt, LIt))
    me = dst(w, Ar, [sq], 'mpteq2dva', '( h e. RR+ |-> ( ( abs ` %s ) ^ 2 ) ) = ( h e. RR+ |-> ( ( abs ` %s ) x. ( abs ` %s ) ) )' % (LIt, LIt, LIt))
    vlc = w.s([cv, w.inst('rlimcl')], 'syl', '( %s -> %s e. CC )' % (Ar, VLr))
    avc = dst(w, Ar, [dst(w, Ar, [vlc], 'abscld', '( abs ` %s ) e. RR' % VLr)], 'recnd', '( abs ` %s ) e. CC' % VLr)
    sqv = dst(w, Ar, [avc], 'sqvald', '( ( abs ` %s ) ^ 2 ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (VLr, VLr, VLr))
    r1 = dst(w, Ar, [me, rm], 'eqbrtrd', '( h e. RR+ |-> ( ( abs ` %s ) ^ 2 ) ) ~~>r ( ( abs ` %s ) x. ( abs ` %s ) )' % (LIt, VLr, VLr))
    r2 = dst(w, Ar, [r1, eqc(w, Ar, sqv)], 'breqtrd', '( h e. RR+ |-> ( ( abs ` %s ) ^ 2 ) ) ~~>r ( ( abs ` %s ) ^ 2 )' % (LIt, VLr))
    Atr = '( %s /\\ ( h e. RR+ /\\ r e. F ) )' % A
    ev = a1(w, Atr, 'ovex', '( ( abs ` %s ) ^ 2 ) e. _V' % LIt)
    G = 'sum_ r e. F ( ( abs ` %s ) ^ 2 )' % LIt; Wv = 'sum_ r e. F ( ( abs ` %s ) ^ 2 )' % VLr
    fr = w.s([a1(w, A, 'rpssre', 'RR+ C_ RR'), F['fin'], ev, r2], 'fsumrlim', '( %s -> ( h e. RR+ |-> %s ) ~~>r %s )' % (A, G, Wv))
    # the uniform bound
    At2 = '( %s /\\ h e. RR+ )' % A
    trp2 = w.s([], 'simpr', '( %s -> h e. RR+ )' % At2)
    tr = ap(w, At2, 'ld2trs', [J(w, At2, lift(w, w.s([], 'id', '( %s -> %s )' % (A, A)), At2), trp2)], subst(concl('ld2trs'), {'H': 'h'}))
    Atr2 = '( %s /\\ r e. F )' % At2
    M2 = member(w, Atr2, P, c, F, 'r')
    lic2 = licl_member(w, Atr2, c, F, M2, 'r', 'h', lift(w, trp2, Atr2))
    alr2 = dst(w, Atr2, [lic2], 'abscld', '( abs ` %s ) e. RR' % LIt)
    sqr2 = dst(w, Atr2, [alr2], 'resqcld', '( ( abs ` %s ) ^ 2 ) e. RR' % LIt)
    sq02 = dst(w, Atr2, [alr2], 'sqge0d', '0 <_ ( ( abs ` %s ) ^ 2 )' % LIt)
    gr = dst(w, At2, [lift(w, F['fin'], At2), sqr2], 'fsumrecl', '%s e. RR' % G)
    g0 = dst(w, At2, [lift(w, F['fin'], At2), sqr2, sq02], 'fsumge0', '0 <_ %s' % G)
    ag = dst(w, At2, [dst(w, At2, [gr, g0], 'absidd', '( abs ` %s ) = %s' % (G, G)), tr], 'eqbrtrd', '( abs ` %s ) <_ %s' % (G, BV))
    alg = dst(w, A, [ag], 'ralrimiva', 'A. h e. RR+ ( abs ` %s ) <_ %s' % (G, BV))
    bvr = c.mem(BV, 'RR')
    zl = ap(w, A, 'z6rlimle', [fr, J(w, A, bvr, alg)], '( abs ` %s ) <_ %s' % (Wv, BV))
    wr = dst(w, A, [F['fin'], dst(w, Ar, [dst(w, Ar, [vlc], 'abscld', '( abs ` %s ) e. RR' % VLr)], 'resqcld', '( ( abs ` %s ) ^ 2 ) e. RR' % VLr)], 'fsumrecl', '%s e. RR' % Wv)
    la = dst(w, A, [wr], 'leabsd', '%s <_ ( abs ` %s )' % (Wv, Wv))
    dst(w, A, [wr, dst(w, A, [wr], 'x', 'x') if False else dst(w, A, [dst(w, A, [wr], 'recnd', '%s e. CC' % Wv)], 'abscld', '( abs ` %s ) e. RR' % Wv), bvr, la, zl], 'letrd', '%s <_ %s' % (Wv, BV))
    return fin(w)


def ld2cexp():
    w = W('ld2cexp', 'Lean ` classII_exponent ` : ` ( D ^ ( 201 / 800 ) ) ^ 2 D ( Y ^ ( 1/2 - sigma ) ) ^ 2 <_ D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) ` for ` D >_ 1 ` (~ cxpmul , ~ cxpp1d , ~ cxpaddd , ~ cxplead ; the exponents differ by ` 3 / 400 ` ).')
    A = ante('ld2cexp'); P = parts(w, A)
    dr, d1, tr = P['D e. RR'], P['1 < D'], P['T e. RR']
    c = Closure(w, A, {'D': [('RR', dr), ('gt1', d1)], 'T': ('RR', tr)})
    c.have('D', 'gt0', linarith(w, A, [d1], '0 < D', closure=c))
    drp = c.mem('D', 'RR+'); dc = c.mem('D', 'CC'); dn = c.ne0('D')
    E1 = '( ; ; 2 0 1 / ; ; 8 0 0 )'; E2 = '( ; ; 1 5 1 / ; ; 1 0 0 )'; H = '( ( 1 / 2 ) - T )'
    # ( D8 ^ 2 ) = D ^c ( 201/400 )
    x1 = ap(w, A, 'cxpexp', [c.mem(D8, 'CC'), a1(w, A, '2nn0', '2 e. NN0')], '( %s ^c 2 ) = ( %s ^ 2 )' % (D8, D8))
    x2 = ap(w, A, 'cxpmul', [drp, c.mem(E1, 'RR'), c.mem('2', 'CC')], '( D ^c ( %s x. 2 ) ) = ( %s ^c 2 )' % (E1, D8))
    x3 = dst(w, A, [ringeq(w, A, '( %s x. 2 )' % E1, '( ; ; 2 0 1 / ; ; 4 0 0 )', c)], 'oveq2d', '( D ^c ( %s x. 2 ) ) = ( D ^c ( ; ; 2 0 1 / ; ; 4 0 0 ) )' % E1)
    d82 = eqt(w, A, eqc(w, A, x1), eqt(w, A, eqc(w, A, x2), x3))
    # YPT = D ^c ( E2 x. H ), ( YPT ^ 2 ) = D ^c ( ( E2 x. H ) x. 2 )
    EH = '( %s x. %s )' % (E2, H)
    y1 = ap(w, A, 'cxpmul', [drp, c.mem(E2, 'RR'), c.mem(H, 'CC')], '( D ^c %s ) = %s' % (EH, YPT))
    y2 = ap(w, A, 'cxpexp', [c.mem(YPT, 'CC'), a1(w, A, '2nn0', '2 e. NN0')], '( %s ^c 2 ) = ( %s ^ 2 )' % (YPT, YPT))
    y3 = ap(w, A, 'cxpmul', [drp, c.mem(EH, 'RR'), c.mem('2', 'CC')], '( D ^c ( %s x. 2 ) ) = ( ( D ^c %s ) ^c 2 )' % (EH, EH))
    y4 = dst(w, A, [y1], 'oveq1d', '( ( D ^c %s ) ^c 2 ) = ( %s ^c 2 )' % (EH, YPT))
    ypt2 = eqt(w, A, eqc(w, A, y2), eqt(w, A, eqc(w, A, y4), eqc(w, A, y3)))
    # the product
    E3 = '( ; ; 2 0 1 / ; ; 4 0 0 )'
    p1 = dst(w, A, [dc, dn, c.mem(E3, 'CC')], 'cxpp1d', '( D ^c ( %s + 1 ) ) = ( ( D ^c %s ) x. D )' % (E3, E3))
    lhs1 = eqt(w, A, dst(w, A, [d82], 'oveq1d', '( ( %s ^ 2 ) x. D ) = ( ( D ^c %s ) x. D )' % (D8, E3)), eqc(w, A, p1))
    EA = '( %s + 1 )' % E3; EB = '( %s x. 2 )' % EH
    p2 = dst(w, A, [dc, dn, c.mem(EA, 'CC'), c.mem(EB, 'CC')], 'cxpaddd', '( D ^c ( %s + %s ) ) = ( ( D ^c %s ) x. ( D ^c %s ) )' % (EA, EB, EA, EB))
    lhs = eqt(w, A, dst(w, A, [lhs1, ypt2], 'oveq12d', '( ( ( %s ^ 2 ) x. D ) x. ( %s ^ 2 ) ) = ( ( D ^c %s ) x. ( D ^c %s ) )' % (D8, YPT, EA, EB)), eqc(w, A, p2))
    ex = linarith(w, A, [], '( %s + %s ) <_ %s' % (EA, EB, EXP2), closure=c)
    bnd = dst(w, A, [dr, ltle(w, A, c, d1), c.mem('( %s + %s )' % (EA, EB), 'RR'), c.mem(EXP2, 'RR'), ex], 'cxplead', '( D ^c ( %s + %s ) ) <_ ( D ^c %s )' % (EA, EB, EXP2))
    dst(w, A, [lhs, bnd], 'eqbrtrd', '( ( ( %s ^ 2 ) x. D ) x. ( %s ^ 2 ) ) <_ ( D ^c %s )' % (D8, YPT, EXP2))
    return fin(w)


def ld2num():
    w = W('ld2num', 'Lean ` hKsq ` : the constant, ` ( 1 / 36 ) K ^ 2 51200 D log ^ 3 D <_ 10 ^ 25 CTau ^ 2 log ^ 5 D D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) ` (~ ld2cexp ; ` 576 ^ 2 51200 / 36 = 471859200 <_ 5 10 ^ 8 ` , ` 10 ^ 25 = ( 10 ^ 8 ) ^ 3 10 ` ).')
    import lin as _L2
    oldd, oldp = _L2.MAXDEG, _L2.MAXPOW; _L2.MAXDEG = 16; _L2.MAXPOW = 8
    try:
        A = ante('ld2num'); P = parts(w, A); c, F = basecl(w, A, P)
        tr = P['T e. RR']
        kcr = kcfacts(w, A, c, F, tr)
        TEN = '; 1 0'
        TEN25 = '( %s ^ ; 2 5 )' % TEN
        t25 = w.s([w.s([], '10nn', '%s e. NN' % TEN), num.nn0(w, 25), w.inst('nnexpcl')], 'mp2an', '%s e. NN' % TEN25)
        c.leaf(TEN25, 'NN', w.s([t25], 'a1i', '( %s -> %s e. NN )' % (A, TEN25)))
        P83 = '( %s ^ 3 )' % P8; P82 = '( %s ^ 2 )' % P8
        c.leaf(P83, 'NN', c.mem(P83, 'NN')); c.leaf(P82, 'NN', c.mem(P82, 'NN'))
        X2 = '( ( ( %s ^ 2 ) x. D ) x. ( %s ^ 2 ) )' % (D8, YPT)
        CQ = '; ; ; ; ; ; ; ; 4 7 1 8 5 9 2 0 0'
        Q = '( ( %s x. ( %s x. ( CTau ^ 2 ) ) ) x. ( %s ^ 5 ) )' % (CQ, P82, L)
        rg = ringeqp(w, A, '( ( 1 / ; 3 6 ) x. %s )' % BV, '( %s x. %s )' % (Q, X2), c)
        ce = ap(w, A, 'ld2cexp', [J(w, A, J(w, A, F['dr'], F['d1']), tr)], concl('ld2cexp'))
        DE = '( D ^c %s )' % EXP2
        c.leaf(DE, 'RR+', c.mem(DE, 'RR+'))
        m1 = dst(w, A, [c.mem(X2, 'RR'), c.mem(DE, 'RR'), c.mem(Q, 'RR'), c.ge0(Q), ce], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (Q, X2, Q, DE))
        # CQ <_ 5 x. P8 (closed numerals)
        e8 = pow10_8(w)
        LIT8 = num.nat_text(10 ** 8); LIT5 = num.nat_text(5 * 10 ** 8)
        f5 = w.s([w.s([e8], 'oveq2i', '( 5 x. %s ) = ( 5 x. %s )' % (P8, LIT8)), num.mul_lits(w, '5', LIT8)], 'eqtri', '( 5 x. %s ) = %s' % (P8, LIT5))
        cq5 = w.s([num.le_nat(w, 471859200, 5 * 10 ** 8), f5], 'breqtrri', '%s <_ ( 5 x. %s )' % (CQ, P8))
        # 10 ^ 25 = ( ( 10 ^ 8 ) ^ 3 ) x. 10 (closed)
        m83 = num.mul_nat(w, 8, 3)
        a241 = num.add_nat(w, 24, 1)
        tc = num.fact(w, TEN, 'CC')
        ep = w.s([tc, num.nn0(w, 24), w.inst('expp1')], 'mp2an', '( %s ^ ( ; 2 4 + 1 ) ) = ( ( %s ^ ; 2 4 ) x. %s )' % (TEN, TEN, TEN))
        em = w.s([tc, num.nn0(w, 8), num.nn0(w, 3), w.inst('expmul')], 'mp3an', '( %s ^ ( 8 x. 3 ) ) = ( %s ^ 3 )' % (TEN, P8))
        x1 = w.s([a241], 'oveq2i', '( %s ^ ( ; 2 4 + 1 ) ) = %s' % (TEN, TEN25))
        x2 = w.s([m83], 'oveq2i', '( %s ^ ( 8 x. 3 ) ) = ( %s ^ ; 2 4 )' % (TEN, TEN))
        x3 = w.s([x2, em], 'eqtr3i', '( %s ^ ; 2 4 ) = %s' % (TEN, P83))
        x4 = w.s([x3], 'oveq1i', '( ( %s ^ ; 2 4 ) x. %s ) = ( %s x. %s )' % (TEN, TEN, P83, TEN))
        x5 = w.s([x1, ep], 'eqtr3i', '%s = ( ( %s ^ ; 2 4 ) x. %s )' % (TEN25, TEN, TEN))
        x6 = w.s([x5, x4], 'eqtri', '%s = ( %s x. %s )' % (TEN25, P83, TEN))
        t25e = eqt(w, A, w.s([x6], 'a1i', '( %s -> %s = ( %s x. %s ) )' % (A, TEN25, P83, TEN)), ringeq(w, A, '( %s x. %s )' % (P83, TEN), '( %s x. %s )' % (TEN, P83), c))
        # CQ x. P8 ^ 2 <_ 10 ^ 25
        n1 = dst(w, A, [c.mem(CQ, 'RR'), c.mem('( 5 x. %s )' % P8, 'RR'), c.mem(P82, 'RR'), c.ge0(P82), w.s([cq5], 'a1i', '( %s -> %s <_ ( 5 x. %s ) )' % (A, CQ, P8))], 'lemul1ad',
                 '( %s x. %s ) <_ ( ( 5 x. %s ) x. %s )' % (CQ, P82, P8, P82))
        n2 = ringeqp(w, A, '( ( 5 x. %s ) x. %s )' % (P8, P82), '( 5 x. %s )' % P83, c)
        n3 = linarith(w, A, [c.ge0(P83)], '( 5 x. %s ) <_ ( %s x. %s )' % (P83, TEN, P83), closure=c)
        CP = '( %s x. %s )' % (CQ, P82)
        n4 = dst(w, A, [c.mem(CP, 'RR'), c.mem('( 5 x. %s )' % P83, 'RR'), c.mem('( %s x. %s )' % (TEN, P83), 'RR'), dst(w, A, [n1, n2], 'breqtrd', '%s <_ ( 5 x. %s )' % (CP, P83)), n3], 'letrd',
                 '%s <_ ( %s x. %s )' % (CP, TEN, P83))
        n5 = dst(w, A, [n4, eqc(w, A, t25e)], 'breqtrd', '%s <_ %s' % (CP, TEN25))
        # the remaining factor
        WT_ = '( ( ( CTau ^ 2 ) x. ( %s ^ 5 ) ) x. %s )' % (L, DE)
        c.have(WT_, 'RR', c.mem(WT_, 'RR'))
        rq = ringeqp(w, A, '( %s x. %s )' % (Q, DE), '( %s x. %s )' % (CP, WT_), c)
        rf = ringeqp(w, A, '( %s x. %s )' % (TEN25, WT_), FINAL, c)
        m2 = dst(w, A, [c.mem(CP, 'RR'), c.mem(TEN25, 'RR'), c.mem(WT_, 'RR'), c.ge0(WT_), n5], 'lemul1ad', '( %s x. %s ) <_ ( %s x. %s )' % (CP, WT_, TEN25, WT_))
        t1 = dst(w, A, [rg, m1], 'eqbrtrd', '( ( 1 / ; 3 6 ) x. %s ) <_ ( %s x. %s )' % (BV, Q, DE))
        t2 = dst(w, A, [dst(w, A, [rq, m2], 'eqbrtrd', '( %s x. %s ) <_ ( %s x. %s )' % (Q, DE, TEN25, WT_)), rf], 'breqtrd', '( %s x. %s ) <_ %s' % (Q, DE, FINAL))
        dst(w, A, [c.mem('( ( 1 / ; 3 6 ) x. %s )' % BV, 'RR'), c.mem('( %s x. %s )' % (Q, DE), 'RR'), c.mem(FINAL, 'RR'), t1, t2], 'letrd', '( ( 1 / ; 3 6 ) x. %s ) <_ %s' % (BV, FINAL))
        return fin(w)
    finally:
        _L2.MAXDEG = oldd; _L2.MAXPOW = oldp


def ld2ssq():
    w = W('ld2ssq', 'Lean ` sum_sq_EctrHalf_le ` (Lemma L1.f, the headline of section 6 and of LoggedDetector.lean): over a ` 1 ` -separated family of zeros ` ( chi_r , rho_r ) ` in the strip ` sigma <_ Re rho_r <_ 1 ` , ` abs Im rho_r <_ t ` , with ` D = d ( t + 2 ) ` , ` sum_ r abs EctrHalf ( chi_r , rho_r ) ^ 2 <_ 10 ^ 25 CTau ^ 2 log ^ 5 D D ^ ( ( 151 / 50 ) ( 1 - sigma ) ) ` (~ ld2lim through ` abs ( 1 / ( 2 pi i ) ) ^ 2 <_ 1 / 36 ` , ~ ld2num ).')
    A = ante('ld2ssq'); P, c, F = famsetup(w, A)
    kcr = kcfacts(w, A, c, F, F['tr'])
    c.leaf('_pi', 'RR+', a1(w, A, 'pirp', '_pi e. RR+')); c.leaf('_i', 'CC', a1(w, A, 'ax-icn', '_i e. CC')); c.leaf('_i', 'ne0', a1(w, A, 'ine0', '_i =/= 0'))
    TP = '( 2 x. _pi )'; RT = '( 1 / %s )' % TP; RTI = '( 1 / %s )' % TPI
    c.leaf(RT, 'RR+', c.mem(RT, 'RR+'))
    IP = '( _i x. _pi )'
    ipc = c.mem(IP, 'CC'); ipn = dst(w, A, [c.mem('_i', 'CC'), c.mem('_pi', 'CC'), c.ne0('_i'), c.ne0('_pi')], 'mulne0d', '%s =/= 0' % IP)
    c.leaf(TPI, 'CC', c.mem(TPI, 'CC')); c.leaf(TPI, 'ne0', dst(w, A, [c.mem('2', 'CC'), ipc, c.ne0('2'), ipn], 'mulne0d', '%s =/= 0' % TPI))
    Ar = '( %s /\\ r e. F )' % A
    M = member(w, Ar, P, c, F, 'r')
    cv = ap(w, Ar, 'ld2vlcv', [M['a7c']], subst(concl('ld2vlcv'), FAM('r')))
    VLr = VLK('r')
    vlc = w.s([cv, w.inst('rlimcl')], 'syl', '( %s -> %s e. CC )' % (Ar, VLr))
    AV = '( abs ` %s )' % VLr
    avr = dst(w, Ar, [vlc], 'abscld', '%s e. RR' % AV); avc = dst(w, Ar, [avr], 'recnd', '%s e. CC' % AV)
    cr = child(w, Ar, c)
    tpic = cr.mem(TPI, 'CC'); tpin = cr.ne0(TPI)
    ECT = ECTRK('r')
    assert ECT == '( %s x. %s )' % (RTI, VLr), ECT[:80]
    ab1 = dst(w, Ar, [cr.mem(RTI, 'CC'), vlc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. %s )' % (ECT, RTI, AV))
    ab2 = dst(w, Ar, [cr.mem('1', 'CC'), tpic, tpin], 'absdivd', '( abs ` %s ) = ( ( abs ` 1 ) / ( abs ` %s ) )' % (RTI, TPI))
    ab3 = w.s([w.s([], 'abs1', '( abs ` 1 ) = 1'), w.s([], 'abstpi', '( abs ` %s ) = %s' % (TPI, TP))], 'oveq12i', '( ( abs ` 1 ) / ( abs ` %s ) ) = %s' % (TPI, RT))
    ab4 = eqt(w, Ar, ab2, w.s([ab3], 'a1i', '( %s -> ( ( abs ` 1 ) / ( abs ` %s ) ) = %s )' % (Ar, TPI, RT)))
    ab5 = eqt(w, Ar, ab1, dst(w, Ar, [ab4], 'oveq1d', '( ( abs ` %s ) x. %s ) = ( %s x. %s )' % (RTI, AV, RT, AV)))
    sq = eqt(w, Ar, dst(w, Ar, [ab5], 'oveq1d', '( ( abs ` %s ) ^ 2 ) = ( ( %s x. %s ) ^ 2 )' % (ECT, RT, AV)),
             dst(w, Ar, [cr.mem(RT, 'CC'), avc], 'sqmuld', '( ( %s x. %s ) ^ 2 ) = ( ( %s ^ 2 ) x. ( %s ^ 2 ) )' % (RT, AV, RT, AV)))
    LHS = 'sum_ r e. F ( ( abs ` %s ) ^ 2 )' % ECT
    RT2 = '( %s ^ 2 )' % RT; AV2 = '( %s ^ 2 )' % AV
    se = dst(w, A, [sq], 'sumeq2dv', '%s = sum_ r e. F ( %s x. %s )' % (LHS, RT2, AV2))
    av2c = dst(w, Ar, [avc], 'sqcld', '%s e. CC' % AV2)
    fm = dst(w, A, [F['fin'], c.mem(RT2, 'CC'), av2c], 'fsummulc2', '( %s x. sum_ r e. F %s ) = sum_ r e. F ( %s x. %s )' % (RT2, AV2, RT2, AV2))
    SV = 'sum_ r e. F %s' % AV2
    svr = dst(w, A, [F['fin'], dst(w, Ar, [avr], 'resqcld', '%s e. RR' % AV2)], 'fsumrecl', '%s e. RR' % SV)
    c.leaf(SV, 'RR', svr)
    lim = ap(w, A, 'ld2lim', [F['hfam']], concl('ld2lim'))
    assert body(w, lim, A) == '%s <_ %s' % (SV, BV), body(w, lim, A)[-200:]
    # ( 1 / ( 2 pi ) ) ^ 2 <_ 1 / 36
    six = linarith(w, A, [a1(w, A, 'pige3', '3 <_ _pi')], '6 <_ %s' % TP, closure=c)
    lr = dst(w, A, [c.mem('6', 'RR+'), c.mem(TP, 'RR+')], 'lerecd', '( 6 <_ %s <-> %s <_ ( 1 / 6 ) )' % (TP, RT))
    r6 = dst(w, A, [six, lr], 'mpbid', '%s <_ ( 1 / 6 )' % RT)
    sq6 = ap(w, A, 'le2sq2', [J(w, A, c.mem(RT, 'RR'), c.ge0(RT)), J(w, A, c.mem('( 1 / 6 )', 'RR'), r6)], '%s <_ ( ( 1 / 6 ) ^ 2 )' % RT2)
    e36 = ringeqp(w, A, '( ( 1 / 6 ) ^ 2 )', '( 1 / ; 3 6 )', c)
    rt36 = dst(w, A, [sq6, e36], 'breqtrd', '%s <_ ( 1 / ; 3 6 )' % RT2)
    # the chain
    bvr = c.mem(BV, 'RR'); bv0 = c.ge0(BV)
    m1 = dst(w, A, [svr, bvr, c.mem(RT2, 'RR'), c.ge0(RT2), lim], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (RT2, SV, RT2, BV))
    m2 = dst(w, A, [c.mem(RT2, 'RR'), c.mem('( 1 / ; 3 6 )', 'RR'), bvr, bv0, rt36], 'lemul1ad', '( %s x. %s ) <_ ( ( 1 / ; 3 6 ) x. %s )' % (RT2, BV, BV))
    nm = ap(w, A, 'ld2num', [J(w, A, F['hz'], F['tr'])], concl('ld2num'))
    t1 = dst(w, A, [se, eqc(w, A, fm)], 'eqtrd', '%s = ( %s x. %s )' % (LHS, RT2, SV))
    t2 = dst(w, A, [c.mem('( %s x. %s )' % (RT2, SV), 'RR'), c.mem('( %s x. %s )' % (RT2, BV), 'RR'), c.mem('( ( 1 / ; 3 6 ) x. %s )' % BV, 'RR'), m1, m2], 'letrd', '( %s x. %s ) <_ ( ( 1 / ; 3 6 ) x. %s )' % (RT2, SV, BV))
    t3 = dst(w, A, [c.mem('( %s x. %s )' % (RT2, SV), 'RR'), c.mem('( ( 1 / ; 3 6 ) x. %s )' % BV, 'RR'), c.mem(FINAL, 'RR'), t2, nm], 'letrd', '( %s x. %s ) <_ %s' % (RT2, SV, FINAL))
    dst(w, A, [t1, t3], 'eqbrtrd', '%s <_ %s' % (LHS, FINAL))
    return fin(w)


if __name__ == '__main__':
    for f in (ld2mrds, ld2mmass, ld2hp6, ld2mvu, ld2mvw, ld2int, ld2trs, ld2lim, ld2cexp, ld2num, ld2ssq):
        if want(f.__name__):
            f()
