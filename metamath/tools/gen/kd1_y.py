"""Sortie KD1: the l2 zero sum at s0 = ( 1 + E ) + i T (kdl2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from kd1lib import *
from cl import formula_of, lift, split_imp
from c9lib import top_and
from c8lib import tsub
from lin import linarith, lineq
from mvlib import ringeq

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def gen_l2():
    w = W('kdl2', 'Lean ` KDerivDetect.sum_ord_div_normSq_le ` (with ` div_normSq_le_re_div ` ): ` sum_ZD m / abs ( s0 - q ) ^ 2 <_ ( 1 / E ) ( ( 5 / 4 ) / E + 5 + 17500000 log ( N ( abs T + 2 ) ) ) ` at ` s0 = ( 1 + E ) + i T ` (Lean ` 1 / E + 2 ` : ZC1 ` lchrldre ` ; C10 ` lndlchrk ` ).')
    A0 = S['kdl2'].split(' -> sum_')[0][2:]
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    chi = s([], 'simpl', CHI)
    tee = s([], 'simpr', '( T e. RR /\\ E e. RR+ /\\ E <_ %s )' % R120)
    tr = s([tee], 'simp1d', 'T e. RR'); ep = s([tee], 'simp2d', 'E e. RR+'); e20 = s([tee], 'simp3d', 'E <_ %s' % R120)
    er = s([ep], 'rpred', 'E e. RR'); e0 = s([ep], 'rpgt0d', '0 < E')
    SS = S0(); CC_ = CT('T')
    c = Closure(w, A0, {'E': ('RR', er), 'T': ('RR', tr)})
    e1 = linarith(w, A0, [e20], 'E <_ 1', closure=c)
    oe = c.mem('( 1 + E )', 'RR')
    s0c = s([s([oe], 'recnd', '( 1 + E ) e. CC'), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')], 'addcld', '%s e. CC' % SS)
    rs0 = s([oe, tr, w.inst('crre')], 'syl2anc', '( Re ` %s ) = ( 1 + E )' % SS)
    # the two bounds at s0
    LDR = tsub(stmt('lchrldre'), {'U': 'E', 'S': SS})
    lra, lrc = split_imp(LDR)
    ldr = s([chi, s([s([ep, e1], 'jca', '( E e. RR+ /\\ E <_ 1 )'), s([s0c, rs0], 'jca', '( %s e. CC /\\ ( Re ` %s ) = ( 1 + E ) )' % (SS, SS))], 'jca', top_and(lra)[1]), w.inst('lchrldre')], 'syl2anc', lrc)
    LD = lrc.split('( abs ` ', 1)[1].rsplit(' ) <_ ', 1)[0]
    # |s0 - c| <_ 3/2 and L(s0) =/= 0
    cc_ = s([w.s([w.s([], '2cn', '2 e. CC')], 'a1i', '( %s -> 2 e. CC )' % A0), s([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0), s([tr], 'recnd', 'T e. CC')], 'mulcld', '( _i x. T ) e. CC')],
            'addcld', '%s e. CC' % CC_)
    cd = Closure(w, A0, {'E': ('CC', s([er], 'recnd', 'E e. CC')), 'T': ('CC', s([tr], 'recnd', 'T e. CC'))})
    cd.leaf('_i', 'CC', w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A0)); cd.atom('_i')
    dif = ringeq(w, A0, '( %s - %s )' % (SS, CC_), '( E - 1 )', cd)
    ad = s([s([dif], 'fveq2d', '( abs ` ( %s - %s ) ) = ( abs ` ( E - 1 ) )' % (SS, CC_)), s([s([er], 'recnd', 'E e. CC') and er, w.s([], '1red', '( %s -> 1 e. RR )' % A0), e1], 'abssuble0d', '( abs ` ( E - 1 ) ) = ( 1 - E )')],
           'eqtrd', '( abs ` ( %s - %s ) ) = ( 1 - E )' % (SS, CC_))
    d32 = s([ad, linarith(w, A0, [e0], '( 1 - E ) <_ ( 3 / 2 )', closure=c)], 'eqbrtrd', '( abs ` ( %s - %s ) ) <_ ( 3 / 2 )' % (SS, CC_))
    DDs = stmt('ef2ddl').split(' -> ', 1)[1][:-2]
    dd = s([chi, w.inst('ef2ddl')], 'syl', DDs)
    NV = top_and(top_and(DDs)[2])[1]
    nv = s([s([dd], 'simp3d', top_and(DDs)[2])], 'simprd', NV)
    cs = Closure(w, A0, {'E': ('RR', er), '( Re ` %s )' % SS: ('RR', s([s0c], 'recld', '( Re ` %s ) e. RR' % SS))}); cs.atom('( Re ` %s )' % SS)
    s01 = linarith(w, A0, [rs0, e0], '1 < ( Re ` %s )' % SS, closure=cs)
    s00 = linarith(w, A0, [rs0, e0], '0 < ( Re ` %s )' % SS, closure=cs)
    shp = s([s([s0c, s00], 'jca', '( %s e. CC /\\ 0 < ( Re ` %s ) )' % (SS, SS)), s([w.s([], '0red', '( %s -> 0 e. RR )' % A0), w.inst('elhp2')], 'syl', '( %s e. %s <-> ( %s e. CC /\\ 0 < ( Re ` %s ) ) )' % (SS, HP0, SS, SS))],
            'mpbird', '%s e. %s' % (SS, HP0))
    idw = w.s([], 'id', '( w = %s -> w = %s )' % (SS, SS))
    cw, nw = w.wcongr('( 1 < ( Re ` w ) -> ( %s ` w ) =/= 0 )' % LFN, {'w': SS}, 'w = %s' % SS, {'w': idw})
    lnz = s([s([shp, nv, w.s([cw], 'rspcv', '( %s e. %s -> ( %s -> %s ) )' % (SS, HP0, NV, nw))], 'sylc', nw), s01], 'mpd', '( %s ` %s ) =/= 0' % (LFN, SS))
    LN = tsub(stmt('lndlchrk'), {'S': SS})
    lna, lnc = split_imp(LN)
    ln = s([s([chi, tr], 'jca', top_and(lna)[0]), s([s0c, d32, lnz], '3jca', top_and(lna)[1]), w.inst('lndlchrk')], 'syl2anc', lnc)
    SG = 'sum_ q e. %s ( %s / ( %s - q ) )' % (ZD(), MU(), SS)
    assert lnc == '( abs ` ( %s - %s ) ) <_ %s' % (LD, SG, KL), lnc[-400:]
    # per zero
    Aq = '( %s /\\ q e. %s )' % (A0, ZD())
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (Aq, f))
    L = lambda st: lift(w, st, Aq)
    qq = a([], 'simpr', 'q e. %s' % ZD())
    LZ = stmt('lchrzc8'); lza, lzc = split_imp(LZ)
    lz = s([s([chi, tr], 'jca', lza), w.inst('lchrzc8')], 'syl', lzc)
    zfin = s([lz], 'simp1d', top_and(lzc)[0]); zord = s([lz], 'simp2d', top_and(lzc)[1])
    M_ = MU('q')
    mn = a([qq, a([L(zord), w.inst('rsp')], 'syl', '( q e. %s -> %s e. NN )' % (ZD(), M_))], 'mpd', '%s e. NN' % M_)
    mr = a([mn], 'nnred', '%s e. RR' % M_); m0 = a([a([mn], 'nnrpd', '%s e. RR+' % M_)], 'rpge0d', '0 <_ %s' % M_); mc = a([mr], 'recnd', '%s e. CC' % M_)
    rq = a([L(chi), L(tr), qq, w.inst('kdre1')], 'syl3anc', '( Re ` q ) <_ 1')
    SQ13 = SQ(CC_, R138)
    RI_ = '( %s + ( _i x. %s ) )' % (R138, R138)
    cq = Closure(w, Aq, {'T': ('RR', L(tr)), 'E': ('RR', L(er))})
    ric = a([a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138), a([w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % Aq), a([cq.mem(R138, 'RR')], 'recnd', '%s e. CC' % R138)], 'mulcld', '( _i x. %s ) e. CC' % R138)],
            'addcld', '%s e. CC' % RI_)
    sqcc = a([a([a([L(cc_), ric], 'subcld', '%s e. CC' % A13), a([L(cc_), ric], 'addcld', '%s e. CC' % B13)], 'jca', '( %s e. CC /\\ %s e. CC )' % (A13, B13)), w.inst('crectss')], 'syl', '%s C_ CC' % SQ13)
    qc = a([sqcc, a([w.s([w.s([], 'ssrab2', '%s C_ %s' % (ZD(), SQ13))], 'a1i', '( %s -> %s C_ %s )' % (Aq, ZD(), SQ13)), qq], 'sseldd', 'q e. %s' % SQ13)], 'sseldd', 'q e. CC')
    Z_ = '( %s - q )' % SS
    zc = a([L(s0c), qc], 'subcld', '%s e. CC' % Z_)
    rz = a([L(s0c), qc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` q ) )' % (Z_, SS))
    cq.leaf('( Re ` q )', 'RR', a([qc], 'recld', '( Re ` q ) e. RR')); cq.atom('( Re ` q )')
    cq.leaf('( Re ` %s )' % SS, 'RR', a([L(s0c)], 'recld', '( Re ` %s ) e. RR' % SS)); cq.atom('( Re ` %s )' % SS)
    cq.leaf('( Re ` %s )' % Z_, 'RR', a([zc], 'recld', '( Re ` %s ) e. RR' % Z_)); cq.atom('( Re ` %s )' % Z_)
    ez = linarith(w, Aq, [rz, L(rs0), rq], 'E <_ ( Re ` %s )' % Z_, closure=cq)
    zpos = linarith(w, Aq, [rz, L(rs0), rq, L(e0)], '0 < ( Re ` %s )' % Z_, closure=cq)
    rne0 = a([a([zpos], 'gt0ne0d', '( Re ` %s ) =/= 0' % Z_), w.s([w.s([], 're0', '( Re ` 0 ) = 0')], 'a1i', '( %s -> ( Re ` 0 ) = 0 )' % Aq)], 'neeqtrrd', '( Re ` %s ) =/= ( Re ` 0 )' % Z_)
    zn = a([rne0, w.s([w.s([], 'fveq2', '( %s = 0 -> ( Re ` %s ) = ( Re ` 0 ) )' % (Z_, Z_))], 'necon3i', '( ( Re ` %s ) =/= ( Re ` 0 ) -> %s =/= 0 )' % (Z_, Z_))], 'syl', '%s =/= 0' % Z_)
    Q_ = '( ( abs ` %s ) ^ 2 )' % Z_
    azp = a([zc, zn], 'absrpcld', '( abs ` %s ) e. RR+' % Z_)
    qp = a([azp, w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % Aq)], 'rpexpcld', '%s e. RR+' % Q_)
    qr = a([qp], 'rpred', '%s e. RR' % Q_); qcc = a([qp], 'rpcnd', '%s e. CC' % Q_); qn = a([qp], 'rpne0d', '%s =/= 0' % Q_)
    # Re ( M / Z ) = M ( Re Z / Q )
    r1 = a([mc, zc, zn], 'divrecd', '( %s / %s ) = ( %s x. ( 1 / %s ) )' % (M_, Z_, M_, Z_))
    r2 = a([zc, zn, w.inst('recval')], 'syl2anc', '( 1 / %s ) = ( ( * ` %s ) / %s )' % (Z_, Z_, Q_))
    r3 = a([r1, a([r2], 'oveq2d', '( %s x. ( 1 / %s ) ) = ( %s x. ( ( * ` %s ) / %s ) )' % (M_, Z_, M_, Z_, Q_))], 'eqtrd', '( %s / %s ) = ( %s x. ( ( * ` %s ) / %s ) )' % (M_, Z_, M_, Z_, Q_))
    cj = a([zc], 'cjcld', '( * ` %s ) e. CC' % Z_)
    r4 = a([mr, a([cj, qcc, qn], 'divcld', '( ( * ` %s ) / %s ) e. CC' % (Z_, Q_))], 'remul2d', '( Re ` ( %s x. ( ( * ` %s ) / %s ) ) ) = ( %s x. ( Re ` ( ( * ` %s ) / %s ) ) )' % (M_, Z_, Q_, M_, Z_, Q_))
    r5 = a([qr, cj, qn], 'redivd', '( Re ` ( ( * ` %s ) / %s ) ) = ( ( Re ` ( * ` %s ) ) / %s )' % (Z_, Q_, Z_, Q_))
    r6 = a([zc], 'recjd', '( Re ` ( * ` %s ) ) = ( Re ` %s )' % (Z_, Z_))
    RZ = '( ( Re ` %s ) / %s )' % (Z_, Q_)
    r7 = a([r5, a([r6], 'oveq1d', '( ( Re ` ( * ` %s ) ) / %s ) = %s' % (Z_, Q_, RZ))], 'eqtrd', '( Re ` ( ( * ` %s ) / %s ) ) = %s' % (Z_, Q_, RZ))
    ReMZ = '( Re ` ( %s / %s ) )' % (M_, Z_)
    r8 = a([a([r3], 'fveq2d', '%s = ( Re ` ( %s x. ( ( * ` %s ) / %s ) ) )' % (ReMZ, M_, Z_, Q_)), r4, a([r7], 'oveq2d', '( %s x. ( Re ` ( ( * ` %s ) / %s ) ) ) = ( %s x. %s )' % (M_, Z_, Q_, M_, RZ))],
           '3eqtrd', '%s = ( %s x. %s )' % (ReMZ, M_, RZ))
    # M / Q <_ ( 1 / E ) ( M ( Re Z / Q ) )
    EQ = '( E / %s )' % Q_
    eqr = a([L(er), qp], 'rerpdivcld', '%s e. RR' % EQ)
    rzr = a([a([zc], 'recld', '( Re ` %s ) e. RR' % Z_), qp], 'rerpdivcld', '%s e. RR' % RZ)
    b1 = a([L(er), a([zc], 'recld', '( Re ` %s ) e. RR' % Z_), qp, ez], 'lediv1dd', '%s <_ %s' % (EQ, RZ))
    b2 = a([eqr, rzr, mr, m0, b1], 'lemul2ad', '( %s x. %s ) <_ ( %s x. %s )' % (M_, EQ, M_, RZ))
    ie = '( 1 / E )'
    ier = a([L(ep)], 'rprecred', '%s e. RR' % ie); ie0 = a([a([L(ep)], 'rpreccld', '%s e. RR+' % ie)], 'rpge0d', '0 <_ %s' % ie)
    b3 = a([a([mr, eqr], 'remulcld', '( %s x. %s ) e. RR' % (M_, EQ)), a([mr, rzr], 'remulcld', '( %s x. %s ) e. RR' % (M_, RZ)), ier, ie0, b2], 'lemul2ad',
           '( %s x. ( %s x. %s ) ) <_ ( %s x. ( %s x. %s ) )' % (ie, M_, EQ, ie, M_, RZ))
    ec = a([L(er)], 'recnd', 'E e. CC'); en = a([L(ep)], 'rpne0d', 'E =/= 0')
    d1 = a([mc, ec, qcc, qn], 'div12d', '( %s x. %s ) = ( E x. ( %s / %s ) )' % (M_, EQ, M_, Q_))
    MQ = '( %s / %s )' % (M_, Q_)
    mqc = a([mc, qcc, qn], 'divcld', '%s e. CC' % MQ)
    d2 = a([a([ec, en], 'reccld', '%s e. CC' % ie), ec, mqc], 'mulassd', '( ( %s x. E ) x. %s ) = ( %s x. ( E x. %s ) )' % (ie, MQ, ie, MQ))
    d3 = a([a([ec, en], 'recid2d', '( %s x. E ) = 1' % ie)], 'oveq1d', '( ( %s x. E ) x. %s ) = ( 1 x. %s )' % (ie, MQ, MQ))
    d4 = a([mqc], 'mullidd', '( 1 x. %s ) = %s' % (MQ, MQ))
    d5 = a([a([d2, d3], 'eqtr3d', '( %s x. ( E x. %s ) ) = ( 1 x. %s )' % (ie, MQ, MQ)), d4], 'eqtrd', '( %s x. ( E x. %s ) ) = %s' % (ie, MQ, MQ))
    d6 = a([a([d1], 'oveq2d', '( %s x. ( %s x. %s ) ) = ( %s x. ( E x. %s ) )' % (ie, M_, EQ, ie, MQ)), d5], 'eqtrd', '( %s x. ( %s x. %s ) ) = %s' % (ie, M_, EQ, MQ))
    tb = a([a([d6], 'eqcomd', '%s = ( %s x. ( %s x. %s ) )' % (MQ, ie, M_, EQ)), b3, a([a([r8], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (ie, ReMZ, ie, M_, RZ))], 'eqcomd',
                                                                                                    '( %s x. ( %s x. %s ) ) = ( %s x. %s )' % (ie, M_, RZ, ie, ReMZ))], '3brtr4d' if False else 'T.', 'T.') if False else None
    tb1 = a([a([d6], 'eqcomd', '%s = ( %s x. ( %s x. %s ) )' % (MQ, ie, M_, EQ)), b3], 'eqbrtrd', '%s <_ ( %s x. ( %s x. %s ) )' % (MQ, ie, M_, RZ))
    tb2 = a([tb1, a([r8], 'oveq2d', '( %s x. %s ) = ( %s x. ( %s x. %s ) )' % (ie, ReMZ, ie, M_, RZ))], 'breqtrrd', '%s <_ ( %s x. %s )' % (MQ, ie, ReMZ))
    mqr = a([mr, qp], 'rerpdivcld', '%s e. RR' % MQ)
    mzc = a([mc, zc, zn], 'divcld', '( %s / %s ) e. CC' % (M_, Z_))
    rmz = a([mzc], 'recld', '%s e. RR' % ReMZ)
    irm = a([ier, rmz], 'remulcld', '( %s x. %s ) e. RR' % (ie, ReMZ))
    SMQ = 'sum_ q e. %s %s' % (ZD(), MQ)
    SIR = 'sum_ q e. %s ( %s x. %s )' % (ZD(), ie, ReMZ)
    SRe = 'sum_ q e. %s %s' % (ZD(), ReMZ)
    f1 = s([zfin, mqr, irm, tb2], 'fsumle', '%s <_ %s' % (SMQ, SIR))
    f2 = s([zfin, s([s([ep], 'rprecred', '%s e. RR' % ie)], 'recnd', '%s e. CC' % ie), a([rmz], 'recnd', '%s e. CC' % ReMZ)], 'fsummulc2', '( %s x. %s ) = %s' % (ie, SRe, SIR))
    f3 = s([zfin, mzc], 'fsumre', '( Re ` %s ) = %s' % (SG, SRe))
    f4 = s([s([f3], 'oveq2d', '( %s x. ( Re ` %s ) ) = ( %s x. %s )' % (ie, SG, ie, SRe)), f2], 'eqtrd', '( %s x. ( Re ` %s ) ) = %s' % (ie, SG, SIR))
    # Re SG <_ ( 5/4 ) / E + 5 + KL
    sgc = s([zfin, mzc], 'fsumcl', '%s e. CC' % SG)
    hol = s([dd], 'simp1d', top_and(DDs)[0])
    ldn = s([s([hol, w.inst('holf')], 'syl', '( CC _D %s ) : %s --> CC' % (LFN, HP0)), shp], 'ffvelcdmd', '( ( CC _D %s ) ` %s ) e. CC' % (LFN, SS))
    lfv = s([s([s([hol, w.inst('simpl')], 'syl', '%s e. ( %s -cn-> CC )' % (LFN, HP0)), w.inst('cncff')], 'syl', '%s : %s --> CC' % (LFN, HP0)), shp], 'ffvelcdmd', '( %s ` %s ) e. CC' % (LFN, SS))
    ldc = s([ldn, lfv, lnz], 'divcld', '%s e. CC' % LD)
    DIF = '( %s - %s )' % (LD, SG)
    difc = s([ldc, sgc], 'subcld', '%s e. CC' % DIF)
    rdf = s([ldc, sgc], 'resubd', '( Re ` %s ) = ( ( Re ` %s ) - ( Re ` %s ) )' % (DIF, LD, SG))
    rle = s([ldc], 'releabsd', '( Re ` %s ) <_ ( abs ` %s )' % (LD, LD))
    rn = s([difc], 'renegd', '( Re ` -u %s ) = -u ( Re ` %s )' % (DIF, DIF))
    rnl = s([s([difc], 'negcld', '-u %s e. CC' % DIF)], 'releabsd', '( Re ` -u %s ) <_ ( abs ` -u %s )' % (DIF, DIF))
    an = s([difc], 'absnegd', '( abs ` -u %s ) = ( abs ` %s )' % (DIF, DIF))
    RB = '( ( ( 5 / 4 ) / E ) + 5 )'
    cz = Closure(w, A0, {'E': ('RR', er)})
    cz.have('E', 'gt0', e0)
    for e_, st in (('( Re ` %s )' % LD, s([ldc], 'recld', '( Re ` %s ) e. RR' % LD)), ('( Re ` %s )' % SG, s([sgc], 'recld', '( Re ` %s ) e. RR' % SG)),
                   ('( Re ` %s )' % DIF, s([difc], 'recld', '( Re ` %s ) e. RR' % DIF)), ('( Re ` -u %s )' % DIF, s([s([difc], 'negcld', '-u %s e. CC' % DIF)], 'recld', '( Re ` -u %s ) e. RR' % DIF)),
                   ('( abs ` %s )' % LD, s([ldc], 'abscld', '( abs ` %s ) e. RR' % LD)), ('( abs ` %s )' % DIF, s([difc], 'abscld', '( abs ` %s ) e. RR' % DIF)),
                   ('( abs ` -u %s )' % DIF, s([s([difc], 'negcld', '-u %s e. CC' % DIF)], 'abscld', '( abs ` -u %s ) e. RR' % DIF)),
                   ('( log ` ( N x. ( ( abs ` T ) + 2 ) ) )', None)):
        if st is not None:
            cz.leaf(e_, 'RR', st); cz.atom(e_)
    # log real
    nn_ = s([s([chi], 'simpld', NXH)], 'simpld', 'N e. NN')
    at = s([s([tr], 'recnd', 'T e. CC')], 'abscld', '( abs ` T ) e. RR')
    ca = Closure(w, A0, {'( abs ` T )': ('RR', at)}); ca.atom('( abs ` T )')
    t2p = s([ca.mem('( ( abs ` T ) + 2 )', 'RR'), linarith(w, A0, [s([s([tr], 'recnd', 'T e. CC')], 'absge0d', '0 <_ ( abs ` T )')], '0 < ( ( abs ` T ) + 2 )', closure=ca)], 'elrpd', '( ( abs ` T ) + 2 ) e. RR+')
    XT = '( N x. ( ( abs ` T ) + 2 ) )'
    lg = s([s([s([nn_], 'nnrpd', 'N e. RR+'), t2p], 'rpmulcld', '%s e. RR+' % XT)], 'relogcld', '( log ` %s ) e. RR' % XT)
    cz.leaf('( log ` %s )' % XT, 'RR', lg); cz.atom('( log ` %s )' % XT)
    rsg = linarith(w, A0, [rdf, rle, rn, rnl, an, ldr, ln], '( Re ` %s ) <_ ( %s + %s )' % (SG, RB, KL), closure=cz)
    iep = s([ep], 'rpreccld', '%s e. RR+' % ie)
    b5 = s([s([sgc], 'recld', '( Re ` %s ) e. RR' % SG), cz.mem('( %s + %s )' % (RB, KL), 'RR'), s([iep], 'rpred', '%s e. RR' % ie), s([iep], 'rpge0d', '0 <_ %s' % ie), rsg], 'lemul2ad',
           '( %s x. ( Re ` %s ) ) <_ ( %s x. ( %s + %s ) )' % (ie, SG, ie, RB, KL))
    b6 = s([f4, b5], 'eqbrtrrd', '%s <_ ( %s x. ( %s + %s ) )' % (SIR, ie, RB, KL))
    fin = s([s([zfin, mqr], 'fsumrecl', '%s e. RR' % SMQ), s([zfin, irm], 'fsumrecl', '%s e. RR' % SIR), cz.mem('( %s x. ( %s + %s ) )' % (ie, RB, KL), 'RR'), f1, b6], 'letrd',
            '%s <_ ( %s x. ( %s + %s ) )' % (SMQ, ie, RB, KL))
    w.lines.append('qed:%s:idi |- %s' % (fin, S['kdl2']))
    return run(w)




if __name__ == '__main__':
    gen_l2()
