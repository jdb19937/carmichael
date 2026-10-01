"""Sortie CEN2: character values, the unimodular twist, and the constant/diagonal series group (cen2chv, cen2tw, cen2gc;
Lean Census huf_le, hph_le, hsum0, hsum3, hbound0, hbound3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from cen2lib import *
from cl import split_imp, Closure, lift
from c9lib import top_and
from lin import linarith, nlinarith

only = sys.argv[1:]


def run(w):
    if only and w.label not in only:
        return True
    return w.run()


def icn(w, A):
    return w.s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '( %s -> _i e. CC )' % A)


def gen_chv():
    w = W('cen2chv', 'A Dirichlet character value at an integer is a complex number of absolute value at most 1 (Lean ` DirichletCharacter.norm_le_one ` ).')
    A0, C0 = split_imp(S['cen2chv'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    nx = s([], 'simpl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )')
    nn = s([nx], 'simpld', 'N e. NN'); xd = s([nx], 'simprd', 'X e. ( Base ` ( DChr ` N ) )')
    az = s([], 'simpr', 'A e. ZZ')
    G = '( DChr ` N )'; DN = '( Base ` %s )' % G; ZN = '( Z/nZ ` N )'; BN = '( Base ` %s )' % ZN; LN = '( ZRHom ` %s )' % ZN
    eg = w.s([], 'eqid', '%s = %s' % (G, G)); ed = w.s([], 'eqid', '%s = %s' % (DN, DN))
    ez = w.s([], 'eqid', '%s = %s' % (ZN, ZN)); eb = w.s([], 'eqid', '%s = %s' % (BN, BN)); el = w.s([], 'eqid', '%s = %s' % (LN, LN))
    fo = w.s([ez, eb, el], 'znzrhfo', '( N e. NN0 -> %s : ZZ -onto-> %s )' % (LN, BN))
    lf = s([s([s([nn], 'nnnn0d', 'N e. NN0'), fo], 'syl', '%s : ZZ -onto-> %s' % (LN, BN)), w.inst('fof')], 'syl', '%s : ZZ --> %s' % (LN, BN))
    LA = '( %s ` A )' % LN
    lb = s([lf, az], 'ffvelcdmd', '%s e. %s' % (LA, BN))
    xf = s([eg, ez, ed, eb, xd], 'dchrf', 'X : %s --> CC' % BN)
    cc = s([xf, lb], 'ffvelcdmd', '%s e. CC' % CHV('A'))
    ab = s([eg, ed, ez, eb, xd, lb], 'dchrabs2', '( abs ` %s ) <_ 1' % CHV('A'))
    w.qed([cc, ab], 'jca', S['cen2chv'])
    return run(w)


def gen_tw():
    w = W('cen2tw', 'The twist ` k ^c -u ( _i T ) ` for real ` T ` has absolute value 1 (Lean Census ` hph_le ` ).')
    A0, C0 = split_imp(S['cen2tw'])
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    kn = s([], 'simpl', 'k e. NN'); tr = s([], 'simpr', 'T e. RR')
    ic = icn(w, A0)
    c = Closure(w, A0, {'k': ('NN', kn), 'T': ('RR', tr), '_i': ('CC', ic)})
    IT = '( _i x. T )'; NI = '-u %s' % IT; TWT = TW('T')
    nic = c.mem(NI, 'CC')
    tc = s([c.mem('k', 'CC'), nic], 'cxpcld', '%s e. CC' % TWT)
    a1 = s([c.mem('k', 'RR+'), nic, w.inst('abscxp')], 'syl2anc', '( abs ` %s ) = ( k ^c ( Re ` %s ) )' % (TWT, NI))
    r1 = s([c.mem(IT, 'CC')], 'renegd', '( Re ` %s ) = -u ( Re ` %s )' % (NI, IT))
    r2 = s([ic, c.mem('T', 'CC')], 'mulcomd', '%s = ( T x. _i )' % IT)
    r3 = s([tr, ic], 'remul2d', '( Re ` ( T x. _i ) ) = ( T x. ( Re ` _i ) )')
    r4 = s([w.s([], 'rei', '( Re ` _i ) = 0')], 'a1i', '( Re ` _i ) = 0')
    r5 = s([r4], 'oveq2d', '( T x. ( Re ` _i ) ) = ( T x. 0 )')
    r6 = s([c.mem('T', 'CC')], 'mul01d', '( T x. 0 ) = 0')
    r7 = s([s([r2], 'fveq2d', '( Re ` %s ) = ( Re ` ( T x. _i ) )' % IT), r3], 'eqtrd', '( Re ` %s ) = ( T x. ( Re ` _i ) )' % IT)
    r8 = s([s([r7, r5], 'eqtrd', '( Re ` %s ) = ( T x. 0 )' % IT), r6], 'eqtrd', '( Re ` %s ) = 0' % IT)
    r9 = s([r8], 'negeqd', '-u ( Re ` %s ) = -u 0' % IT)
    r10 = s([s([r1, r9], 'eqtrd', '( Re ` %s ) = -u 0' % NI), s([w.s([], 'neg0', '-u 0 = 0')], 'a1i', '-u 0 = 0')], 'eqtrd', '( Re ` %s ) = 0' % NI)
    a2 = s([s([r10], 'oveq2d', '( k ^c ( Re ` %s ) ) = ( k ^c 0 )' % NI), s([c.mem('k', 'CC')], 'cxp0d', '( k ^c 0 ) = 1')], 'eqtrd', '( k ^c ( Re ` %s ) ) = 1' % NI)
    w.qed([tc, s([a1, a2], 'eqtrd', '( abs ` %s ) = 1' % TWT)], 'jca', S['cen2tw'])
    return run(w)


def gen_gc():
    w = W('cen2gc', 'The constant and the diagonal series at ` 1 + 3 D ` converge and are at most ` ( 5 / 4 ) / ( 3 D ) + 5 ` (Lean Census ` hsum0 ` , ` hsum3 ` , ` hbound0 ` , ` hbound3 ` ; ZC1 ~ vmsharp through CEN1 ~ cenvmb at ` U = 3 D ` ).')
    A0, C0 = split_imp(S['cen2gc'])
    A1 = '( %s /\\ k e. NN )' % A0
    s = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A0, f))
    a = lambda h, r, f: w.s(h, r, '( %s -> %s )' % (A1, f))
    L1 = lambda st: lift(w, st, A1)
    nx = s([], 'simpl', '( N e. NN /\\ X e. ( Base ` ( DChr ` N ) ) )')
    tr = s([], 'simprl', 'T e. RR'); dd = s([], 'simprr', DDH)
    drp = s([dd], 'simpld', 'D e. RR+'); dle = s([dd], 'simprd', 'D <_ %s' % F140)
    c0 = Closure(w, A0, {'D': ('RR+', drp), 'T': ('RR', tr)})
    U = '( 3 x. D )'; Q = '( 1 + %s )' % U
    urp = c0.mem(U, 'RR+')
    ule = linarith(w, A0, [dle], '%s <_ 1' % U, closure=c0)
    VB = split_imp(stmt('cenvmb'))[1].split()
    VB = ' '.join(U if t == 'U' else t for t in VB)
    vmb = s([urp, ule, w.inst('cenvmb')], 'syl2anc', VB)
    SA = 'sum_ k e. NN %s' % AW()
    sar = s([vmb], 'simpld', '%s e. RR' % SA)
    sab = s([s([sar], 'rered', '( Re ` %s ) = %s' % (SA, SA)), s([vmb], 'simprd', '( Re ` %s ) <_ %s' % (SA, BV))], 'eqbrtrrd', '%s <_ %s' % (SA, BV))
    qc = c0.mem(Q, 'CC')
    q1 = s([s([], '1red', '1 e. RR'), urp], 'ltaddrpd', '1 < %s' % Q)
    q1r = s([q1, s([c0.mem(Q, 'RR')], 'rered', '( Re ` %s ) = %s' % (Q, Q))], 'breqtrrd', '1 < ( Re ` %s )' % Q)
    cvh = s([qc, q1r], 'jca', '( %s e. CC /\\ 1 < ( Re ` %s ) )' % (Q, Q))
    one = s([], '1red', '1 e. RR')
    # ---- per k
    kn = a([], 'simpr', 'k e. NN')
    L = '( Lam ` k )'
    lr = a([kn, w.inst('vmacl')], 'syl', '%s e. RR' % L); l0 = a([kn, w.inst('vmage0')], 'syl', '0 <_ %s' % L)
    c1 = Closure(w, A1, {'k': ('NN', kn), 'D': ('RR+', L1(drp)), 'T': ('RR', L1(tr)), L: [('RR', lr), ('ge0', l0)]})
    lc = c1.mem(L, 'CC')
    le1 = a([a([a([lr, l0], 'absidd', '( abs ` %s ) = %s' % (L, L)), a([lr], 'leidd', '%s <_ %s' % (L, L))], 'eqbrtrd', '( abs ` %s ) <_ %s' % (L, L)),
             a([lc], 'mullidd', '( 1 x. %s ) = %s' % (L, L))], 'breqtrrd', '( abs ` %s ) <_ ( 1 x. %s )' % (L, L))
    cva = w.s([cvh, one, lc, le1], 'cencvg', '( %s -> seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~> )' % (A0, AW()))
    # the diagonal term
    CH = CHV('k'); TT = TW('T'); VV = VT('N', 'X', 'T')
    ch = a([L1(nx), a([kn], 'nnzd', 'k e. ZZ'), w.inst('cen2chv')], 'syl2anc', '( %s e. CC /\\ ( abs ` %s ) <_ 1 )' % (CH, CH))
    tw = a([kn, L1(tr), w.inst('cen2tw')], 'syl2anc', '( %s e. CC /\\ ( abs ` %s ) = 1 )' % (TT, TT))
    chc = a([ch], 'simpld', '%s e. CC' % CH); tc = a([tw], 'simpld', '%s e. CC' % TT)
    vc = a([chc, tc], 'mulcld', '%s e. CC' % VV)
    av = a([chc, tc], 'absmuld', '( abs ` %s ) = ( ( abs ` %s ) x. ( abs ` %s ) )' % (VV, CH, TT))
    av2 = a([av, a([a([tw], 'simprd', '( abs ` %s ) = 1' % TT)], 'oveq2d', '( ( abs ` %s ) x. ( abs ` %s ) ) = ( ( abs ` %s ) x. 1 )' % (CH, TT, CH))], 'eqtrd',
            '( abs ` %s ) = ( ( abs ` %s ) x. 1 )' % (VV, CH))
    av3 = a([av2, a([a([chc], 'abscld', '( abs ` %s ) e. RR' % CH)], 'recnd', '( abs ` %s ) e. CC' % CH)], 'mulridd', '( ( abs ` %s ) x. 1 ) = ( abs ` %s )' % (CH, CH)) if False else None
    av3 = a([av2, a([a([a([chc], 'abscld', '( abs ` %s ) e. RR' % CH)], 'recnd', '( abs ` %s ) e. CC' % CH)], 'mulridd', '( ( abs ` %s ) x. 1 ) = ( abs ` %s )' % (CH, CH))],
            'eqtrd', '( abs ` %s ) = ( abs ` %s )' % (VV, CH))
    avl = a([av3, a([ch], 'simprd', '( abs ` %s ) <_ 1' % CH)], 'eqbrtrd', '( abs ` %s ) <_ 1' % VV)
    X_ = '( abs ` %s )' % VV
    x0 = a([vc], 'absge0d', '0 <_ %s' % X_)
    c1.have(X_, 'RR', a([vc], 'abscld', '%s e. RR' % X_)); c1.have(X_, 'ge0', x0)
    SQV = SQ(VV)
    sq1 = nlinarith(w, A1, [avl, x0], '%s <_ 1' % SQV, closure=c1)
    c1.have(SQV, 'RR', c1.mem(SQV, 'RR')); c1.have(SQV, 'ge0', c1.ge0(SQV))
    B2 = '( %s x. %s )' % (L, SQV)
    b2r = c1.mem(B2, 'RR'); b20 = c1.ge0(B2)
    b2le = nlinarith(w, A1, [sq1, l0], '%s <_ ( 1 x. %s )' % (B2, L), closure=c1)
    le2 = a([a([b2r, b20], 'absidd', '( abs ` %s ) = %s' % (B2, B2)), b2le], 'eqbrtrd', '( abs ` %s ) <_ ( 1 x. %s )' % (B2, L))
    cv2 = w.s([cvh, one, c1.mem(B2, 'CC'), le2], 'cencvg', '( %s -> seq 1 ( + , ( k e. NN |-> ( %s x. ( k ^c -u %s ) ) ) ) e. dom ~~> )' % (A0, B2, Q))
    PW = '( k ^c -u %s )' % Q
    CT = '( %s x. %s )' % (AW(), SQV)
    meq = a([lc, c1.mem(SQV, 'CC'), c1.mem(PW, 'CC')], 'mul32d', '( %s x. %s ) = %s' % (B2, PW, CT))
    mp = s([meq], 'mpteq2dva', '( k e. NN |-> ( %s x. %s ) ) = ( k e. NN |-> %s )' % (B2, PW, CT))
    sq = s([mp], 'seqeq3d', 'seq 1 ( + , ( k e. NN |-> ( %s x. %s ) ) ) = seq 1 ( + , ( k e. NN |-> %s ) )' % (B2, PW, CT))
    cvc = s([sq, cv2], 'eqeltrrd', 'seq 1 ( + , ( k e. NN |-> %s ) ) e. dom ~~>' % CT)
    awr = c1.mem(AW(), 'RR'); aw0 = c1.ge0(AW()); c1.have(AW(), 'ge0', aw0)
    ctr = c1.mem(CT, 'RR')
    ctle = nlinarith(w, A1, [sq1, aw0], '%s <_ %s' % (CT, AW()), closure=c1, atoms=[AW(), SQV])
    SC = 'sum_ k e. NN %s' % CT
    scr, fc, cvcn = sumre(w, A0, CT, ctr, cvc)
    sar2, fa, cvan = sumre(w, A0, AW(), awr, cva)
    scle = sumle(w, A0, CT, ctr, fc, cvcn, AW(), awr, fa, cvan, ctle)
    scb = s([scr, sar, c0.mem(BV, 'RR'), scle, sab], 'letrd', '%s <_ %s' % (SC, BV))
    g1 = s([cva, s([sar, sab], 'jca', '( %s e. RR /\\ %s <_ %s )' % (SA, SA, BV))], 'jca', top_and(C0)[0])
    g2 = s([cvc, s([scr, scb], 'jca', '( %s e. RR /\\ %s <_ %s )' % (SC, SC, BV))], 'jca', top_and(C0)[1])
    w.qed([g1, g2], 'jca', S['cen2gc'])
    return run(w)


if __name__ == '__main__':
    gen_chv()
    gen_tw()
    gen_gc()
