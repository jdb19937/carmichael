"""Sortie EF3: segments (ef3sgri, ef3vseg, ef3hseg) and the vertical split (ef3vsp, Lean rectInt_vsplit)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ef3lib import *
from c8_o import numst
import lin
lin.FASTPATH = True

LIN = '( A + ( t x. ( B - A ) ) )'
S['ef3sgri'] = ('( ( ( A e. CC /\\ B e. CC ) /\\ X e. ( A cseg B ) ) -> ( X = ( ( Re ` X ) + ( _i x. ( Im ` X ) ) ) /\\ '
                '( Re ` X ) e. ( ( Re ` A ) cseg ( Re ` B ) ) /\\ ( Im ` X ) e. ( ( Im ` A ) cseg ( Im ` B ) ) ) )')
S['ef3vseg'] = ('( ( ( P e. RR /\\ ( L e. RR /\\ H e. RR ) ) /\\ ( ( E e. ( L [,] H ) /\\ K e. ( L [,] H ) ) /\\ '
                'A. t e. ( L [,] H ) ( P + ( _i x. t ) ) e. D ) ) -> ( ( P + ( _i x. E ) ) cseg ( P + ( _i x. K ) ) ) C_ D )')
S['ef3hseg'] = ('( ( ( M e. RR /\\ ( P e. RR /\\ Q e. RR ) ) /\\ ( ( E e. ( P [,] Q ) /\\ K e. ( P [,] Q ) ) /\\ '
                'A. x e. ( P [,] Q ) ( x + ( _i x. M ) ) e. D ) ) -> ( ( E + ( _i x. M ) ) cseg ( K + ( _i x. M ) ) ) C_ D )')


def gen_sgri():
    w = W('ef3sgri', 'A point of a segment: its real and imaginary parts lie on the segments of the real and imaginary parts.')
    A0, G = ante_of(S['ef3sgri'])
    s = St(w, A0)
    ac = s([], 'simpll', 'A e. CC'); bc = s([], 'simplr', 'B e. CC'); xin = s([], 'simpr', 'X e. ( A cseg B )')
    xc = s([s([ac, bc], 'csegcl', '( A cseg B ) C_ CC') if False else s([ac, bc, w.inst('csegcl')], 'syl2anc', '( A cseg B ) C_ CC'), xin], 'sseldd', 'X e. CC')
    rep = s([xc, w.inst('replim')], 'syl', 'X = ( ( Re ` X ) + ( _i x. ( Im ` X ) ) )')
    EX = 'E. t e. ( 0 [,] 1 ) X = %s' % LIN
    ex = s([xin, s([ac, bc, w.inst('csegel')], 'syl2anc', '( X e. ( A cseg B ) <-> %s )' % EX)], 'mpbid', EX)
    A1 = '( %s /\\ t e. ( 0 [,] 1 ) )' % A0
    A2 = '( %s /\\ X = %s )' % (A1, LIN)
    s2 = St(w, A2)
    t01 = lift(w, w.s([], 'simpr', '( %s -> t e. ( 0 [,] 1 ) )' % A1), A2)
    tr = s2([t01, w.inst('elunitrn')], 'syl', 't e. RR')
    eqx = s2([], 'simpr', 'X = %s' % LIN)
    a2, b2 = lift(w, ac, A2), lift(w, bc, A2)
    parts = []
    for p, lem in (('Re', 'cseglinre'), ('Im', 'cseglinim')):
        f1 = s2([eqx], 'fveq2d', '( %s ` X ) = ( %s ` %s )' % (p, p, LIN))
        V = '( ( %s ` A ) + ( t x. ( ( %s ` B ) - ( %s ` A ) ) ) )' % (p, p, p)
        f2 = s2([a2, b2, tr, w.inst(lem)], 'syl3anc', '( %s ` %s ) = %s' % (p, LIN, V))
        pa = s2([s2([a2], 'recld' if p == 'Re' else 'imcld', '( %s ` A ) e. RR' % p)], 'recnd', '( %s ` A ) e. CC' % p)
        pb = s2([s2([b2], 'recld' if p == 'Re' else 'imcld', '( %s ` B ) e. RR' % p)], 'recnd', '( %s ` B ) e. CC' % p)
        f3 = s2([pa, pb, t01, w.inst('cseglin')], 'syl3anc', '%s e. ( ( %s ` A ) cseg ( %s ` B ) )' % (V, p, p))
        parts.append(s2([s2([f1, f2], 'eqtrd', '( %s ` X ) = %s' % (p, V)), f3], 'eqeltrd', '( %s ` X ) e. ( ( %s ` A ) cseg ( %s ` B ) )' % (p, p, p)))
    RI = '( ( Re ` X ) e. ( ( Re ` A ) cseg ( Re ` B ) ) /\\ ( Im ` X ) e. ( ( Im ` A ) cseg ( Im ` B ) ) )'
    j = s2(parts, 'jca', RI)
    e1 = w.s([j], 'ex', '( %s -> ( X = %s -> %s ) )' % (A1, LIN, RI))
    rl = s([e1], 'rexlimdva', '( %s -> %s )' % (EX, RI))
    ri = s([ex, rl], 'mpd', RI)
    w.qed([rep, s([ri, w.inst('simpl')], 'syl', '( Re ` X ) e. ( ( Re ` A ) cseg ( Re ` B ) )'),
           s([ri, w.inst('simpr')], 'syl', '( Im ` X ) e. ( ( Im ` A ) cseg ( Im ` B ) )')], '3jca', S['ef3sgri'])
    return run8(w)


def gen_seg(lab):
    """vertical (ef3vseg: Re fixed P, Im in [L,H]) or horizontal (ef3hseg: Im fixed M, Re in [P,Q])"""
    vert = lab == 'ef3vseg'
    w = W(lab, 'A %s segment between two points of a %s line lying in ` D ` lies in ` D ` .' % (('vertical', 'vertical') if vert else ('horizontal', 'horizontal')))
    A0, G = ante_of(S[lab])
    s = St(w, A0)
    if vert:
        c0, lo, hi, v = 'P', 'L', 'H', 't'
        pt = lambda y: '( P + ( _i x. %s ) )' % y
        fx, mv = 'Re', 'Im'
    else:
        c0, lo, hi, v = 'M', 'P', 'Q', 'x'
        pt = lambda y: '( %s + ( _i x. M ) )' % y
        fx, mv = 'Im', 'Re'
    I = '( %s [,] %s )' % (lo, hi)
    c0r = s([], 'simpll', '%s e. RR' % c0)
    lor = s([], 'simplrl' if True else '', '%s e. RR' % lo) if False else None
    lh = s([], 'simplr', '( %s e. RR /\\ %s e. RR )' % (lo, hi))
    lor = s([lh, w.inst('simpl')], 'syl', '%s e. RR' % lo); hir = s([lh, w.inst('simpr')], 'syl', '%s e. RR' % hi)
    ek = s([], 'simprl', '( E e. %s /\\ K e. %s )' % (I, I))
    ei = s([ek, w.inst('simpl')], 'syl', 'E e. %s' % I); ki = s([ek, w.inst('simpr')], 'syl', 'K e. %s' % I)
    AL = 'A. %s e. %s %s e. D' % (v, I, pt(v))
    al = s([], 'simprr', AL)
    iccr = s([lor, hir], 'iccssred', '%s C_ RR' % I)
    er = s([iccr, ei], 'sseldd', 'E e. RR'); kr = s([iccr, ki], 'sseldd', 'K e. RR')
    ptc = lambda y, yr: s([s([c0r], 'recnd', '%s e. CC' % c0), s([s([], 'ax-icn', '_i e. CC') if False else s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([yr], 'recnd', '%s e. CC' % y)], 'mulcld', '( _i x. %s ) e. CC' % y)], 'addcld', '%s e. CC' % pt(y)) if vert else \
        s([s([yr], 'recnd', '%s e. CC' % y), s([s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC'), s([c0r], 'recnd', 'M e. CC')], 'mulcld', '( _i x. M ) e. CC')], 'addcld', '%s e. CC' % pt(y))
    ec, kc = ptc('E', er), ptc('K', kr)
    SEG = '( %s cseg %s )' % (pt('E'), pt('K'))
    A1 = '( %s /\\ y e. %s )' % (A0, SEG)
    s1 = St(w, A1)
    L = lambda st: lift(w, st, A1)
    xin = s1([], 'simpr', 'y e. %s' % SEG)
    SG = S['ef3sgri']
    RIf = tsub(ante_of(SG)[1], {'A': pt('E'), 'B': pt('K'), 'X': 'y'})
    ri = s1([L(ec), L(kc), xin, w.inst('ef3sgri')], 'syl21anc', RIf) if False else \
        s1([s1([s1([L(ec), L(kc)], 'jca', '( %s e. CC /\\ %s e. CC )' % (pt('E'), pt('K'))), xin], 'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ y e. %s )' % (pt('E'), pt('K'), SEG)), w.inst('ef3sgri')], 'syl', RIf)
    rep = s1([ri, w.inst('simp1')], 'syl', 'y = ( ( Re ` y ) + ( _i x. ( Im ` y ) ) )')
    fxin = s1([ri, w.inst('simp2' if fx == 'Re' else 'simp3')], 'syl', '( %s ` y ) e. ( ( %s ` %s ) cseg ( %s ` %s ) )' % (fx, fx, pt('E'), fx, pt('K')))
    mvin = s1([ri, w.inst('simp3' if fx == 'Re' else 'simp2')], 'syl', '( %s ` y ) e. ( ( %s ` %s ) cseg ( %s ` %s ) )' % (mv, mv, pt('E'), mv, pt('K')))
    # the parts of the end points
    def parts(y, yr):
        if vert:
            re_ = s1([L(c0r), L(yr)], 'crred', '( Re ` %s ) = P' % pt(y)); im_ = s1([L(c0r), L(yr)], 'crimd', '( Im ` %s ) = %s' % (pt(y), y))
        else:
            re_ = s1([L(yr), L(c0r)], 'crred', '( Re ` %s ) = %s' % (pt(y), y)); im_ = s1([L(yr), L(c0r)], 'crimd', '( Im ` %s ) = M' % pt(y))
        return re_, im_
    reE, imE = parts('E', er); reK, imK = parts('K', kr)
    fE, mE = (reE, imE) if vert else (imE, reE)
    fK, mK = (reK, imK) if vert else (imK, reK)
    # fixed part: ( fx y ) e. ( c0 cseg c0 ) C_ ( c0 [,] c0 )
    fx1 = s1([fxin, s1([fE, fK], 'oveq12d', '( ( %s ` %s ) cseg ( %s ` %s ) ) = ( %s cseg %s )' % (fx, pt('E'), fx, pt('K'), c0, c0))], 'eleqtrd', '( %s ` y ) e. ( %s cseg %s )' % (fx, c0, c0))
    cc0 = s1([L(c0r), w.inst('iccid')], 'syl', '( %s [,] %s ) = { %s }' % (c0, c0, c0)) if False else None
    c0i = s1([L(c0r), s1([L(c0r)], 'leidd', '%s <_ %s' % (c0, c0))], 'jca', '( %s e. RR /\\ %s <_ %s )' % (c0, c0, c0)) if False else None
    ci = s1([s1([L(c0r), L(c0r)], 'jca', '( %s e. RR /\\ %s e. RR )' % (c0, c0)), s1([s1([L(c0r), L(c0r), s1([L(c0r)], 'leidd', '%s <_ %s' % (c0, c0))], 'lbicc2d', '%s e. ( %s [,] %s )' % (c0, c0, c0)) if False else
                                                                            s1([s1([L(c0r)], 'rexrd', '%s e. RR*' % c0), s1([L(c0r)], 'rexrd', '%s e. RR*' % c0), s1([L(c0r)], 'leidd', '%s <_ %s' % (c0, c0)), w.inst('lbicc2')], 'syl3anc', '%s e. ( %s [,] %s )' % (c0, c0, c0)),
                                                                            s1([s1([L(c0r)], 'rexrd', '%s e. RR*' % c0), s1([L(c0r)], 'rexrd', '%s e. RR*' % c0), s1([L(c0r)], 'leidd', '%s <_ %s' % (c0, c0)), w.inst('lbicc2')], 'syl3anc', '%s e. ( %s [,] %s )' % (c0, c0, c0))],
                                                                           'jca', '( %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) )' % (c0, c0, c0, c0, c0, c0))],
            'jca', '( ( %s e. RR /\\ %s e. RR ) /\\ ( %s e. ( %s [,] %s ) /\\ %s e. ( %s [,] %s ) ) )' % (c0, c0, c0, c0, c0, c0, c0, c0))
    cs = s1([ci, w.inst('csegicc')], 'syl', '( %s cseg %s ) C_ ( %s [,] %s )' % (c0, c0, c0, c0))
    fx2 = s1([cs, fx1], 'sseldd', '( %s ` y ) e. ( %s [,] %s )' % (fx, c0, c0))
    xc = s1([s1([s1([L(ec), L(kc), w.inst('csegcl')], 'syl2anc', '%s C_ CC' % SEG), xin], 'sseldd', 'y e. CC')], 'id', 'y e. CC') if False else \
        s1([s1([L(ec), L(kc), w.inst('csegcl')], 'syl2anc', '%s C_ CC' % SEG), xin], 'sseldd', 'y e. CC')
    fxr = s1([xc], 'recld' if fx == 'Re' else 'imcld', '( %s ` y ) e. RR' % fx)
    e3 = s1([L(c0r), L(c0r), w.inst('elicc2')], 'syl2anc', '( ( %s ` y ) e. ( %s [,] %s ) <-> ( ( %s ` y ) e. RR /\\ %s <_ ( %s ` y ) /\\ ( %s ` y ) <_ %s ) )' % (fx, c0, c0, fx, c0, fx, fx, c0))
    tri = s1([fx2, e3], 'mpbid', '( ( %s ` y ) e. RR /\\ %s <_ ( %s ` y ) /\\ ( %s ` y ) <_ %s )' % (fx, c0, fx, fx, c0))
    fxeq = s1([L(c0r), fxr, s1([tri, w.inst('simp3')], 'syl', '( %s ` y ) <_ %s' % (fx, c0)), s1([tri, w.inst('simp2')], 'syl', '%s <_ ( %s ` y )' % (c0, fx))], 'letri3d', '( %s ` y ) = %s' % (fx, c0)) if False else \
        s1([s1([tri, w.inst('simp3')], 'syl', '( %s ` y ) <_ %s' % (fx, c0)), s1([tri, w.inst('simp2')], 'syl', '%s <_ ( %s ` y )' % (c0, fx)), s1([fxr, L(c0r), w.inst('letri3')], 'syl2anc', '( ( %s ` y ) = %s <-> ( ( %s ` y ) <_ %s /\\ %s <_ ( %s ` y ) ) )' % (fx, c0, fx, c0, c0, fx))], 'mpbir2and', '( %s ` y ) = %s' % (fx, c0))
    # moving part in I
    mv1 = s1([mvin, s1([mE, mK], 'oveq12d', '( ( %s ` %s ) cseg ( %s ` %s ) ) = ( E cseg K )' % (mv, pt('E'), mv, pt('K')))], 'eleqtrd', '( %s ` y ) e. ( E cseg K )' % mv)
    ekc = s1([s1([L(lor), L(hir)], 'jca', '( %s e. RR /\\ %s e. RR )' % (lo, hi)), s1([L(ei), L(ki)], 'jca', '( E e. %s /\\ K e. %s )' % (I, I))], 'jca', '( ( %s e. RR /\\ %s e. RR ) /\\ ( E e. %s /\\ K e. %s ) )' % (lo, hi, I, I))
    mv2 = s1([s1([ekc, w.inst('csegicc')], 'syl', '( E cseg K ) C_ %s' % I), mv1], 'sseldd', '( %s ` y ) e. %s' % (mv, I))
    # y = pt ( mv y ) e. D
    MX = '( %s ` y )' % mv
    body = '%s e. D' % pt(v)
    eqv = w.wcongr(body, {v: MX}, '%s = %s' % (v, MX), {v: w.s([], 'id', '( %s = %s -> %s = %s )' % (v, MX, v, MX))})[0]
    pin = s1([eqv, L(al), mv2], 'rspcdva', '%s e. D' % pt(MX))
    if vert:
        xe = s1([rep, s1([fxeq], 'oveq1d', '( ( Re ` y ) + ( _i x. ( Im ` y ) ) ) = ( P + ( _i x. ( Im ` y ) ) )')], 'eqtrd', 'y = %s' % pt(MX))
    else:
        xe = s1([rep, s1([s1([fxeq], 'oveq2d', '( _i x. ( Im ` y ) ) = ( _i x. M )')], 'oveq2d', '( ( Re ` y ) + ( _i x. ( Im ` y ) ) ) = ( ( Re ` y ) + ( _i x. M ) )')], 'eqtrd', 'y = %s' % pt(MX))
    xd = s1([xe, pin], 'eqeltrd', 'y e. D')
    w.qed([w.s([xd], 'ex', '( %s -> ( y e. %s -> y e. D ) )' % (A0, SEG))], 'ssrdv', S[lab])
    return run8(w)


def icc_mem(w, A0, x, lo, hi, xr, lor, hir, l1, l2):
    """( A0 -> x e. ( lo [,] hi ) ) from closures and the two bounds"""
    s = St(w, A0)
    e = s([lor, hir, w.inst('elicc2')], 'syl2anc', '( %s e. ( %s [,] %s ) <-> ( %s e. RR /\\ %s <_ %s /\\ %s <_ %s ) )' % (x, lo, hi, x, lo, x, x, hi))
    return s([s([xr, l1, l2], '3jca', '( %s e. RR /\\ %s <_ %s /\\ %s <_ %s )' % (x, lo, x, x, hi)), e], 'mpbird', '%s e. ( %s [,] %s )' % (x, lo, hi))


def gen_vsp():
    w = W('ef3vsp', 'Lean ` rectInt_vsplit ` : the boundary integral of a rectangle is the sum over the two rectangles cut at height ` M ` , for ` F ` continuous on a set containing the frame and the cut line (the rectangle itself need not lie in ` D ` ).')
    A0, G = ante_of(S['ef3vsp'])
    s = St(w, A0)
    H1, H2, H3 = top_and(A0)
    h1 = s([], 'simp1', H1); h2 = s([], 'simp2', H2); h3 = s([], 'simp3', H3)
    fc = s([h1, w.inst('simpl')], 'syl', 'F e. ( D -cn-> CC )')
    pq = s([h1, w.inst('simpr')], 'syl', '( ( P e. RR /\\ Q e. RR ) /\\ P <_ Q )')
    pr = s([s([pq, w.inst('simpl')], 'syl', '( P e. RR /\\ Q e. RR )'), w.inst('simpl')], 'syl', 'P e. RR')
    qr = s([s([pq, w.inst('simpl')], 'syl', '( P e. RR /\\ Q e. RR )'), w.inst('simpr')], 'syl', 'Q e. RR')
    ple = s([pq, w.inst('simpr')], 'syl', 'P <_ Q')
    r3 = s([h2, w.inst('simpl')], 'syl', '( L e. RR /\\ H e. RR /\\ M e. RR )')
    o3 = s([h2, w.inst('simpr')], 'syl', '( L <_ M /\\ M <_ H /\\ L < H )')
    lr = s([r3, w.inst('simp1')], 'syl', 'L e. RR'); hr = s([r3, w.inst('simp2')], 'syl', 'H e. RR'); mr = s([r3, w.inst('simp3')], 'syl', 'M e. RR')
    lm = s([o3, w.inst('simp1')], 'syl', 'L <_ M'); mh = s([o3, w.inst('simp2')], 'syl', 'M <_ H'); lh = s([o3, w.inst('simp3')], 'syl', 'L < H')
    lv = {'P': pr, 'Q': qr, 'L': lr, 'H': hr, 'M': mr}
    lhl = lin8(w, A0, [lh], 'L <_ H', lv)
    li = icc_mem(w, A0, 'L', 'L', 'H', lr, lr, hr, lin8(w, A0, [], 'L <_ L', lv), lhl)
    hi = icc_mem(w, A0, 'H', 'L', 'H', hr, lr, hr, lhl, lin8(w, A0, [], 'H <_ H', lv))
    mi = icc_mem(w, A0, 'M', 'L', 'H', mr, lr, hr, lm, mh)
    pi_ = icc_mem(w, A0, 'P', 'P', 'Q', pr, pr, qr, lin8(w, A0, [], 'P <_ P', lv), ple)
    qi = icc_mem(w, A0, 'Q', 'P', 'Q', qr, pr, qr, ple, lin8(w, A0, [], 'Q <_ Q', lv))
    IV = '( L [,] H )'; IH = '( P [,] Q )'
    V1, V2 = top_and(H3)
    v1 = s([h3, w.inst('simpl')], 'syl', V1); v2 = s([h3, w.inst('simpr')], 'syl', V2)
    pt = lambda x, y: '( %s + ( _i x. %s ) )' % (x, y)
    r26 = w.s([], 'r19.26', '( %s <-> ( A. t e. %s %s e. D /\\ A. t e. %s %s e. D ) )' % (V1, IV, pt('P', 't'), IV, pt('Q', 't')))
    vv = s([v1, r26], 'sylib', '( A. t e. %s %s e. D /\\ A. t e. %s %s e. D )' % (IV, pt('P', 't'), IV, pt('Q', 't')))
    alP = s([vv, w.inst('simpl')], 'syl', 'A. t e. %s %s e. D' % (IV, pt('P', 't')))
    alQ = s([vv, w.inst('simpr')], 'syl', 'A. t e. %s %s e. D' % (IV, pt('Q', 't')))
    r263 = w.s([], 'r19.26-3', '( %s <-> ( A. x e. %s %s e. D /\\ A. x e. %s %s e. D /\\ A. x e. %s %s e. D ) )' % (V2, IH, pt('x', 'L'), IH, pt('x', 'M'), IH, pt('x', 'H')))
    hh = s([v2, r263], 'sylib', '( A. x e. %s %s e. D /\\ A. x e. %s %s e. D /\\ A. x e. %s %s e. D )' % (IH, pt('x', 'L'), IH, pt('x', 'M'), IH, pt('x', 'H')))
    alx = {y: s([hh, w.inst(k)], 'syl', 'A. x e. %s %s e. D' % (IH, pt('x', y))) for y, k in (('L', 'simp1'), ('M', 'simp2'), ('H', 'simp3'))}
    ins = {'L': li, 'H': hi, 'M': mi, 'P': pi_, 'Q': qi}

    def vseg(c, cr, al, e, k):
        f = '( ( %s cseg %s ) C_ D )' % (pt(c, e), pt(c, k))
        a = '( ( %s e. RR /\\ ( L e. RR /\\ H e. RR ) ) /\\ ( ( %s e. %s /\\ %s e. %s ) /\\ A. t e. %s %s e. D ) )' % (c, e, IV, k, IV, IV, pt(c, 't'))
        hy = s([s([cr, s([lr, hr], 'jca', '( L e. RR /\\ H e. RR )')], 'jca', '( %s e. RR /\\ ( L e. RR /\\ H e. RR ) )' % c),
                s([s([ins[e], ins[k]], 'jca', '( %s e. %s /\\ %s e. %s )' % (e, IV, k, IV)), al], 'jca', '( ( %s e. %s /\\ %s e. %s ) /\\ A. t e. %s %s e. D )' % (e, IV, k, IV, IV, pt(c, 't')))], 'jca', a)
        return s([hy, w.inst('ef3vseg')], 'syl', '( %s cseg %s ) C_ D' % (pt(c, e), pt(c, k)))

    def hseg(m, e, k):
        a = '( ( %s e. RR /\\ ( P e. RR /\\ Q e. RR ) ) /\\ ( ( %s e. %s /\\ %s e. %s ) /\\ A. x e. %s %s e. D ) )' % (m, e, IH, k, IH, IH, pt('x', m))
        hy = s([s([lv[m], s([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )')], 'jca', '( %s e. RR /\\ ( P e. RR /\\ Q e. RR ) )' % m),
                s([s([ins[e], ins[k]], 'jca', '( %s e. %s /\\ %s e. %s )' % (e, IH, k, IH)), alx[m]], 'jca', '( ( %s e. %s /\\ %s e. %s ) /\\ A. x e. %s %s e. D )' % (e, IH, k, IH, IH, pt('x', m)))], 'jca', a)
        return s([hy, w.inst('ef3hseg')], 'syl', '( %s cseg %s ) C_ D' % (pt(e, m), pt(k, m)))

    ic = s([w.s([], 'ax-icn', '_i e. CC')], 'a1i', '_i e. CC')
    cc = {}
    for x in ('P', 'Q'):
        for y in ('L', 'H', 'M'):
            cc[(x, y)] = s([s([lv[x]], 'recnd', '%s e. CC' % x), s([ic, s([lv[y]], 'recnd', '%s e. CC' % y)], 'mulcld', '( _i x. %s ) e. CC' % y)], 'addcld', '%s e. CC' % pt(x, y))
    LI = lambda a, b: '( F lint <. %s , %s >. )' % (a, b)

    def lcl(a, b, seg):
        (xa, ya), (xb, yb) = a, b
        return s([s([s([cc[a], cc[b]], 'jca', '( %s e. CC /\\ %s e. CC )' % (pt(xa, ya), pt(xb, yb))), s([fc, seg], 'jca', '( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (pt(xa, ya), pt(xb, yb)))],
                    'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (pt(xa, ya), pt(xb, yb), pt(xa, ya), pt(xb, yb))), w.inst('lintcl')], 'syl',
                 '%s e. CC' % LI(pt(xa, ya), pt(xb, yb)))
    segs = {}
    segs[('P', 'H', 'P', 'L')] = vseg('P', pr, alP, 'H', 'L'); segs[('P', 'H', 'P', 'M')] = vseg('P', pr, alP, 'H', 'M'); segs[('P', 'M', 'P', 'L')] = vseg('P', pr, alP, 'M', 'L')
    segs[('Q', 'L', 'Q', 'H')] = vseg('Q', qr, alQ, 'L', 'H'); segs[('Q', 'L', 'Q', 'M')] = vseg('Q', qr, alQ, 'L', 'M'); segs[('Q', 'M', 'Q', 'H')] = vseg('Q', qr, alQ, 'M', 'H')
    segs[('P', 'L', 'Q', 'L')] = hseg('L', 'P', 'Q'); segs[('P', 'M', 'Q', 'M')] = hseg('M', 'P', 'Q'); segs[('Q', 'H', 'P', 'H')] = hseg('H', 'Q', 'P')
    lints = {k: lcl((k[0], k[1]), (k[2], k[3]), v) for k, v in segs.items()}
    b, rB, t, lB = LI(pt('P', 'L'), pt('Q', 'L')), LI(pt('Q', 'L'), pt('Q', 'H')), LI(pt('Q', 'H'), pt('P', 'H')), LI(pt('P', 'H'), pt('P', 'L'))
    r1, r2 = LI(pt('Q', 'L'), pt('Q', 'M')), LI(pt('Q', 'M'), pt('Q', 'H'))
    l2, l1 = LI(pt('P', 'H'), pt('P', 'M')), LI(pt('P', 'M'), pt('P', 'L'))
    m_, mp = LI(pt('Q', 'M'), pt('P', 'M')), LI(pt('P', 'M'), pt('Q', 'M'))
    fv = s([fc], 'elexd', 'F e. _V')
    def rco(a, bb, lo, hi):
        f = '( F rectint <. %s , %s >. ) = ( ( %s + %s ) + ( %s + %s ) )' % (pt(a, lo), pt(bb, hi), LI(pt(a, lo), pt(bb, lo)), LI(pt(bb, lo), pt(bb, hi)), LI(pt(bb, hi), pt(a, hi)), LI(pt(a, hi), pt(a, lo)))
        return s([fv, s([pr, qr], 'jca', '( P e. RR /\\ Q e. RR )'), s([lv[lo], lv[hi]], 'jca', '( %s e. RR /\\ %s e. RR )' % (lo, hi)), w.inst('rectintco')], 'syl3anc', f)
    ebig = rco('P', 'Q', 'L', 'H'); elow = rco('P', 'Q', 'L', 'M'); eup = rco('P', 'Q', 'M', 'H')
    # split points
    X = '( ( M - L ) / ( H - L ) )'; X2 = '( ( H - M ) / ( H - L ) )'
    hlp = s([s([hr, lr], 'resubcld', '( H - L ) e. RR'), lin8(w, A0, [lh], '0 < ( H - L )', lv)], 'elrpd', '( H - L ) e. RR+')
    def unit(num, n0, nle):
        nr = s([lv[num[1]] if False else s([lv[num[0]], lv[num[1]]], 'resubcld', '( %s - %s ) e. RR' % num)], 'id', '( %s - %s ) e. RR' % num) if False else s([lv[num[0]], lv[num[1]]], 'resubcld', '( %s - %s ) e. RR' % num)
        Xn = '( ( %s - %s ) / ( H - L ) )' % num
        g0 = s([nr, hlp, n0], 'divge0d', '0 <_ %s' % Xn)
        g1 = s([nle, s([nr, hlp, w.inst('divle1le')], 'syl2anc', '( %s <_ 1 <-> ( %s - %s ) <_ ( H - L ) )' % (Xn, num[0], num[1]))], 'mpbird', '%s <_ 1' % Xn)
        xr = s([nr, hlp], 'rerpdivcld', '%s e. RR' % Xn)
        one = numst(w, A0, '1', 'RR'); zero = numst(w, A0, '0', 'RR')
        return icc_mem(w, A0, Xn, '0', '1', xr, zero, one, g0, g1), xr, nr
    lv2 = dict(lv)
    xu, xr, nr1 = unit(('M', 'L'), lin8(w, A0, [lm], '0 <_ ( M - L )', lv), lin8(w, A0, [mh], '( M - L ) <_ ( H - L )', lv))
    x2u, x2r, nr2 = unit(('H', 'M'), lin8(w, A0, [mh], '0 <_ ( H - M )', lv), lin8(w, A0, [lm], '( H - M ) <_ ( H - L )', lv))
    hlc = s([s([hlp], 'rpred', '( H - L ) e. RR')], 'recnd', '( H - L ) e. CC')
    hl0 = s([hlp], 'rpne0d', '( H - L ) =/= 0')
    c = Closure(w, A0, {'P': ('RR', pr), 'Q': ('RR', qr), 'L': ('RR', lr), 'H': ('RR', hr), 'M': ('RR', mr), X: ('RR', xr), X2: ('RR', x2r), '_i': ('CC', ic)})
    for k in ('P', 'Q', 'L', 'H', 'M', X, X2, '_i'):
        c.atom(k)
    # right: Q + i M = ( Q + i L ) + X ( ( Q + i H ) - ( Q + i L ) )
    RHS1 = '( %s + ( %s x. ( %s - %s ) ) )' % (pt('Q', 'L'), X, pt('Q', 'H'), pt('Q', 'L'))
    e1 = ringeq(w, A0, RHS1, pt('Q', '( L + ( %s x. ( H - L ) ) )' % X), c)
    dc1 = s([s([nr1], 'recnd', '( M - L ) e. CC'), hlc, hl0], 'divcan1d', '( %s x. ( H - L ) ) = ( M - L )' % X)
    e2 = s([s([s([dc1], 'oveq2d', '( L + ( %s x. ( H - L ) ) ) = ( L + ( M - L ) )' % X), s([s([lr], 'recnd', 'L e. CC'), s([mr], 'recnd', 'M e. CC')], 'pncan3d', '( L + ( M - L ) ) = M')], 'eqtrd', '( L + ( %s x. ( H - L ) ) ) = M' % X)], 'oveq2d',
           '( _i x. ( L + ( %s x. ( H - L ) ) ) ) = ( _i x. M )' % X)
    e3 = s([e2], 'oveq2d', '%s = %s' % (pt('Q', '( L + ( %s x. ( H - L ) ) )' % X), pt('Q', 'M')))
    cq = s([s([e1, e3], 'eqtrd', '%s = %s' % (RHS1, pt('Q', 'M')))], 'eqcomd', '%s = %s' % (pt('Q', 'M'), RHS1))
    def spl(a, bb, seg, u, cpt, ceq, f):
        (xa, ya), (xb, yb) = a, bb
        hy = s([s([cc[a], cc[bb]], 'jca', '( %s e. CC /\\ %s e. CC )' % (pt(xa, ya), pt(xb, yb))), s([fc, seg], 'jca', '( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (pt(xa, ya), pt(xb, yb)))],
               'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (pt(xa, ya), pt(xb, yb), pt(xa, ya), pt(xb, yb)))
        return s([hy, u, ceq, w.inst('lintsplit')], 'syl3anc', f)
    srB = spl(('Q', 'L'), ('Q', 'H'), segs[('Q', 'L', 'Q', 'H')], xu, pt('Q', 'M'), cq, '%s = ( %s + %s )' % (rB, r1, r2))
    # left: P + i M = ( P + i H ) + X2 ( ( P + i L ) - ( P + i H ) )
    RHS2 = '( %s + ( %s x. ( %s - %s ) ) )' % (pt('P', 'H'), X2, pt('P', 'L'), pt('P', 'H'))
    f1 = ringeq(w, A0, RHS2, pt('P', '( H - ( %s x. ( H - L ) ) )' % X2), c)
    dc2 = s([s([nr2], 'recnd', '( H - M ) e. CC'), hlc, hl0], 'divcan1d', '( %s x. ( H - L ) ) = ( H - M )' % X2)
    f2 = s([s([s([dc2], 'oveq2d', '( H - ( %s x. ( H - L ) ) ) = ( H - ( H - M ) )' % X2), s([s([hr], 'recnd', 'H e. CC'), s([mr], 'recnd', 'M e. CC')], 'nncand', '( H - ( H - M ) ) = M')], 'eqtrd', '( H - ( %s x. ( H - L ) ) ) = M' % X2)], 'oveq2d',
           '( _i x. ( H - ( %s x. ( H - L ) ) ) ) = ( _i x. M )' % X2)
    f3 = s([f2], 'oveq2d', '%s = %s' % (pt('P', '( H - ( %s x. ( H - L ) ) )' % X2), pt('P', 'M')))
    cp = s([s([f1, f3], 'eqtrd', '%s = %s' % (RHS2, pt('P', 'M')))], 'eqcomd', '%s = %s' % (pt('P', 'M'), RHS2))
    slB = spl(('P', 'H'), ('P', 'L'), segs[('P', 'H', 'P', 'L')], x2u, pt('P', 'M'), cp, '%s = ( %s + %s )' % (lB, l2, l1))
    # middle: lint < Q+iM , P+iM > = -u lint < P+iM , Q+iM >
    hym = s([s([cc[('P', 'M')], cc[('Q', 'M')]], 'jca', '( %s e. CC /\\ %s e. CC )' % (pt('P', 'M'), pt('Q', 'M'))), s([fc, segs[('P', 'M', 'Q', 'M')]], 'jca', '( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D )' % (pt('P', 'M'), pt('Q', 'M')))],
            'jca', '( ( %s e. CC /\\ %s e. CC ) /\\ ( F e. ( D -cn-> CC ) /\\ ( %s cseg %s ) C_ D ) )' % (pt('P', 'M'), pt('Q', 'M'), pt('P', 'M'), pt('Q', 'M')))
    srev = s([hym, w.inst('lintrev')], 'syl', '%s = -u %s' % (m_, mp))
    # algebra
    for k, st in lints.items():
        E = LI(pt(k[0], k[1]), pt(k[2], k[3]))
        c.leaf(E, 'CC', st)
    B0 = '( ( %s + %s ) + ( %s + %s ) )' % (b, rB, t, lB)
    B1 = '( ( %s + ( %s + %s ) ) + ( %s + ( %s + %s ) ) )' % (b, r1, r2, t, l2, l1)
    g1 = s([s([srB], 'oveq2d', '( %s + %s ) = ( %s + ( %s + %s ) )' % (b, rB, b, r1, r2)), s([slB], 'oveq2d', '( %s + %s ) = ( %s + ( %s + %s ) )' % (t, lB, t, l2, l1))], 'oveq12d', '%s = %s' % (B0, B1))
    LO1 = '( ( %s + %s ) + ( -u %s + %s ) )' % (b, r1, mp, l1)
    UP = '( ( %s + %s ) + ( %s + %s ) )' % (mp, r2, t, l2)
    g2 = ringeq(w, A0, B1, '( %s + %s )' % (LO1, UP), c)
    LO0 = '( ( %s + %s ) + ( %s + %s ) )' % (b, r1, m_, l1)
    g3 = s([s([srev], 'oveq1d', '( %s + %s ) = ( -u %s + %s )' % (m_, l1, mp, l1))], 'oveq2d', '%s = %s' % (LO0, LO1))
    RL = '( F rectint <. %s , %s >. )' % (pt('P', 'L'), pt('Q', 'M'))
    RU = '( F rectint <. %s , %s >. )' % (pt('P', 'M'), pt('Q', 'H'))
    g4 = s([s([elow, g3], 'eqtrd', '%s = %s' % (RL, LO1)), eup], 'oveq12d', '( %s + %s ) = ( %s + %s )' % (RL, RU, LO1, UP))
    RB = '( F rectint <. %s , %s >. )' % (pt('P', 'L'), pt('Q', 'H'))
    g5 = s([s([ebig, g1], 'eqtrd', '%s = %s' % (RB, B1)), g2], 'eqtrd', '%s = ( %s + %s )' % (RB, LO1, UP))
    w.qed([g5, g4], 'eqtr4d', S['ef3vsp'])
    return run8(w)


if __name__ == '__main__':
    gen_sgri()
    gen_seg('ef3vseg')
    gen_seg('ef3hseg')
    gen_vsp()
