"""Sortie A4a, batch 12: the scan for k (step 3)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

# ======================================================================= the cost algebra
if not only or 'scancb1' in only:
    w = W('scancb1', 'The scan cost bound when the scan stops at once.')
    T = '( ( C e. NN0 /\\ K e. NN0 /\\ B e. NN0 ) /\\ B <_ C )'
    cn = w.s([], 'simpl1', '( %s -> C e. NN0 )' % T)
    kn = w.s([], 'simpl2', '( %s -> K e. NN0 )' % T)
    bn = w.s([], 'simpl3', '( %s -> B e. NN0 )' % T)
    bc = w.s([], 'simpr', '( %s -> B <_ C )' % T)
    cr = w.s([cn], 'nn0red', '( %s -> C e. RR )' % T)
    kr = w.s([kn], 'nn0red', '( %s -> K e. RR )' % T)
    br = w.s([bn], 'nn0red', '( %s -> B e. RR )' % T)
    lin.nlinarith(w, T, [bc], 'B <_ ( ( ( K - K ) + 1 ) x. C )', leaves={'C': cr, 'K': kr, 'B': br}, name='qed')
    run(w)

if not only or 'scancb2' in only:
    w = W('scancb2', 'The scan cost bound accumulates one body per step.')
    T = ('( ( ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) /\\ ( A e. NN0 /\\ B e. NN0 ) ) /\\ '
         '( A <_ ( ( ( L - ( K + 1 ) ) + 1 ) x. C ) /\\ B <_ C ) )')
    cn = w.s([w.s([], 'simpll', '( %s -> ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) )' % T)], 'simp1d', '( %s -> C e. NN0 )' % T)
    kn = w.s([w.s([], 'simpll', '( %s -> ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) )' % T)], 'simp2d', '( %s -> K e. NN0 )' % T)
    ln = w.s([w.s([], 'simpll', '( %s -> ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) )' % T)], 'simp3d', '( %s -> L e. NN0 )' % T)
    an = w.s([], 'simplrl', '( %s -> A e. NN0 )' % T)
    bn = w.s([], 'simplrr', '( %s -> B e. NN0 )' % T)
    h1 = w.s([], 'simprl', '( %s -> A <_ ( ( ( L - ( K + 1 ) ) + 1 ) x. C ) )' % T)
    h2 = w.s([], 'simprr', '( %s -> B <_ C )' % T)
    cr = w.s([cn], 'nn0red', '( %s -> C e. RR )' % T)
    kr = w.s([kn], 'nn0red', '( %s -> K e. RR )' % T)
    lr = w.s([ln], 'nn0red', '( %s -> L e. RR )' % T)
    ar = w.s([an], 'nn0red', '( %s -> A e. RR )' % T)
    br = w.s([bn], 'nn0red', '( %s -> B e. RR )' % T)
    lin.nlinarith(w, T, [h1, h2], '( A + B ) <_ ( ( ( L - K ) + 1 ) x. C )',
                  leaves={'C': cr, 'K': kr, 'L': lr, 'A': ar, 'B': br}, name='qed')
    run(w)

if not only or 'scancb3' in only:
    w = W('scancb3', 'The scan cost bound accumulating a coprimality test and a pool construction.')
    T = ('( ( ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) /\\ ( A e. NN0 /\\ P e. NN0 /\\ Q e. NN0 ) ) /\\ '
         '( A <_ ( ( ( L - ( K + 1 ) ) + 1 ) x. C ) /\\ ( ( P + Q ) + 1 ) <_ C ) )')
    o1 = w.s([], 'simpll', '( %s -> ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) )' % T)
    o2 = w.s([], 'simplr', '( %s -> ( A e. NN0 /\\ P e. NN0 /\\ Q e. NN0 ) )' % T)
    cn = w.s([o1], 'simp1d', '( %s -> C e. NN0 )' % T)
    kn = w.s([o1], 'simp2d', '( %s -> K e. NN0 )' % T)
    ln = w.s([o1], 'simp3d', '( %s -> L e. NN0 )' % T)
    an = w.s([o2], 'simp1d', '( %s -> A e. NN0 )' % T)
    pn = w.s([o2], 'simp2d', '( %s -> P e. NN0 )' % T)
    qn = w.s([o2], 'simp3d', '( %s -> Q e. NN0 )' % T)
    h1 = w.s([], 'simprl', '( %s -> A <_ ( ( ( L - ( K + 1 ) ) + 1 ) x. C ) )' % T)
    h2 = w.s([], 'simprr', '( %s -> ( ( P + Q ) + 1 ) <_ C )' % T)
    lv = {'C': w.s([cn], 'nn0red', '( %s -> C e. RR )' % T), 'K': w.s([kn], 'nn0red', '( %s -> K e. RR )' % T),
          'L': w.s([ln], 'nn0red', '( %s -> L e. RR )' % T), 'A': w.s([an], 'nn0red', '( %s -> A e. RR )' % T),
          'P': w.s([pn], 'nn0red', '( %s -> P e. RR )' % T), 'Q': w.s([qn], 'nn0red', '( %s -> Q e. RR )' % T)}
    lin.nlinarith(w, T, [h1, h2], '( ( ( A + P ) + Q ) + 1 ) <_ ( ( ( L - K ) + 1 ) x. C )', leaves=lv, name='qed')
    run(w)

if not only or 'scancb4' in only:
    w = W('scancb4', 'The scan cost bound accumulating a coprimality test only.')
    T = ('( ( ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) /\\ ( A e. NN0 /\\ P e. NN0 ) ) /\\ '
         '( A <_ ( ( ( L - ( K + 1 ) ) + 1 ) x. C ) /\\ ( P + 1 ) <_ C ) )')
    o1 = w.s([], 'simpll', '( %s -> ( C e. NN0 /\\ K e. NN0 /\\ L e. NN0 ) )' % T)
    cn = w.s([o1], 'simp1d', '( %s -> C e. NN0 )' % T)
    kn = w.s([o1], 'simp2d', '( %s -> K e. NN0 )' % T)
    ln = w.s([o1], 'simp3d', '( %s -> L e. NN0 )' % T)
    an = w.s([], 'simplrl', '( %s -> A e. NN0 )' % T)
    pn = w.s([], 'simplrr', '( %s -> P e. NN0 )' % T)
    h1 = w.s([], 'simprl', '( %s -> A <_ ( ( ( L - ( K + 1 ) ) + 1 ) x. C ) )' % T)
    h2 = w.s([], 'simprr', '( %s -> ( P + 1 ) <_ C )' % T)
    lv = {'C': w.s([cn], 'nn0red', '( %s -> C e. RR )' % T), 'K': w.s([kn], 'nn0red', '( %s -> K e. RR )' % T),
          'L': w.s([ln], 'nn0red', '( %s -> L e. RR )' % T), 'A': w.s([an], 'nn0red', '( %s -> A e. RR )' % T),
          'P': w.s([pn], 'nn0red', '( %s -> P e. RR )' % T)}
    lin.nlinarith(w, T, [h1, h2], '( ( A + P ) + 1 ) <_ ( ( ( L - K ) + 1 ) x. C )', leaves=lv, name='qed')
    run(w)


CP = lambda k: '( 1st ` ( W CoprimeTo %s ) )' % k
CP2 = lambda k: '( 2nd ` ( W CoprimeTo %s ) )' % k
PAV = lambda k: '( ( ( W PoolAlg X ) ` Z ) ` %s )' % k
PA1 = lambda k: '( 1st ` %s )' % PAV(k)
PA2 = lambda k: '( 2nd ` %s )' % PAV(k)
SC = lambda k, f: '( ( ( ( ( W Scan X ) ` Z ) ` O ) ` %s ) ` %s )' % (k, f)
S1 = lambda k, f: '( 1st ` %s )' % SC(k, f)
S2 = lambda k, f: '( 2nd ` %s )' % SC(k, f)
KP = lambda k, f: '( 1st ` ( 2nd ` %s ) )' % S1(k, f)
PP = lambda k, f: '( 2nd ` ( 2nd ` %s ) )' % S1(k, f)
CB = '( ( ( # ` W ) + 2 ) + ( ( 2 ^ ( # ` W ) ) x. ( %s + 3 ) ) )' % SQ('X')
OPL = '( ( NN0 X. Word NN0 ) |_| 1o )'
WN = '( Word NN0 X. NN0 )'
B2 = '( 2o X. NN0 )'
OUT = ('( ( W e. Word NN0 /\\ X e. NN0 /\\ Z e. NN0 ) /\\ ( O e. NN0 /\\ J e. NN0 ) /\\ '
       '( %s = 1o /\\ O <_ ( # ` %s ) ) )' % (CP('J'), PA1('J')))
CONC = lambda k, f: ('( ( %s =/= %s /\\ ( %s <_ %s /\\ %s <_ J ) ) /\\ ( ( %s = 1o /\\ O <_ ( # ` %s ) ) /\\ '
                     '( %s = %s /\\ %s <_ ( ( ( %s - %s ) + 1 ) x. %s ) ) ) )'
                     % (S1(k, f), NONE, k, KP(k, f), KP(k, f), CP(KP(k, f)), PP(k, f), PP(k, f), PA1(KP(k, f)),
                        S2(k, f), KP(k, f), k, CB))
INN = lambda k, f: '( ( %s <_ J /\\ J < ( %s + %s ) ) -> %s )' % (k, k, f, CONC(k, f))
PHI = lambda f: '( %s -> A. k e. NN0 %s )' % (OUT, INN('k', f))

def sb(w, frm, to, f):
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
    st, new = w.wcongr(INN(frm, f), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
    assert new == INN(to, f), '\n%s\n%s' % (new, INN(to, f))
    return st

def outctx(w, A, sel='simp'):
    o1 = w.s([], sel + '1', '( %s -> ( W e. Word NN0 /\\ X e. NN0 /\\ Z e. NN0 ) )' % A)
    o2 = w.s([], sel + '2', '( %s -> ( O e. NN0 /\\ J e. NN0 ) )' % A)
    o3 = w.s([], sel + '3', '( %s -> ( %s = 1o /\\ O <_ ( # ` %s ) ) )' % (A, CP('J'), PA1('J')))
    ws = w.s([o1], 'simp1d', '( %s -> W e. Word NN0 )' % A)
    xn = w.s([o1], 'simp2d', '( %s -> X e. NN0 )' % A)
    zn = w.s([o1], 'simp3d', '( %s -> Z e. NN0 )' % A)
    on = w.s([o2], 'simpld', '( %s -> O e. NN0 )' % A)
    jn = w.s([o2], 'simprd', '( %s -> J e. NN0 )' % A)
    cj = w.s([o3], 'simpld', '( %s -> %s = 1o )' % (A, CP('J')))
    pj = w.s([o3], 'simprd', '( %s -> O <_ ( # ` %s ) )' % (A, PA1('J')))
    return ws, xn, zn, on, jn, cj, pj

def sccl(w, A, ws, xn, zn, on, kst, fst, k, f):
    return w.s([w.s([w.s([w.s([w.s([ws, xn], 'jca', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % A), zn], 'jca',
                          '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % A), on], 'jca',
                     '( %s -> ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % A), kst], 'jca',
                '( %s -> ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ %s e. NN0 ) )' % (A, k)), fst,
               w.inst('scancl')], 'syl2anc', '( %s -> %s e. ( %s X. NN0 ) )' % (A, SC(k, f), OPL))

def pacl(w, A, ws, xn, zn, kst, k):
    return w.s([w.s([w.s([w.s([ws, xn], 'jca', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % A), zn], 'jca',
                     '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % A), kst], 'jca',
                '( %s -> ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ %s e. NN0 ) )' % (A, k)), w.inst('poolalgcl')], 'syl',
               '( %s -> %s e. %s )' % (A, PAV(k), WN))

def cbcl(w, A, ws, xn):
    lenn = w.s([ws, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % A)
    pwn = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), lenn], 'nn0expcld', '( %s -> ( 2 ^ ( # ` W ) ) e. NN0 )' % A)
    sqn = w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A, SQ('X')))
    s3 = w.s([sqn, w.s([w.s([], '3nn0', '3 e. NN0')], 'a1i', '( %s -> 3 e. NN0 )' % A)], 'nn0addcld', '( %s -> ( %s + 3 ) e. NN0 )' % (A, SQ('X')))
    pr = w.s([pwn, s3], 'nn0mulcld', '( %s -> ( ( 2 ^ ( # ` W ) ) x. ( %s + 3 ) ) e. NN0 )' % (A, SQ('X')))
    l2 = w.s([lenn, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A)], 'nn0addcld', '( %s -> ( ( # ` W ) + 2 ) e. NN0 )' % A)
    return w.s([l2, pr], 'nn0addcld', '( %s -> %s e. NN0 )' % (A, CB)), lenn, pwn, sqn

def cbbnd(w, A, ws, xn, zn, kst, k, cbn):
    """( A -> ( ( CP2(k) + PA2(k) ) + 1 ) <_ CB ) and ( A -> ( CP2(k) + 1 ) <_ CB )"""
    ccl = w.s([ws, kst, w.inst('coprimetocl')], 'syl2anc', '( %s -> ( W CoprimeTo %s ) e. %s )' % (A, k, B2))
    c1, c2 = paircl(w, A, '( W CoprimeTo %s )' % k, ccl, '2o', 'NN0')
    cc = w.s([ws, kst, w.inst('coprimetocost')], 'syl2anc', '( %s -> %s <_ ( ( # ` W ) + 1 ) )' % (A, CP2(k)))
    pcl = pacl(w, A, ws, xn, zn, kst, k)
    p1, p2 = paircl(w, A, PAV(k), pcl, 'Word NN0', 'NN0')
    pc = w.s([w.s([w.s([ws, xn], 'jca', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % A),
                   w.s([zn, kst], 'jca', '( %s -> ( Z e. NN0 /\\ %s e. NN0 ) )' % (A, k))], 'jca',
                  '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ ( Z e. NN0 /\\ %s e. NN0 ) ) )' % (A, k)), w.inst('poolalgcost')], 'syl',
             '( %s -> %s <_ ( ( 2 ^ ( # ` W ) ) x. ( %s + 3 ) ) )' % (A, PA2(k), SQ('X')))
    lenn = w.s([ws, w.inst('lencl')], 'syl', '( %s -> ( # ` W ) e. NN0 )' % A)
    lenr = w.s([lenn], 'nn0red', '( %s -> ( # ` W ) e. RR )' % A)
    pwr = w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), lenn], 'nn0expcld',
                   '( %s -> ( 2 ^ ( # ` W ) ) e. NN0 )' % A)], 'nn0red', '( %s -> ( 2 ^ ( # ` W ) ) e. RR )' % A)
    sqr = w.s([w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A, SQ('X')))], 'nn0red', '( %s -> %s e. RR )' % (A, SQ('X')))
    c2r = w.s([c2], 'nn0red', '( %s -> %s e. RR )' % (A, CP2(k)))
    p2r = w.s([p2], 'nn0red', '( %s -> %s e. RR )' % (A, PA2(k)))
    p20 = w.s([p2], 'nn0ge0d', '( %s -> 0 <_ %s )' % (A, PA2(k)))
    lv = {'( # ` W )': lenr, '( 2 ^ ( # ` W ) )': pwr, SQ('X'): sqr, CP2(k): c2r, PA2(k): p2r}
    pw0 = w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), lenn], 'nn0expcld',
                   '( %s -> ( 2 ^ ( # ` W ) ) e. NN0 )' % A)], 'nn0ge0d', '( %s -> 0 <_ ( 2 ^ ( # ` W ) ) )' % A)
    sq0 = w.s([w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A, SQ('X')))], 'nn0ge0d', '( %s -> 0 <_ %s )' % (A, SQ('X')))
    b1 = lin.nlinarith(w, A, [cc, pc, pw0, sq0], '( ( %s + %s ) + 1 ) <_ %s' % (CP2(k), PA2(k), CB), leaves=lv)
    b2 = lin.nlinarith(w, A, [cc, p20, pw0, sq0], '( %s + 1 ) <_ %s' % (CP2(k), CB), leaves=lv)
    return b1, b2, c1, c2, p1, p2

# ======================================================================= base
if not only or 'scangob' in only:
    w = W('scangob', 'Base of the induction for the scan (Lean: scan_go, zero fuel).')
    B0 = '( %s /\\ k e. NN0 )' % OUT
    ws, xn, zn, on, jn, cj, pj = outctx(w, B0, 'simpl')
    kn = w.s([], 'simpr', '( %s -> k e. NN0 )' % B0)
    C = '( %s /\\ ( k <_ J /\\ J < ( k + 0 ) ) )' % B0
    kr = w.s([w.s([kn], 'adantr', '( %s -> k e. NN0 )' % C)], 'nn0red', '( %s -> k e. RR )' % C)
    jr = w.s([w.s([jn], 'adantr', '( %s -> J e. NN0 )' % C)], 'nn0red', '( %s -> J e. RR )' % C)
    bad = lin.linarith(w, C, [w.s([], 'simprl', '( %s -> k <_ J )' % C), w.s([], 'simprr', '( %s -> J < ( k + 0 ) )' % C)], 'J < J',
                       leaves={'k': kr, 'J': jr})
    con = w.s([bad, w.s([jr], 'ltnrd', '( %s -> -. J < J )' % C)], 'pm2.21dd', '( %s -> %s )' % (C, CONC('k', '0')))
    w.qed([w.s([con], 'ex', '( %s -> %s )' % (B0, INN('k', '0')))], 'ralrimiva', PHI('0'))
    run(w)

# ======================================================================= step
if not only or 'scangos' in only:
    w = W('scangos', 'Step of the induction for the scan (Lean: scan_go, one more unit of fuel).')
    IHD = 'A. k e. NN0 %s' % INN('k', 'F')
    IHC = 'A. c e. NN0 %s' % INN('c', 'F')
    A = '( F e. NN0 /\\ ( %s -> %s ) )' % (OUT, IHD)
    AC = '( F e. NN0 /\\ ( %s -> %s ) )' % (OUT, IHC)
    cbv = w.s([sb(w, 'k', 'c', 'F')], 'cbvralvw', '( %s <-> %s )' % (IHD, IHC))
    conv = w.s([w.s([], 'simpl', '( %s -> F e. NN0 )' % A),
                w.s([w.s([], 'simpr', '( %s -> ( %s -> %s ) )' % (A, OUT, IHD)),
                     w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd', '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))],
                    'syld', '( %s -> ( %s -> %s ) )' % (A, OUT, IHC))], 'jca', '( %s -> %s )' % (A, AC))
    B1 = '( %s /\\ %s )' % (AC, OUT)
    B = '( %s /\\ k e. NN0 )' % B1
    U = '( %s /\\ ( k <_ J /\\ J < ( k + ( F + 1 ) ) ) )' % B
    fn = w.s([], 'simp-4l', '( %s -> F e. NN0 )' % U)
    ihh = w.s([], 'simp-4r', '( %s -> ( %s -> %s ) )' % (U, OUT, IHC))
    out = w.s([], 'simpllr', '( %s -> %s )' % (U, OUT))
    kn = w.s([], 'simplr', '( %s -> k e. NN0 )' % U)
    kj = w.s([], 'simprl', '( %s -> k <_ J )' % U)
    jlt = w.s([], 'simprr', '( %s -> J < ( k + ( F + 1 ) ) )' % U)
    ihc = w.s([ihh, out], 'mpd', '( %s -> %s )' % (U, IHC))
    o1 = w.s([out], 'simp1d', '( %s -> ( W e. Word NN0 /\\ X e. NN0 /\\ Z e. NN0 ) )' % U)
    o2 = w.s([out], 'simp2d', '( %s -> ( O e. NN0 /\\ J e. NN0 ) )' % U)
    o3 = w.s([out], 'simp3d', '( %s -> ( %s = 1o /\\ O <_ ( # ` %s ) ) )' % (U, CP('J'), PA1('J')))
    ws = w.s([o1], 'simp1d', '( %s -> W e. Word NN0 )' % U)
    xn = w.s([o1], 'simp2d', '( %s -> X e. NN0 )' % U)
    zn = w.s([o1], 'simp3d', '( %s -> Z e. NN0 )' % U)
    on = w.s([o2], 'simpld', '( %s -> O e. NN0 )' % U)
    jn = w.s([o2], 'simprd', '( %s -> J e. NN0 )' % U)
    cj = w.s([o3], 'simpld', '( %s -> %s = 1o )' % (U, CP('J')))
    pj = w.s([o3], 'simprd', '( %s -> O <_ ( # ` %s ) )' % (U, PA1('J')))
    kr = w.s([kn], 'nn0red', '( %s -> k e. RR )' % U)
    jr = w.s([jn], 'nn0red', '( %s -> J e. RR )' % U)
    fr = w.s([fn], 'nn0red', '( %s -> F e. RR )' % U)
    k1n = w.s([kn, w.inst('peano2nn0')], 'syl', '( %s -> ( k + 1 ) e. NN0 )' % U)
    cbn, lenn, pwn, sqn = cbcl(w, U, ws, xn)
    T1 = '<. ( inl ` <. k , %s >. ) , ( ( %s + %s ) + 1 ) >.' % (PA1('k'), CP2('k'), PA2('k'))
    T2 = '<. %s , ( ( ( %s + %s ) + %s ) + 1 ) >.' % (S1('( k + 1 )', 'F'), S2('( k + 1 )', 'F'), CP2('k'), PA2('k'))
    T3 = '<. %s , ( ( %s + %s ) + 1 ) >.' % (S1('( k + 1 )', 'F'), S2('( k + 1 )', 'F'), CP2('k'))
    IF2 = 'if ( O <_ ( # ` %s ) , %s , %s )' % (PA1('k'), T1, T2)
    v1 = w.s([ws, xn], 'jca', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % U)
    v2 = w.s([v1, zn], 'jca', '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % U)
    v3 = w.s([v2, on], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % U)
    v4 = w.s([v3, kn], 'jca', '( %s -> ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ k e. NN0 ) )' % U)
    val = w.s([v4, fn], 'jca', '( %s -> ( ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ k e. NN0 ) /\\ F e. NN0 ) )' % U)
    valv = w.s([val, w.inst('scanp1')], 'syl', '( %s -> %s = if ( %s = 1o , %s , %s ) )' % (U, SC('k', '( F + 1 )'), CP('k'), IF2, T3))
    vt1, vf1 = ifproj(w, U, SC('k', '( F + 1 )'), valv, '%s = 1o' % CP('k'), IF2, T3)
    C1 = '( %s /\\ %s = 1o )' % (U, CP('k'))
    C3 = '( %s /\\ -. %s = 1o )' % (U, CP('k'))
    vt2, vf2 = ifproj(w, C1, SC('k', '( F + 1 )'), vt1, 'O <_ ( # ` %s )' % PA1('k'), T1, T2)
    C11 = '( %s /\\ O <_ ( # ` %s ) )' % (C1, PA1('k'))
    C12 = '( %s /\\ -. O <_ ( # ` %s ) )' % (C1, PA1('k'))
    PR = '<. k , %s >.' % PA1('k')
    INLPR = '( inl ` %s )' % PR
    CST1 = '( ( %s + %s ) + 1 )' % (CP2('k'), PA2('k'))
    CST2 = '( ( ( %s + %s ) + %s ) + 1 )' % (S2('( k + 1 )', 'F'), CP2('k'), PA2('k'))
    CST3 = '( ( %s + %s ) + 1 )' % (S2('( k + 1 )', 'F'), CP2('k'))
    def conj7(wa, ante, a, b, c, d, e, f, g):
        ab = wa.s([a, wa.s([b, c], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, BQ[1], BQ[2]))], 'jca',
                  '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (ante, BQ[0], BQ[1], BQ[2]))
        de = wa.s([d, e], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, BQ[3], BQ[4]))
        fg = wa.s([f, g], 'jca', '( %s -> ( %s /\\ %s ) )' % (ante, BQ[5], BQ[6]))
        return wa.s([ab, wa.s([de, fg], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (ante, BQ[3], BQ[4], BQ[5], BQ[6]))], 'jca',
                    '( %s -> %s )' % (ante, CONCK))
    # ------------------------------------------------- case 1: the scan stops here
    CA = C11
    BQ = ['%s =/= %s' % (S1('k', '( F + 1 )'), NONE), 'k <_ %s' % KP('k', '( F + 1 )'), '%s <_ J' % KP('k', '( F + 1 )'),
          '%s = 1o' % CP(KP('k', '( F + 1 )')), 'O <_ ( # ` %s )' % PP('k', '( F + 1 )'),
          '%s = %s' % (PP('k', '( F + 1 )'), PA1(KP('k', '( F + 1 )'))),
          '%s <_ ( ( ( %s - k ) + 1 ) x. %s )' % (S2('k', '( F + 1 )'), KP('k', '( F + 1 )'), CB)]
    CONCK = CONC('k', '( F + 1 )')
    kna = w.s([kn], 'ad2antrr', '( %s -> k e. NN0 )' % CA)
    jna = w.s([jn], 'ad2antrr', '( %s -> J e. NN0 )' % CA)
    ona = w.s([on], 'ad2antrr', '( %s -> O e. NN0 )' % CA)
    wsa = w.s([ws], 'ad2antrr', '( %s -> W e. Word NN0 )' % CA)
    xna = w.s([xn], 'ad2antrr', '( %s -> X e. NN0 )' % CA)
    zna = w.s([zn], 'ad2antrr', '( %s -> Z e. NN0 )' % CA)
    kja = w.s([kj], 'ad2antrr', '( %s -> k <_ J )' % CA)
    cka = w.s([], 'simplr', '( %s -> %s = 1o )' % (CA, CP('k')))
    pka = w.s([], 'simpr', '( %s -> O <_ ( # ` %s ) )' % (CA, PA1('k')))
    cbna = w.s([cbn], 'ad2antrr', '( %s -> %s e. NN0 )' % (CA, CB))
    pcla = pacl(w, CA, wsa, xna, zna, kna, 'k')
    pp1, pp2 = paircl(w, CA, PAV('k'), pcla, 'Word NN0', 'NN0')
    prcl = w.s([kna, pp1], 'opelxpd' if False else 'jca', '( %s -> ( k e. NN0 /\\ %s e. Word NN0 ) )' % (CA, PA1('k')))
    prel = w.s([kna, pp1, w.inst('opelxpi')], 'syl2anc', '( %s -> %s e. ( NN0 X. Word NN0 ) )' % (CA, PR))
    prex = w.s([prel], 'elexd', '( %s -> %s e. _V )' % (CA, PR))
    inlel = w.s([prel, w.inst('djulcl')], 'syl', '( %s -> %s e. %s )' % (CA, INLPR, OPL))
    b1, b2, cc1, cc2, ppa1, ppa2 = cbbnd(w, CA, wsa, xna, zna, kna, 'k', cbna)
    cstn = w.s([w.s([cc2, ppa2], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (CA, CP2('k'), PA2('k'))), w.inst('peano2nn0')], 'syl',
               '( %s -> %s e. NN0 )' % (CA, CST1))
    p1 = projeq(w, CA, SC('k', '( F + 1 )'), vt2, INLPR, CST1, w.s([inlel], 'elexd', '( %s -> %s e. _V )' % (CA, INLPR)),
                w.s([cstn], 'elexd', '( %s -> %s e. _V )' % (CA, CST1)), 1)
    p2 = projeq(w, CA, SC('k', '( F + 1 )'), vt2, INLPR, CST1, w.s([inlel], 'elexd', '( %s -> %s e. _V )' % (CA, INLPR)),
                w.s([cstn], 'elexd', '( %s -> %s e. _V )' % (CA, CST1)), 2)
    zex = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % CA)
    nen = w.s([prex, zex, w.inst('inlneinr')], 'syl2anc', '( %s -> %s =/= %s )' % (CA, INLPR, NONE))
    ne1 = w.s([p1, nen], 'eqnetrd', '( %s -> %s )' % (CA, BQ[0]))
    iv = w.s([prex, w.inst('inlval')], 'syl', '( %s -> %s = <. (/) , %s >. )' % (CA, INLPR, PR))
    s2i = projeq(w, CA, INLPR, iv, '(/)', PR, zex, prex, 2)
    kpeq = w.s([w.s([w.s([p1], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (CA, S1('k', '( F + 1 )'), INLPR)), s2i], 'eqtrd',
                    '( %s -> ( 2nd ` %s ) = %s )' % (CA, S1('k', '( F + 1 )'), PR))], 'fveq2d',
               '( %s -> %s = ( 1st ` %s ) )' % (CA, KP('k', '( F + 1 )'), PR))
    ppeq = w.s([w.s([w.s([p1], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (CA, S1('k', '( F + 1 )'), INLPR)), s2i], 'eqtrd',
                    '( %s -> ( 2nd ` %s ) = %s )' % (CA, S1('k', '( F + 1 )'), PR))], 'fveq2d',
               '( %s -> %s = ( 2nd ` %s ) )' % (CA, PP('k', '( F + 1 )'), PR))
    kpk = w.s([kpeq, w.s([kna, pp1, w.inst('op1stg')], 'syl2anc', '( %s -> ( 1st ` %s ) = k )' % (CA, PR))], 'eqtrd',
              '( %s -> %s = k )' % (CA, KP('k', '( F + 1 )')))
    ppk = w.s([ppeq, w.s([kna, pp1, w.inst('op2ndg')], 'syl2anc', '( %s -> ( 2nd ` %s ) = %s )' % (CA, PR, PA1('k')))], 'eqtrd',
              '( %s -> %s = %s )' % (CA, PP('k', '( F + 1 )'), PA1('k')))
    q2 = w.s([kpk], 'breq2d', '( %s -> ( k <_ %s <-> k <_ k ) )' % (CA, KP('k', '( F + 1 )')))
    q2b = w.s([q2, w.s([], 'leidd', '( %s -> k <_ k )' % CA)], 'mpbird', '( %s -> %s )' % (CA, BQ[1]))
    q3 = w.s([kpk, kja], 'eqbrtrd', '( %s -> %s )' % (CA, BQ[2]))
    q4, _ = rwbi(w, CA, BQ[3], KP('k', '( F + 1 )'), 'k', kpk)
    q4b = w.s([q4, cka], 'mpbird', '( %s -> %s )' % (CA, BQ[3]))
    q5, _ = rwbi(w, CA, BQ[4], PP('k', '( F + 1 )'), PA1('k'), ppk)
    q5b = w.s([q5, pka], 'mpbird', '( %s -> %s )' % (CA, BQ[4]))
    pa1kp, _ = rweq(w, CA, PA1(KP('k', '( F + 1 )')), KP('k', '( F + 1 )'), 'k', kpk)
    q6 = w.s([ppk, pa1kp], 'eqtr4d', '( %s -> %s )' % (CA, BQ[5]))
    cb1 = w.s([w.s([w.s([cbna, kna, cstn], '3jca', '( %s -> ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) )' % (CA, CB, CST1)), b1], 'jca',
                   '( %s -> ( ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) /\\ %s <_ %s ) )' % (CA, CB, CST1, CST1, CB)), w.inst('scancb1')], 'syl',
              '( %s -> %s <_ ( ( ( k - k ) + 1 ) x. %s ) )' % (CA, CST1, CB))
    rhs1, _ = rweq(w, CA, '( ( ( %s - k ) + 1 ) x. %s )' % (KP('k', '( F + 1 )'), CB), KP('k', '( F + 1 )'), 'k', kpk)
    q7 = w.s([w.s([p2, cb1], 'eqbrtrd', '( %s -> %s <_ ( ( ( k - k ) + 1 ) x. %s ) )' % (CA, S2('k', '( F + 1 )'), CB)), rhs1], 'breqtrrd',
             '( %s -> %s )' % (CA, BQ[6]))
    case1 = conj7(w, CA, ne1, q2b, q3, q4b, q5b, q6, q7)


    # ------------------------------------------------- cases 2 and 3: the scan goes on
    KQ = KP('( k + 1 )', 'F')
    PQ = PP('( k + 1 )', 'F')
    BQ = ['%s =/= %s' % (S1('k', '( F + 1 )'), NONE), 'k <_ %s' % KP('k', '( F + 1 )'), '%s <_ J' % KP('k', '( F + 1 )'),
          '%s = 1o' % CP(KP('k', '( F + 1 )')), 'O <_ ( # ` %s )' % PP('k', '( F + 1 )'),
          '%s = %s' % (PP('k', '( F + 1 )'), PA1(KP('k', '( F + 1 )'))),
          '%s <_ ( ( ( %s - k ) + 1 ) x. %s )' % (S2('k', '( F + 1 )'), KP('k', '( F + 1 )'), CB)]
    AA = ['%s =/= %s' % (S1('( k + 1 )', 'F'), NONE), '( k + 1 ) <_ %s' % KQ, '%s <_ J' % KQ, '%s = 1o' % CP(KQ),
          'O <_ ( # ` %s )' % PQ, '%s = %s' % (PQ, PA1(KQ)),
          '%s <_ ( ( ( %s - ( k + 1 ) ) + 1 ) x. %s )' % (S2('( k + 1 )', 'F'), KQ, CB)]

    def gocase(CA, lift, valst, CST, cstcl, cblab, contra):
        knA = w.s([kn], lift, '( %s -> k e. NN0 )' % CA)
        jnA = w.s([jn], lift, '( %s -> J e. NN0 )' % CA)
        onA = w.s([on], lift, '( %s -> O e. NN0 )' % CA)
        wsA = w.s([ws], lift, '( %s -> W e. Word NN0 )' % CA)
        xnA = w.s([xn], lift, '( %s -> X e. NN0 )' % CA)
        znA = w.s([zn], lift, '( %s -> Z e. NN0 )' % CA)
        fnA = w.s([fn], lift, '( %s -> F e. NN0 )' % CA)
        kjA = w.s([kj], lift, '( %s -> k <_ J )' % CA)
        jltA = w.s([jlt], lift, '( %s -> J < ( k + ( F + 1 ) ) )' % CA)
        ihcA = w.s([ihc], lift, '( %s -> %s )' % (CA, IHC))
        cbnA = w.s([cbn], lift, '( %s -> %s e. NN0 )' % (CA, CB))
        k1nA = w.s([k1n], lift, '( %s -> ( k + 1 ) e. NN0 )' % CA)
        krA = w.s([knA], 'nn0red', '( %s -> k e. RR )' % CA)
        jrA = w.s([jnA], 'nn0red', '( %s -> J e. RR )' % CA)
        frA = w.s([fnA], 'nn0red', '( %s -> F e. RR )' % CA)
        b1A, b2A, cc1A, cc2A, pp1A, pp2A = cbbnd(w, CA, wsA, xnA, znA, knA, 'k', cbnA)
        kne = contra(CA, knA, jnA, onA, wsA, xnA, znA)
        klt = w.s([w.s([krA, jrA], 'ltlend', '( %s -> ( k < J <-> ( k <_ J /\\ J =/= k ) ) )' % CA),
                   w.s([kjA, w.s([w.s([kne], 'neqned', '( %s -> k =/= J )' % CA)], 'necomd', '( %s -> J =/= k )' % CA)], 'jca',
                       '( %s -> ( k <_ J /\\ J =/= k ) )' % CA)], 'mpbird',
                  '( %s -> k < J )' % CA)
        k1j = w.s([klt, w.s([w.s([knA], 'nn0zd', '( %s -> k e. ZZ )' % CA), w.s([jnA], 'nn0zd', '( %s -> J e. ZZ )' % CA), w.inst('zltp1le')],
                            'syl2anc', '( %s -> ( k < J <-> ( k + 1 ) <_ J ) )' % CA)], 'mpbid', '( %s -> ( k + 1 ) <_ J )' % CA)
        jlt2 = lin.linarith(w, CA, [jltA], 'J < ( ( k + 1 ) + F )', leaves={'k': krA, 'J': jrA, 'F': frA})
        ihk = w.s([sb(w, 'c', '( k + 1 )', 'F'), ihcA, k1nA], 'rspcdva', '( %s -> %s )' % (CA, INN('( k + 1 )', 'F')))
        cc = w.s([ihk, w.s([k1j, jlt2], 'jca', '( %s -> ( ( k + 1 ) <_ J /\\ J < ( ( k + 1 ) + F ) ) )' % CA)], 'mpd',
                 '( %s -> %s )' % (CA, CONC('( k + 1 )', 'F')))
        L = w.s([cc], 'simpld', '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (CA, AA[0], AA[1], AA[2]))
        R = w.s([cc], 'simprd', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (CA, AA[3], AA[4], AA[5], AA[6]))
        a0 = w.s([L], 'simpld', '( %s -> %s )' % (CA, AA[0]))
        bc = w.s([L], 'simprd', '( %s -> ( %s /\\ %s ) )' % (CA, AA[1], AA[2]))
        a1 = w.s([bc], 'simpld', '( %s -> %s )' % (CA, AA[1]))
        a2 = w.s([bc], 'simprd', '( %s -> %s )' % (CA, AA[2]))
        de = w.s([R], 'simpld', '( %s -> ( %s /\\ %s ) )' % (CA, AA[3], AA[4]))
        a3 = w.s([de], 'simpld', '( %s -> %s )' % (CA, AA[3]))
        a4 = w.s([de], 'simprd', '( %s -> %s )' % (CA, AA[4]))
        fg = w.s([R], 'simprd', '( %s -> ( %s /\\ %s ) )' % (CA, AA[5], AA[6]))
        a5 = w.s([fg], 'simpld', '( %s -> %s )' % (CA, AA[5]))
        a6 = w.s([fg], 'simprd', '( %s -> %s )' % (CA, AA[6]))
        # the typing of the payload
        d1 = w.s([wsA, xnA], 'jca', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % CA)
        d2 = w.s([d1, znA], 'jca', '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % CA)
        d3 = w.s([d2, onA], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % CA)
        d4 = w.s([d3, w.s([k1nA, fnA], 'jca', '( %s -> ( ( k + 1 ) e. NN0 /\\ F e. NN0 ) )' % CA)], 'jca',
                 '( %s -> ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( ( k + 1 ) e. NN0 /\\ F e. NN0 ) ) )' % CA)
        dj = w.s([d4, a0], 'jca',
                 '( %s -> ( ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( ( k + 1 ) e. NN0 /\\ F e. NN0 ) ) /\\ %s ) )' % (CA, AA[0]))
        djv = w.s([dj, w.inst('scandj')], 'syl', '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (CA, KQ, PQ))
        kqn = w.s([djv], 'simpld', '( %s -> %s e. NN0 )' % (CA, KQ))
        pqn = w.s([djv], 'simprd', '( %s -> %s e. Word NN0 )' % (CA, PQ))
        kqr = w.s([kqn], 'nn0red', '( %s -> %s e. RR )' % (CA, KQ))
        # the value
        sccl2 = sccl(w, CA, wsA, xnA, znA, onA, k1nA, fnA, '( k + 1 )', 'F')
        r1, r2 = paircl(w, CA, SC('( k + 1 )', 'F'), sccl2, OPL, 'NN0')
        cstn = cstcl(CA, r2, cc2A, pp2A)
        p1 = projeq(w, CA, SC('k', '( F + 1 )'), valst, S1('( k + 1 )', 'F'), CST,
                    w.s([r1], 'elexd', '( %s -> %s e. _V )' % (CA, S1('( k + 1 )', 'F'))),
                    w.s([cstn], 'elexd', '( %s -> %s e. _V )' % (CA, CST)), 1)
        p2 = projeq(w, CA, SC('k', '( F + 1 )'), valst, S1('( k + 1 )', 'F'), CST,
                    w.s([r1], 'elexd', '( %s -> %s e. _V )' % (CA, S1('( k + 1 )', 'F'))),
                    w.s([cstn], 'elexd', '( %s -> %s e. _V )' % (CA, CST)), 2)
        pj2 = w.s([p1], 'fveq2d', '( %s -> ( 2nd ` %s ) = ( 2nd ` %s ) )' % (CA, S1('k', '( F + 1 )'), S1('( k + 1 )', 'F')))
        kpe = w.s([pj2], 'fveq2d', '( %s -> %s = %s )' % (CA, KP('k', '( F + 1 )'), KQ))
        ppe = w.s([pj2], 'fveq2d', '( %s -> %s = %s )' % (CA, PP('k', '( F + 1 )'), PQ))
        q1 = w.s([p1, a0], 'eqnetrd', '( %s -> %s )' % (CA, BQ[0]))
        kle = lin.linarith(w, CA, [a1], 'k <_ %s' % KQ, leaves={'k': krA, KQ: kqr})
        q2 = w.s([kle, kpe], 'breqtrrd', '( %s -> %s )' % (CA, BQ[1]))
        q3 = w.s([kpe, a2], 'eqbrtrd', '( %s -> %s )' % (CA, BQ[2]))
        e4, _ = rwbi(w, CA, BQ[3], KP('k', '( F + 1 )'), KQ, kpe)
        q4 = w.s([e4, a3], 'mpbird', '( %s -> %s )' % (CA, BQ[3]))
        e5, _ = rwbi(w, CA, BQ[4], PP('k', '( F + 1 )'), PQ, ppe)
        q5 = w.s([e5, a4], 'mpbird', '( %s -> %s )' % (CA, BQ[4]))
        e6, _ = rwbi(w, CA, BQ[5], PP('k', '( F + 1 )'), PQ, ppe)
        e6b, _ = rwbi(w, CA, '%s = %s' % (PQ, PA1(KP('k', '( F + 1 )'))), KP('k', '( F + 1 )'), KQ, kpe)
        q6 = w.s([e6, w.s([e6b, a5], 'mpbird', '( %s -> %s = %s )' % (CA, PQ, PA1(KP('k', '( F + 1 )'))))], 'mpbird',
                 '( %s -> %s )' % (CA, BQ[5]))
        cbst = CBAPP[cblab](CA, cbnA, knA, kqn, r2, cc2A, pp2A, a6, b1A, b2A)
        e7, _ = rweq(w, CA, '( ( ( %s - k ) + 1 ) x. %s )' % (KP('k', '( F + 1 )'), CB), KP('k', '( F + 1 )'), KQ, kpe)
        q7 = w.s([w.s([p2, cbst], 'eqbrtrd', '( %s -> %s <_ ( ( ( %s - k ) + 1 ) x. %s ) )' % (CA, S2('k', '( F + 1 )'), KQ, CB)), e7], 'breqtrrd',
                 '( %s -> %s )' % (CA, BQ[6]))
        ab = w.s([q1, w.s([q2, q3], 'jca', '( %s -> ( %s /\\ %s ) )' % (CA, BQ[1], BQ[2]))], 'jca',
                 '( %s -> ( %s /\\ ( %s /\\ %s ) ) )' % (CA, BQ[0], BQ[1], BQ[2]))
        dee = w.s([q4, q5], 'jca', '( %s -> ( %s /\\ %s ) )' % (CA, BQ[3], BQ[4]))
        fgg = w.s([q6, q7], 'jca', '( %s -> ( %s /\\ %s ) )' % (CA, BQ[5], BQ[6]))
        return w.s([ab, w.s([dee, fgg], 'jca', '( %s -> ( ( %s /\\ %s ) /\\ ( %s /\\ %s ) ) )' % (CA, BQ[3], BQ[4], BQ[5], BQ[6]))], 'jca',
                   '( %s -> %s )' % (CA, CONC('k', '( F + 1 )')))

    def cstcl2(CA, r2, cc2A, pp2A):
        s1_ = w.s([r2, cc2A], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (CA, S2('( k + 1 )', 'F'), CP2('k')))
        s2_ = w.s([s1_, pp2A], 'nn0addcld', '( %s -> ( ( %s + %s ) + %s ) e. NN0 )' % (CA, S2('( k + 1 )', 'F'), CP2('k'), PA2('k')))
        return w.s([s2_, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (CA, CST2))
    def cstcl3(CA, r2, cc2A, pp2A):
        s1_ = w.s([r2, cc2A], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (CA, S2('( k + 1 )', 'F'), CP2('k')))
        return w.s([s1_, w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (CA, CST3))
    def cbapp3(CA, cbnA, knA, kqn, r2, cc2A, pp2A, a6, b1A, b2A):
        h = w.s([w.s([w.s([cbnA, knA, kqn], '3jca', '( %s -> ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) )' % (CA, CB, KQ)),
                      w.s([r2, cc2A, pp2A], '3jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 /\\ %s e. NN0 ) )' % (CA, S2('( k + 1 )', 'F'), CP2('k'), PA2('k')))], 'jca',
                     '( %s -> ( ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 /\\ %s e. NN0 ) ) )'
                     % (CA, CB, KQ, S2('( k + 1 )', 'F'), CP2('k'), PA2('k'))),
                 w.s([a6, b1A], 'jca', '( %s -> ( %s /\\ ( ( %s + %s ) + 1 ) <_ %s ) )' % (CA, AA[6], CP2('k'), PA2('k'), CB))], 'jca',
                '( %s -> ( ( ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 /\\ %s e. NN0 ) ) /\\ ( %s /\\ ( ( %s + %s ) + 1 ) <_ %s ) )'
                % (CA, CB, KQ, S2('( k + 1 )', 'F'), CP2('k'), PA2('k'), AA[6], CP2('k'), PA2('k'), CB) + ' )')
        return w.s([h, w.inst('scancb3')], 'syl', '( %s -> %s <_ ( ( ( %s - k ) + 1 ) x. %s ) )' % (CA, CST2, KQ, CB))
    def cbapp4(CA, cbnA, knA, kqn, r2, cc2A, pp2A, a6, b1A, b2A):
        h = w.s([w.s([w.s([cbnA, knA, kqn], '3jca', '( %s -> ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) )' % (CA, CB, KQ)),
                      w.s([r2, cc2A], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. NN0 ) )' % (CA, S2('( k + 1 )', 'F'), CP2('k')))], 'jca',
                     '( %s -> ( ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) )'
                     % (CA, CB, KQ, S2('( k + 1 )', 'F'), CP2('k'))),
                 w.s([a6, b2A], 'jca', '( %s -> ( %s /\\ ( %s + 1 ) <_ %s ) )' % (CA, AA[6], CP2('k'), CB))], 'jca',
                '( %s -> ( ( ( %s e. NN0 /\\ k e. NN0 /\\ %s e. NN0 ) /\\ ( %s e. NN0 /\\ %s e. NN0 ) ) /\\ ( %s /\\ ( %s + 1 ) <_ %s ) ) )'
                % (CA, CB, KQ, S2('( k + 1 )', 'F'), CP2('k'), AA[6], CP2('k'), CB))
        return w.s([h, w.inst('scancb4')], 'syl', '( %s -> %s <_ ( ( ( %s - k ) + 1 ) x. %s ) )' % (CA, CST3, KQ, CB))
    CBAPP = {'scancb3': cbapp3, 'scancb4': cbapp4}
    def contra2(CA, knA, jnA, onA, wsA, xnA, znA):
        Y = '( %s /\\ k = J )' % CA
        pjY = w.s([pj], 'ad3antrrr', '( %s -> O <_ ( # ` %s ) )' % (Y, PA1('J')))
        e, _ = rwbi(w, Y, 'O <_ ( # ` %s )' % PA1('J'), 'J', 'k', w.s([w.s([], 'simpr', '( %s -> k = J )' % Y)], 'eqcomd', '( %s -> J = k )' % Y))
        got = w.s([e, pjY], 'mpbid', '( %s -> O <_ ( # ` %s ) )' % (Y, PA1('k')))
        return w.s([got, w.s([], 'simplr', '( %s -> -. O <_ ( # ` %s ) )' % (Y, PA1('k')))], 'pm2.65da', '( %s -> k =/= J )' % CA) if False else                w.s([w.s([], 'simplr', '( %s -> -. O <_ ( # ` %s ) )' % (Y, PA1('k'))), got], 'pm2.65da', '( %s -> -. k = J )' % CA)
    def contra3(CA, knA, jnA, onA, wsA, xnA, znA):
        Y = '( %s /\\ k = J )' % CA
        cjY = w.s([cj], 'ad2antrr', '( %s -> %s = 1o )' % (Y, CP('J')))
        e, _ = rwbi(w, Y, '%s = 1o' % CP('J'), 'J', 'k', w.s([w.s([], 'simpr', '( %s -> k = J )' % Y)], 'eqcomd', '( %s -> J = k )' % Y))
        got = w.s([e, cjY], 'mpbid', '( %s -> %s = 1o )' % (Y, CP('k')))
        return w.s([w.s([], 'simplr', '( %s -> -. %s = 1o )' % (Y, CP('k'))), got], 'pm2.65da', '( %s -> -. k = J )' % CA)
    case2 = gocase(C12, 'ad2antrr', vf2, CST2, cstcl2, 'scancb3', contra2)
    case3 = gocase(C3, 'adantr', vf1, CST3, cstcl3, 'scancb4', contra3)
    inner = w.s([case1, case2], 'pm2.61dan', '( %s -> %s )' % (C1, CONC('k', '( F + 1 )')))
    main = w.s([inner, case3], 'pm2.61dan', '( %s -> %s )' % (U, CONC('k', '( F + 1 )')))
    w.qed([conv, w.s([w.s([w.s([main], 'ex', '( %s -> %s )' % (B, INN('k', '( F + 1 )')))], 'ralrimiva',
                          '( %s -> A. k e. NN0 %s )' % (B1, INN('k', '( F + 1 )')))], 'ex', '( %s -> %s )' % (AC, PHI('( F + 1 )')))],
          'syl', '( %s -> %s )' % (A, PHI('( F + 1 )')))
    run(w)

# ======================================================================= the option payload
if not only or 'scandj' in only:
    w = W('scandj', 'The shift and the pool list a successful scan returns are a number and a word.')
    T = '( ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( K e. NN0 /\\ F e. NN0 ) ) /\\ %s =/= %s )' % (S1('K', 'F'), NONE)
    o1 = w.s([], 'simplll', '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % T)
    on = w.s([], 'simpllr', '( %s -> O e. NN0 )' % T)
    kf = w.s([], 'simplr', '( %s -> ( K e. NN0 /\\ F e. NN0 ) )' % T)
    ne = w.s([], 'simpr', '( %s -> %s =/= %s )' % (T, S1('K', 'F'), NONE))
    ws = w.s([w.s([o1], 'simpld', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % T)], 'simpld', '( %s -> W e. Word NN0 )' % T)
    xn = w.s([w.s([o1], 'simpld', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % T)], 'simprd', '( %s -> X e. NN0 )' % T)
    zn = w.s([o1], 'simprd', '( %s -> Z e. NN0 )' % T)
    kn = w.s([kf], 'simpld', '( %s -> K e. NN0 )' % T)
    fn = w.s([kf], 'simprd', '( %s -> F e. NN0 )' % T)
    cl = sccl(w, T, ws, xn, zn, on, kn, fn, 'K', 'F')
    s1c, s2c = paircl(w, T, SC('K', 'F'), cl, OPL, 'NN0')
    dj = w.s([w.s([s1c, ne], 'jca', '( %s -> ( %s e. %s /\\ %s =/= %s ) )' % (T, S1('K', 'F'), OPL, S1('K', 'F'), NONE)),
              w.inst('algdjun')], 'syl',
             '( %s -> ( ( 2nd ` %s ) e. ( NN0 X. Word NN0 ) /\\ %s = ( inl ` ( 2nd ` %s ) ) ) )' % (T, S1('K', 'F'), S1('K', 'F'), S1('K', 'F')))
    pl = w.s([dj], 'simpld', '( %s -> ( 2nd ` %s ) e. ( NN0 X. Word NN0 ) )' % (T, S1('K', 'F')))
    a, b = paircl(w, T, '( 2nd ` %s )' % S1('K', 'F'), pl, 'NN0', 'Word NN0')
    w.qed([a, b], 'jca', '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (T, KP('K', 'F'), PP('K', 'F')))
    run(w)

# ======================================================================= assembly
if not only or 'scangol' in only:
    w = W('scangol', 'The scan invariant, as the induction on the fuel delivers it.')
    st, pt = fuelind(w, PHI('f'), 'F', 'scangob', 'scangos', fvar='f')
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
    run(w)

if not only or 'scango' in only:
    w = W('scango', 'The scan started at K with enough fuel to reach an accepted J stops at the first accepted shift (Lean: scan_go).')
    T = '( %s /\\ ( F e. NN0 /\\ K e. NN0 ) /\\ ( K <_ J /\\ J < ( K + F ) ) )' % OUT
    out = w.s([], 'simp1', '( %s -> %s )' % (T, OUT))
    fn = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ K e. NN0 ) )' % T)], 'simpld', '( %s -> F e. NN0 )' % T)
    kn = w.s([w.s([], 'simp2', '( %s -> ( F e. NN0 /\\ K e. NN0 ) )' % T)], 'simprd', '( %s -> K e. NN0 )' % T)
    hy = w.s([], 'simp3', '( %s -> ( K <_ J /\\ J < ( K + F ) ) )' % T)
    ral = w.s([w.s([fn, w.inst('scangol')], 'syl', '( %s -> %s )' % (T, PHI('F'))), out], 'mpd',
              '( %s -> A. k e. NN0 %s )' % (T, INN('k', 'F')))
    inst = w.s([sb(w, 'k', 'K', 'F'), ral, kn], 'rspcdva', '( %s -> %s )' % (T, INN('K', 'F')))
    w.qed([inst, hy], 'mpd', '( %s -> %s )' % (T, CONC('K', 'F')))
    run(w)

if not only or 'scanspec' in only:
    w = W('scanspec', 'The scan from K = 1 (Lean: scan_spec).')
    T = ('( ( W e. Word NN0 /\\ X e. NN0 /\\ Z e. NN0 ) /\\ ( O e. NN0 /\\ J e. NN /\\ F e. NN0 ) /\\ '
         '( J <_ F /\\ %s = 1o /\\ O <_ ( # ` %s ) ) )' % (CP('J'), PA1('J')))
    o1 = w.s([], 'simp1', '( %s -> ( W e. Word NN0 /\\ X e. NN0 /\\ Z e. NN0 ) )' % T)
    on = w.s([w.s([], 'simp2', '( %s -> ( O e. NN0 /\\ J e. NN /\\ F e. NN0 ) )' % T)], 'simp1d', '( %s -> O e. NN0 )' % T)
    jnn = w.s([w.s([], 'simp2', '( %s -> ( O e. NN0 /\\ J e. NN /\\ F e. NN0 ) )' % T)], 'simp2d', '( %s -> J e. NN )' % T)
    fn = w.s([w.s([], 'simp2', '( %s -> ( O e. NN0 /\\ J e. NN /\\ F e. NN0 ) )' % T)], 'simp3d', '( %s -> F e. NN0 )' % T)
    jf = w.s([w.s([], 'simp3', '( %s -> ( J <_ F /\\ %s = 1o /\\ O <_ ( # ` %s ) ) )' % (T, CP('J'), PA1('J')))], 'simp1d', '( %s -> J <_ F )' % T)
    cj = w.s([w.s([], 'simp3', '( %s -> ( J <_ F /\\ %s = 1o /\\ O <_ ( # ` %s ) ) )' % (T, CP('J'), PA1('J')))], 'simp2d',
             '( %s -> %s = 1o )' % (T, CP('J')))
    pj = w.s([w.s([], 'simp3', '( %s -> ( J <_ F /\\ %s = 1o /\\ O <_ ( # ` %s ) ) )' % (T, CP('J'), PA1('J')))], 'simp3d',
             '( %s -> O <_ ( # ` %s ) )' % (T, PA1('J')))
    jn = w.s([jnn], 'nnnn0d', '( %s -> J e. NN0 )' % T)
    outst = w.s([o1, w.s([on, jn], 'jca', '( %s -> ( O e. NN0 /\\ J e. NN0 ) )' % T),
                 w.s([cj, pj], 'jca', '( %s -> ( %s = 1o /\\ O <_ ( # ` %s ) ) )' % (T, CP('J'), PA1('J')))], '3jca', '( %s -> %s )' % (T, OUT))
    n1 = w.s([w.s([], '1nn0', '1 e. NN0')], 'a1i', '( %s -> 1 e. NN0 )' % T)
    jr = w.s([jnn], 'nnred', '( %s -> J e. RR )' % T)
    fr = w.s([fn], 'nn0red', '( %s -> F e. RR )' % T)
    j1 = w.s([jnn], 'nnge1d', '( %s -> 1 <_ J )' % T)
    jlt = lin.linarith(w, T, [jf], 'J < ( 1 + F )', leaves={'J': jr, 'F': fr})
    cc = w.s([w.s([outst, w.s([fn, n1], 'jca', '( %s -> ( F e. NN0 /\\ 1 e. NN0 ) )' % T),
                   w.s([j1, jlt], 'jca', '( %s -> ( 1 <_ J /\\ J < ( 1 + F ) ) )' % T)], '3jca',
                  '( %s -> ( %s /\\ ( F e. NN0 /\\ 1 e. NN0 ) /\\ ( 1 <_ J /\\ J < ( 1 + F ) ) ) )' % (T, OUT)), w.inst('scango')], 'syl',
             '( %s -> %s )' % (T, CONC('1', 'F')))
    L = w.s([cc], 'simpld', '( %s -> ( %s =/= %s /\\ ( 1 <_ %s /\\ %s <_ J ) ) )' % (T, S1('1', 'F'), NONE, KP('1', 'F'), KP('1', 'F')))
    R = w.s([cc], 'simprd', '( %s -> ( ( %s = 1o /\\ O <_ ( # ` %s ) ) /\\ ( %s = %s /\\ %s <_ ( ( ( %s - 1 ) + 1 ) x. %s ) ) ) )'
            % (T, CP(KP('1', 'F')), PP('1', 'F'), PP('1', 'F'), PA1(KP('1', 'F')), S2('1', 'F'), KP('1', 'F'), CB))
    fg = w.s([R], 'simprd', '( %s -> ( %s = %s /\\ %s <_ ( ( ( %s - 1 ) + 1 ) x. %s ) ) )'
             % (T, PP('1', 'F'), PA1(KP('1', 'F')), S2('1', 'F'), KP('1', 'F'), CB))
    a5 = w.s([fg], 'simpld', '( %s -> %s = %s )' % (T, PP('1', 'F'), PA1(KP('1', 'F'))))
    a6 = w.s([fg], 'simprd', '( %s -> %s <_ ( ( ( %s - 1 ) + 1 ) x. %s ) )' % (T, S2('1', 'F'), KP('1', 'F'), CB))
    ne = w.s([L], 'simpld', '( %s -> %s =/= %s )' % (T, S1('1', 'F'), NONE))
    e1 = w.s([w.s([o1], 'simp1d', '( %s -> W e. Word NN0 )' % T), w.s([o1], 'simp2d', '( %s -> X e. NN0 )' % T)], 'jca',
             '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % T)
    e2 = w.s([e1, w.s([o1], 'simp3d', '( %s -> Z e. NN0 )' % T)], 'jca',
             '( %s -> ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) )' % T)
    dj = w.s([e2, on], 'jca', '( %s -> ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) )' % T)
    dj2 = w.s([w.s([dj, w.s([n1, fn], 'jca', '( %s -> ( 1 e. NN0 /\\ F e. NN0 ) )' % T)], 'jca',
                   '( %s -> ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( 1 e. NN0 /\\ F e. NN0 ) ) )' % T), ne], 'jca',
               '( %s -> ( ( ( ( ( W e. Word NN0 /\\ X e. NN0 ) /\\ Z e. NN0 ) /\\ O e. NN0 ) /\\ ( 1 e. NN0 /\\ F e. NN0 ) ) /\\ %s =/= %s ) )'
               % (T, S1('1', 'F'), NONE))
    djv = w.s([dj2, w.inst('scandj')], 'syl', '( %s -> ( %s e. NN0 /\\ %s e. Word NN0 ) )' % (T, KP('1', 'F'), PP('1', 'F')))
    kqn = w.s([djv], 'simpld', '( %s -> %s e. NN0 )' % (T, KP('1', 'F')))
    npc = w.s([w.s([kqn], 'nn0cnd', '( %s -> %s e. CC )' % (T, KP('1', 'F'))), w.s([], '1cnd', '( %s -> 1 e. CC )' % T)], 'npcand',
              '( %s -> ( ( %s - 1 ) + 1 ) = %s )' % (T, KP('1', 'F'), KP('1', 'F')))
    rr = w.s([npc], 'oveq1d', '( %s -> ( ( ( %s - 1 ) + 1 ) x. %s ) = ( %s x. %s ) )' % (T, KP('1', 'F'), CB, KP('1', 'F'), CB))
    a6b = w.s([a6, rr], 'breqtrd', '( %s -> %s <_ ( %s x. %s ) )' % (T, S2('1', 'F'), KP('1', 'F'), CB))
    w.qed([L, w.s([w.s([R], 'simpld', '( %s -> ( %s = 1o /\\ O <_ ( # ` %s ) ) )' % (T, CP(KP('1', 'F')), PP('1', 'F'))),
                   w.s([a5, a6b], 'jca', '( %s -> ( %s = %s /\\ %s <_ ( %s x. %s ) ) )'
                       % (T, PP('1', 'F'), PA1(KP('1', 'F')), S2('1', 'F'), KP('1', 'F'), CB))], 'jca',
                  '( %s -> ( ( %s = 1o /\\ O <_ ( # ` %s ) ) /\\ ( %s = %s /\\ %s <_ ( %s x. %s ) ) ) )'
                  % (T, CP(KP('1', 'F')), PP('1', 'F'), PP('1', 'F'), PA1(KP('1', 'F')), S2('1', 'F'), KP('1', 'F'), CB))], 'jca',
          '( %s -> ( ( %s =/= %s /\\ ( 1 <_ %s /\\ %s <_ J ) ) /\\ ( ( %s = 1o /\\ O <_ ( # ` %s ) ) /\\ ( %s = %s /\\ %s <_ ( %s x. %s ) ) ) ) )'
          % (T, S1('1', 'F'), NONE, KP('1', 'F'), KP('1', 'F'), CP(KP('1', 'F')), PP('1', 'F'), PP('1', 'F'), PA1(KP('1', 'F')),
             S2('1', 'F'), KP('1', 'F'), CB))
    run(w)
