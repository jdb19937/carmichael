"""Sortie A4a, batch 11: the cost of resGo and reservoir (step 2)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

RG = lambda q, f: '( ( ( Z ResGo Y ) ` %s ) ` %s )' % (q, f)
R1 = lambda q, f: '( 1st ` %s )' % RG(q, f)
R2 = lambda q, f: '( 2nd ` %s )' % RG(q, f)
IP = lambda q: '( IsPrimeTD ` %s )' % q
SM = lambda q: '( Y SmoothTD ( %s - 1 ) )' % q
SM_ = SM('q')
BND = '( ( ( %s + Y ) + %s ) + 4 )' % (SQ('M'), LG('M'))
OUT = '( Z e. NN0 /\\ Y e. NN /\\ M e. NN0 )'
INN = lambda q, f: '( ( %s + %s ) <_ ( M + 1 ) -> %s <_ ( %s x. %s ) )' % (q, f, R2(q, f), f, BND)
PHI = lambda f: '( %s -> A. q e. NN %s )' % (OUT, INN('q', f))
WN = '( Word NN0 X. NN0 )'
B2 = '( 2o X. NN0 )'

def sb(w, frm, to, f):
    idst = w.s([], 'id', '( %s = %s -> %s = %s )' % (frm, to, frm, to))
    st, new = w.wcongr(INN(frm, f), {}, '%s = %s' % (frm, to), {}, rules={frm: (to, idst)})
    assert new == INN(to, f), '\n%s\n%s' % (new, INN(to, f))
    return st

def bndcl(w, A, mn, yn):
    sqn = w.s([mn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A, SQ('M')))
    lgn = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % A), mn, w.inst('nlogcl')], 'syl2anc',
              '( %s -> %s e. NN0 )' % (A, LG('M')))
    yn0 = w.s([yn], 'nnnn0d', '( %s -> Y e. NN0 )' % A)
    s1 = w.s([sqn, yn0], 'nn0addcld', '( %s -> ( %s + Y ) e. NN0 )' % (A, SQ('M')))
    s2 = w.s([s1, lgn], 'nn0addcld', '( %s -> ( ( %s + Y ) + %s ) e. NN0 )' % (A, SQ('M'), LG('M')))
    s3 = w.s([s2, w.s([w.s([], '4nn0', '4 e. NN0')], 'a1i', '( %s -> 4 e. NN0 )' % A)], 'nn0addcld', '( %s -> %s e. NN0 )' % (A, BND))
    return sqn, lgn, s3

# --------------------------------------------------------------- base
if not only or 'resgocostb' in only:
    w = W('resgocostb', 'Base of the induction for the cost of the reservoir loop.')
    B0 = '( %s /\\ q e. NN )' % OUT
    zn = w.s([], 'simpl1', '( %s -> Z e. NN0 )' % B0)
    yn = w.s([], 'simpl2', '( %s -> Y e. NN )' % B0)
    mn = w.s([], 'simpl3', '( %s -> M e. NN0 )' % B0)
    qn = w.s([], 'simpr', '( %s -> q e. NN )' % B0)
    v = w.s([w.s([zn, yn], 'jca', '( %s -> ( Z e. NN0 /\\ Y e. NN ) )' % B0), qn, w.inst('resgo0')], 'syl2anc',
            '( %s -> %s = <. (/) , 0 >. )' % (B0, RG('q', '0')))
    p2 = projeq(w, B0, RG('q', '0'), v, '(/)', '0', w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % B0),
                w.s([w.s([], 'c0ex', '0 e. _V')], 'a1i', '( %s -> 0 e. _V )' % B0), 2)
    sqn, lgn, bn = bndcl(w, B0, mn, yn)
    z0 = w.s([w.s([bn], 'nn0cnd', '( %s -> %s e. CC )' % (B0, BND))], 'mul02d', '( %s -> ( 0 x. %s ) = 0 )' % (B0, BND))
    zle = w.s([w.s([w.s([], '0re', '0 e. RR'), w.inst('leid')], 'ax-mp', '0 <_ 0')], 'a1i', '( %s -> 0 <_ 0 )' % B0)
    bd = w.s([p2, w.s([zle, z0], 'breqtrrd', '( %s -> 0 <_ ( 0 x. %s ) )' % (B0, BND))], 'eqbrtrd',
             '( %s -> %s <_ ( 0 x. %s ) )' % (B0, R2('q', '0'), BND))
    w.qed([w.s([bd], 'a1d', '( %s -> %s )' % (B0, INN('q', '0')))], 'ralrimiva', PHI('0'))
    run(w)

# --------------------------------------------------------------- step
if not only or 'resgocosts' in only:
    w = W('resgocosts', 'Step of the induction for the cost of the reservoir loop.')
    IHD = 'A. q e. NN %s' % INN('q', 'F')
    IHC = 'A. c e. NN %s' % INN('c', 'F')
    A = '( F e. NN0 /\\ ( %s -> %s ) )' % (OUT, IHD)
    AC = '( F e. NN0 /\\ ( %s -> %s ) )' % (OUT, IHC)
    cbv = w.s([sb(w, 'q', 'c', 'F')], 'cbvralvw', '( %s <-> %s )' % (IHD, IHC))
    conv = w.s([w.s([], 'simpl', '( %s -> F e. NN0 )' % A),
                w.s([w.s([], 'simpr', '( %s -> ( %s -> %s ) )' % (A, OUT, IHD)),
                     w.s([w.s([cbv], 'a1i', '( %s -> ( %s <-> %s ) )' % (A, IHD, IHC))], 'biimpd', '( %s -> ( %s -> %s ) )' % (A, IHD, IHC))],
                    'syld', '( %s -> ( %s -> %s ) )' % (A, OUT, IHC))], 'jca', '( %s -> %s )' % (A, AC))
    B1 = '( %s /\\ %s )' % (AC, OUT)
    B = '( %s /\\ q e. NN )' % B1
    fn = w.s([], 'simplll', '( %s -> F e. NN0 )' % B)
    ihh = w.s([], 'simpllr', '( %s -> ( %s -> %s ) )' % (B, OUT, IHC))
    out = w.s([], 'simplr', '( %s -> %s )' % (B, OUT))
    qn = w.s([], 'simpr', '( %s -> q e. NN )' % B)
    zn = w.s([out], 'simp1d', '( %s -> Z e. NN0 )' % B)
    yn = w.s([out], 'simp2d', '( %s -> Y e. NN )' % B)
    mn = w.s([out], 'simp3d', '( %s -> M e. NN0 )' % B)
    ihc = w.s([ihh, out], 'mpd', '( %s -> %s )' % (B, IHC))
    sqn, lgn, bn = bndcl(w, B, mn, yn)
    U = '( %s /\\ ( q + ( F + 1 ) ) <_ ( M + 1 ) )' % B
    fnU = w.s([fn], 'adantr', '( %s -> F e. NN0 )' % U)
    qnU = w.s([qn], 'adantr', '( %s -> q e. NN )' % U)
    znU = w.s([zn], 'adantr', '( %s -> Z e. NN0 )' % U)
    ynU = w.s([yn], 'adantr', '( %s -> Y e. NN )' % U)
    mnU = w.s([mn], 'adantr', '( %s -> M e. NN0 )' % U)
    ihcU = w.s([ihc], 'adantr', '( %s -> %s )' % (U, IHC))
    bnU = w.s([bn], 'adantr', '( %s -> %s e. NN0 )' % (U, BND))
    sup = w.s([], 'simpr', '( %s -> ( q + ( F + 1 ) ) <_ ( M + 1 ) )' % U)
    qn0 = w.s([qnU], 'nnnn0d', '( %s -> q e. NN0 )' % U)
    qm1 = w.s([qnU, w.inst('nnm1nn0')], 'syl', '( %s -> ( q - 1 ) e. NN0 )' % U)
    q1n = w.s([qnU, w.inst('peano2nn')], 'syl', '( %s -> ( q + 1 ) e. NN )' % U)
    qr = w.s([qnU], 'nnred', '( %s -> q e. RR )' % U)
    fr = w.s([fnU], 'nn0red', '( %s -> F e. RR )' % U)
    mr = w.s([mnU], 'nn0red', '( %s -> M e. RR )' % U)
    fge = w.s([fnU], 'nn0ge0d', '( %s -> 0 <_ F )' % U)
    qle = lin.linarith(w, U, [sup, fge], 'q <_ M', leaves={'q': qr, 'F': fr, 'M': mr})
    qm1le = lin.linarith(w, U, [qle], '( q - 1 ) <_ M', leaves={'q': qr, 'M': mr})
    # the three bounds
    ipc = w.s([qn0, w.inst('isprimetdcost')], 'syl', '( %s -> ( 2nd ` %s ) <_ ( %s + 1 ) )' % (U, IP('q'), SQ('q')))
    sqm = w.s([w.s([w.s([qn0, mnU], 'jca', '( %s -> ( q e. NN0 /\\ M e. NN0 ) )' % U), qle], 'jca',
                   '( %s -> ( ( q e. NN0 /\\ M e. NN0 ) /\\ q <_ M ) )' % U), w.inst('nsqrtmo')], 'syl',
              '( %s -> %s <_ %s )' % (U, SQ('q'), SQ('M')))
    smc = w.s([ynU, qm1, w.inst('smoothtdcost')], 'syl2anc', '( %s -> ( 2nd ` %s ) <_ ( ( Y + %s ) + 2 ) )' % (U, SM_, LG('( q - 1 )')))
    b2u = w.s([w.s([w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % U), w.s([w.s([], '2z', '2 e. ZZ')], 'a1i', '( %s -> 2 e. ZZ )' % U),
                    w.s([w.s([w.s([], '2re', '2 e. RR'), w.inst('leid')], 'ax-mp', '2 <_ 2')], 'a1i', '( %s -> 2 <_ 2 )' % U)], '3jca',
                   '( %s -> ( 2 e. ZZ /\\ 2 e. ZZ /\\ 2 <_ 2 ) )' % U), w.inst('eluz2')], 'sylibr', '( %s -> 2 e. ( ZZ>= ` 2 ) )' % U)
    lgm = w.s([w.s([w.s([b2u, w.s([qm1, mnU], 'jca', '( %s -> ( ( q - 1 ) e. NN0 /\\ M e. NN0 ) )' % U)], 'jca',
                        '( %s -> ( 2 e. ( ZZ>= ` 2 ) /\\ ( ( q - 1 ) e. NN0 /\\ M e. NN0 ) ) )' % U), qm1le], 'jca',
                   '( %s -> ( ( 2 e. ( ZZ>= ` 2 ) /\\ ( ( q - 1 ) e. NN0 /\\ M e. NN0 ) ) /\\ ( q - 1 ) <_ M ) )' % U), w.inst('nlogmo')], 'syl',
              '( %s -> %s <_ %s )' % (U, LG('( q - 1 )'), LG('M')))
    # the recursive call
    ihq = w.s([sb(w, 'c', '( q + 1 )', 'F'), ihcU, q1n], 'rspcdva', '( %s -> %s )' % (U, INN('( q + 1 )', 'F')))
    sup2 = lin.linarith(w, U, [sup], '( ( q + 1 ) + F ) <_ ( M + 1 )', leaves={'q': qr, 'F': fr, 'M': mr})
    ihv = w.s([ihq, sup2], 'mpd', '( %s -> %s <_ ( F x. %s ) )' % (U, R2('( q + 1 )', 'F'), BND))
    # the value
    KEEP = 'if ( Z < q , if ( ( 1st ` %s ) = 1o , ( 1st ` %s ) , (/) ) , (/) )' % (IP('q'), SM_)
    THEN = 'if ( %s = 1o , ( <" q "> ++ %s ) , %s )' % (KEEP, R1('( q + 1 )', 'F'), R1('( q + 1 )', 'F'))
    SUM = '( ( ( %s + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % (R2('( q + 1 )', 'F'), IP('q'), SM_)
    val = w.s([w.s([w.s([znU, ynU], 'jca', '( %s -> ( Z e. NN0 /\\ Y e. NN ) )' % U), qnU], 'jca',
                   '( %s -> ( ( Z e. NN0 /\\ Y e. NN ) /\\ q e. NN ) )' % U), fnU, w.inst('resgop1')], 'syl2anc',
              '( %s -> %s = <. %s , %s >. )' % (U, RG('q', '( F + 1 )'), THEN, SUM))
    rcl = w.s([w.s([w.s([znU, ynU], 'jca', '( %s -> ( Z e. NN0 /\\ Y e. NN ) )' % U), q1n], 'jca',
                   '( %s -> ( ( Z e. NN0 /\\ Y e. NN ) /\\ ( q + 1 ) e. NN ) )' % U), fnU, w.inst('resgocl')], 'syl2anc',
              '( %s -> %s e. %s )' % (U, RG('( q + 1 )', 'F'), WN))
    c1, c2 = paircl(w, U, RG('( q + 1 )', 'F'), rcl, 'Word NN0', 'NN0')
    icl = w.s([qn0, w.inst('isprimetdcl')], 'syl', '( %s -> %s e. %s )' % (U, IP('q'), B2))
    i1, i2 = paircl(w, U, IP('q'), icl, '2o', 'NN0')
    scl = w.s([ynU, qm1, w.inst('smoothtdcl')], 'syl2anc', '( %s -> %s e. %s )' % (U, SM_, B2))
    m1, m2 = paircl(w, U, SM_, scl, '2o', 'NN0')
    s1c = w.s([w.s([qn0, w.inst('s1cl')], 'syl', '( %s -> <" q "> e. Word NN0 )' % U), c1, w.inst('ccatcl')], 'syl2anc',
              '( %s -> ( <" q "> ++ %s ) e. Word NN0 )' % (U, R1('( q + 1 )', 'F')))
    xa = w.s([s1c, c1], 'ifcld', '( %s -> %s e. Word NN0 )' % (U, THEN))
    xb = w.s([w.s([w.s([c2, i2], 'nn0addcld', '( %s -> ( %s + ( 2nd ` %s ) ) e. NN0 )' % (U, R2('( q + 1 )', 'F'), IP('q'))), m2], 'nn0addcld',
                  '( %s -> ( ( %s + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) e. NN0 )' % (U, R2('( q + 1 )', 'F'), IP('q'), SM_)), w.inst('peano2nn0')], 'syl',
             '( %s -> %s e. NN0 )' % (U, SUM))
    p2 = projeq(w, U, RG('q', '( F + 1 )'), val, THEN, SUM, xa, xb, 2)
    # the arithmetic
    sqmr = w.s([w.s([sqn], 'adantr', '( %s -> %s e. NN0 )' % (U, SQ('M')))], 'nn0red', '( %s -> %s e. RR )' % (U, SQ('M')))
    sqqr = w.s([w.s([qn0, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (U, SQ('q')))], 'nn0red', '( %s -> %s e. RR )' % (U, SQ('q')))
    lgmr = w.s([w.s([lgn], 'adantr', '( %s -> %s e. NN0 )' % (U, LG('M')))], 'nn0red', '( %s -> %s e. RR )' % (U, LG('M')))
    lgqr = w.s([w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % U), qm1, w.inst('nlogcl')], 'syl2anc',
                    '( %s -> %s e. NN0 )' % (U, LG('( q - 1 )')))], 'nn0red', '( %s -> %s e. RR )' % (U, LG('( q - 1 )')))
    yr = w.s([ynU], 'nnred', '( %s -> Y e. RR )' % U)
    c2r = w.s([c2], 'nn0red', '( %s -> %s e. RR )' % (U, R2('( q + 1 )', 'F')))
    i2r = w.s([i2], 'nn0red', '( %s -> ( 2nd ` %s ) e. RR )' % (U, IP('q')))
    m2r = w.s([m2], 'nn0red', '( %s -> ( 2nd ` %s ) e. RR )' % (U, SM_))
    li = lin.nlinarith(w, U, [ipc, sqm, smc, lgm, ihv], '%s <_ ( ( F + 1 ) x. %s )' % (SUM, BND),
                       leaves={SQ('M'): sqmr, SQ('q'): sqqr, LG('M'): lgmr, LG('( q - 1 )'): lgqr, 'Y': yr, 'F': fr,
                               R2('( q + 1 )', 'F'): c2r, '( 2nd ` %s )' % IP('q'): i2r, '( 2nd ` %s )' % SM_: m2r})
    main = w.s([w.s([p2, li], 'eqbrtrd', '( %s -> %s <_ ( ( F + 1 ) x. %s ) )' % (U, R2('q', '( F + 1 )'), BND))], 'ex',
               '( %s -> %s )' % (B, INN('q', '( F + 1 )')))
    w.qed([conv, w.s([w.s([main], 'ralrimiva', '( %s -> A. q e. NN %s )' % (B1, INN('q', '( F + 1 )')))], 'ex',
                     '( %s -> %s )' % (AC, PHI('( F + 1 )')))], 'syl', '( %s -> %s )' % (A, PHI('( F + 1 )')))
    run(w)

if not only or 'resgocostl' in only:
    w = W('resgocostl', 'The cost of the reservoir loop, as the induction on the fuel delivers it.')
    st, pt = fuelind(w, PHI('f'), 'F', 'resgocostb', 'resgocosts', fvar='f')
    w.lines[-1] = w.lines[-1].replace('%s:' % st, 'qed:', 1)
    run(w)

if not only or 'resgocost' in only:
    w = W('resgocost', 'The cost of the reservoir loop (Lean: resGo_cost).')
    T = '( ( Z e. NN0 /\\ Y e. NN /\\ Q e. NN ) /\\ ( F e. NN0 /\\ M e. NN0 /\\ ( Q + F ) <_ ( M + 1 ) ) )'
    zn = w.s([], 'simpl1', '( %s -> Z e. NN0 )' % T)
    yn = w.s([], 'simpl2', '( %s -> Y e. NN )' % T)
    qn = w.s([], 'simpl3', '( %s -> Q e. NN )' % T)
    fn = w.s([], 'simpr1', '( %s -> F e. NN0 )' % T)
    mn = w.s([], 'simpr2', '( %s -> M e. NN0 )' % T)
    sup = w.s([], 'simpr3', '( %s -> ( Q + F ) <_ ( M + 1 ) )' % T)
    ral = w.s([w.s([fn, w.inst('resgocostl')], 'syl', '( %s -> %s )' % (T, PHI('F'))),
               w.s([zn, yn, mn], '3jca', '( %s -> %s )' % (T, OUT))], 'mpd', '( %s -> A. q e. NN %s )' % (T, INN('q', 'F')))
    inst = w.s([sb(w, 'q', 'Q', 'F'), ral, qn], 'rspcdva', '( %s -> %s )' % (T, INN('Q', 'F')))
    w.qed([inst, sup], 'mpd', '( %s -> %s <_ ( F x. %s ) )' % (T, R2('Q', 'F'), BND))
    run(w)

# ======================================================================= reservoir cost
if not only or 'rescost' in only:
    w = W('rescost', 'The cost of step 2, the reservoir (Lean: reservoir_cost).')
    T = '( Z e. NN /\\ V e. NN0 /\\ Y e. NN )'
    RV = '( ( Z Reservoir V ) ` Y )'
    RGI = '( ( ( V ResGo Y ) ` 2 ) ` ( Z - 1 ) )'
    B = '( ( %s + Y ) + %s )' % (SQ('Z'), LG('Z'))
    zn = w.s([], 'simp1', '( %s -> Z e. NN )' % T)
    vn = w.s([], 'simp2', '( %s -> V e. NN0 )' % T)
    yn = w.s([], 'simp3', '( %s -> Y e. NN )' % T)
    zn0 = w.s([zn], 'nnnn0d', '( %s -> Z e. NN0 )' % T)
    zm1 = w.s([zn, w.inst('nnm1nn0')], 'syl', '( %s -> ( Z - 1 ) e. NN0 )' % T)
    n2 = w.s([w.s([], '2nn', '2 e. NN')], 'a1i', '( %s -> 2 e. NN )' % T)
    zr = w.s([zn], 'nnred', '( %s -> Z e. RR )' % T)
    zge = w.s([zn], 'nnge1d', '( %s -> 1 <_ Z )' % T)
    sup = lin.linarith(w, T, [zge], '( 2 + ( Z - 1 ) ) <_ ( Z + 1 )', leaves={'Z': zr})
    val = w.s([w.s([w.s([zn, vn], 'jca', '( %s -> ( Z e. NN /\\ V e. NN0 ) )' % T), yn], 'jca',
                   '( %s -> ( ( Z e. NN /\\ V e. NN0 ) /\\ Y e. NN ) )' % T), w.inst('reservoirval')], 'syl',
              '( %s -> %s = %s )' % (T, RV, RGI))
    cost = w.s([w.s([w.s([vn, yn, n2], '3jca', '( %s -> ( V e. NN0 /\\ Y e. NN /\\ 2 e. NN ) )' % T),
                     w.s([zm1, zn0, sup], '3jca', '( %s -> ( ( Z - 1 ) e. NN0 /\\ Z e. NN0 /\\ ( 2 + ( Z - 1 ) ) <_ ( Z + 1 ) ) )' % T)], 'jca',
                    '( %s -> ( ( V e. NN0 /\\ Y e. NN /\\ 2 e. NN ) /\\ ( ( Z - 1 ) e. NN0 /\\ Z e. NN0 /\\ ( 2 + ( Z - 1 ) ) <_ ( Z + 1 ) ) ) )' % T),
                w.inst('resgocost')], 'syl', '( %s -> ( 2nd ` %s ) <_ ( ( Z - 1 ) x. ( %s + 4 ) ) )' % (T, RGI, B))
    cl = w.s([w.s([w.s([vn, yn], 'jca', '( %s -> ( V e. NN0 /\\ Y e. NN ) )' % T), n2], 'jca',
                  '( %s -> ( ( V e. NN0 /\\ Y e. NN ) /\\ 2 e. NN ) )' % T), zm1, w.inst('resgocl')], 'syl2anc',
             '( %s -> %s e. %s )' % (T, RGI, WN))
    c1, c2 = paircl(w, T, RGI, cl, 'Word NN0', 'NN0')
    sqn = w.s([zn0, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (T, SQ('Z')))
    lgn = w.s([w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % T), zn0, w.inst('nlogcl')], 'syl2anc',
              '( %s -> %s e. NN0 )' % (T, LG('Z')))
    bn = w.s([w.s([sqn, w.s([yn], 'nnnn0d', '( %s -> Y e. NN0 )' % T)], 'nn0addcld', '( %s -> ( %s + Y ) e. NN0 )' % (T, SQ('Z'))), lgn], 'nn0addcld',
             '( %s -> %s e. NN0 )' % (T, B))
    br = w.s([bn], 'nn0red', '( %s -> %s e. RR )' % (T, B))
    bge = w.s([bn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (T, B))
    c2r = w.s([c2], 'nn0red', '( %s -> ( 2nd ` %s ) e. RR )' % (T, RGI))
    sqr = w.s([sqn], 'nn0red', '( %s -> %s e. RR )' % (T, SQ('Z')))
    lgr = w.s([lgn], 'nn0red', '( %s -> %s e. RR )' % (T, LG('Z')))
    yr = w.s([yn], 'nnred', '( %s -> Y e. RR )' % T)
    sq0 = w.s([sqn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (T, SQ('Z')))
    lg0 = w.s([lgn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (T, LG('Z')))
    y0 = w.s([w.s([yn], 'nnnn0d', '( %s -> Y e. NN0 )' % T)], 'nn0ge0d', '( %s -> 0 <_ Y )' % T)
    li = lin.nlinarith(w, T, [cost, sq0, lg0, y0, zge], '( 2nd ` %s ) <_ ( ( Z + 1 ) x. ( %s + 6 ) )' % (RGI, B),
                       leaves={SQ('Z'): sqr, LG('Z'): lgr, 'Y': yr, 'Z': zr, '( 2nd ` %s )' % RGI: c2r})
    eqv, _ = rweq(w, T, '( 2nd ` %s )' % RV, RV, RGI, val)
    w.qed([eqv, li], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ ( ( Z + 1 ) x. ( %s + 6 ) ) )' % (T, RV, B))
    run(w)
