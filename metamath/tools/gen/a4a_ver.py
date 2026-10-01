"""Sortie A4a, batch 7: allPrimeTD and verify (step 5 of the algorithm)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *
import lin

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

CSV = '( <" P "> ++ V )'
B2 = '( 2o X. NN0 )'
RALP = lambda x: 'A. p e. ran %s p e. Prime' % x

def ex(w, a, e, lab):
    return w.s([w.s([], lab, '%s e. _V' % e)], 'a1i', '( %s -> %s e. _V )' % (a, e))

# ======================================================================= allPrimeTD value
PHI = '( ( 1st ` ( AllPrimeTD ` s ) ) = 1o <-> %s )' % RALP('s')
def _b(w, goal):
    v = w.s([], 'allprimetd0', '( AllPrimeTD ` (/) ) = <. 1o , 0 >.')
    e = w.s([v], 'fveq2i', '( 1st ` ( AllPrimeTD ` (/) ) ) = ( 1st ` <. 1o , 0 >. )')
    o = w.s([w.s([], '1oex', '1o e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op1st', '( 1st ` <. 1o , 0 >. ) = 1o')
    l = w.s([e, o], 'eqtri', '( 1st ` ( AllPrimeTD ` (/) ) ) = 1o')
    r = w.s([w.s([w.s([], 'rn0', 'ran (/) = (/)')], 'raleqi', '( %s <-> A. p e. (/) p e. Prime )' % RALP('(/)')),
             w.s([], 'ral0', 'A. p e. (/) p e. Prime')], 'mpbir', RALP('(/)'))
    w.qed([l, r], '2th', goal)
def _s(w, A, ih, co):
    IP = '( 1st ` ( IsPrimeTD ` P ) )'
    AP = '( 1st ` ( AllPrimeTD ` V ) )'
    IFE = 'if ( %s = 1o , %s , (/) )' % (IP, AP)
    SUM = '( ( ( 2nd ` ( IsPrimeTD ` P ) ) + ( 2nd ` ( AllPrimeTD ` V ) ) ) + 1 )'
    L = '( 1st ` ( AllPrimeTD ` %s ) )' % CSV
    vs = w.s([], 'simp1', '( %s -> V e. Word NN0 )' % A)
    pn = w.s([], 'simp2', '( %s -> P e. NN0 )' % A)
    ihs = w.s([], 'simp3', '( %s -> %s )' % (A, ih))
    cl = w.s([vs, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` V ) e. %s )' % (A, B2))
    a1, b1 = paircl(w, A, '( AllPrimeTD ` V )', cl, '2o', 'NN0')
    icl = w.s([pn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` P ) e. %s )' % (A, B2))
    i1, i2 = paircl(w, A, '( IsPrimeTD ` P )', icl, '2o', 'NN0')
    cs = w.s([pn, vs, w.inst('allprimetdcs')], 'syl2anc', '( %s -> ( AllPrimeTD ` %s ) = <. %s , %s >. )' % (A, CSV, IFE, SUM))
    xa = w.s([a1, w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % A)], 'ifcld', '( %s -> %s e. 2o )' % (A, IFE))
    xb = w.s([w.s([i2, b1], 'nn0addcld', '( %s -> ( ( 2nd ` ( IsPrimeTD ` P ) ) + ( 2nd ` ( AllPrimeTD ` V ) ) ) e. NN0 )' % A),
              w.inst('peano2nn0')], 'syl', '( %s -> %s e. NN0 )' % (A, SUM))
    p1 = projeq(w, A, '( AllPrimeTD ` %s )' % CSV, cs, IFE, SUM, xa, xb, 1)
    st, sf = ifproj(w, A, L, p1, '%s = 1o' % IP, AP, '(/)')
    prb = w.s([pn, w.inst('isprimetdspec')], 'syl', '( %s -> ( %s = 1o <-> P e. Prime ) )' % (A, IP))
    rc = w.s([pn, vs, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (A, CSV))
    pex = w.s([pn], 'elexd', '( %s -> P e. _V )' % A)
    sbp = w.s([w.s([], 'id', '( p = P -> p = P )')], 'eleq1d', '( p = P -> ( p e. Prime <-> P e. Prime ) )')
    rsp, _ = ralcons(w, A, 'p', 'p e. Prime', 'P e. Prime', 'V', rc, pex, sbp)
    T = '( %s /\\ %s = 1o )' % (A, IP)
    prt = w.s([w.s([prb], 'adantr', '( %s -> ( %s = 1o <-> P e. Prime ) )' % (T, IP)), w.s([], 'simpr', '( %s -> %s = 1o )' % (T, IP))], 'mpbid',
              '( %s -> P e. Prime )' % T)
    lt = w.s([w.s([st], 'eqeq1d', '( %s -> ( %s = 1o <-> %s = 1o ) )' % (T, L, AP)), w.s([ihs], 'adantr', '( %s -> %s )' % (T, ih))], 'bitrd',
             '( %s -> ( %s = 1o <-> %s ) )' % (T, L, RALP('V')))
    rt = w.s([w.s([rsp], 'adantr', '( %s -> ( %s <-> ( P e. Prime /\\ %s ) ) )' % (T, RALP(CSV), RALP('V'))),
              w.s([prt], 'biantrurd', '( %s -> ( %s <-> ( P e. Prime /\\ %s ) ) )' % (T, RALP('V'), RALP('V')))], 'bitr4d',
             '( %s -> ( %s <-> %s ) )' % (T, RALP(CSV), RALP('V')))
    ct = w.s([lt, rt], 'bitr4d', '( %s -> ( %s = 1o <-> %s ) )' % (T, L, RALP(CSV)))
    F = '( %s /\\ -. %s = 1o )' % (A, IP)
    npr = w.s([w.s([], 'simpr', '( %s -> -. %s = 1o )' % (F, IP)),
               w.s([prb], 'adantr', '( %s -> ( %s = 1o <-> P e. Prime ) )' % (F, IP))], 'mtbid', '( %s -> -. P e. Prime )' % F)
    nl = w.s([w.s([sf], 'eqeq1d', '( %s -> ( %s = 1o <-> (/) = 1o ) )' % (F, L)), zne1o(w, F)], 'mtbird', '( %s -> -. %s = 1o )' % (F, L))
    nr = w.s([w.s([rsp], 'adantr', '( %s -> ( %s <-> ( P e. Prime /\\ %s ) ) )' % (F, RALP(CSV), RALP('V'))),
              w.s([npr], 'intnanrd', '( %s -> -. ( P e. Prime /\\ %s ) )' % (F, RALP('V')))], 'mtbird', '( %s -> -. %s )' % (F, RALP(CSV)))
    cf = w.s([nl, nr], '2falsed', '( %s -> ( %s = 1o <-> %s ) )' % (F, L, RALP(CSV)))
    w.qed([ct, cf], 'pm2.61dan', '( %s -> %s )' % (A, co))
family(run, 'allprimetdfst', PHI, _b, _s, desc='allPrimeTD reports true exactly when every element is prime (Lean: allPrimeTD_fst).', only=only)

# ======================================================================= allPrimeTD cost
RALX = lambda x: 'A. p e. ran %s p <_ X' % x
PHI = '( ( X e. NN0 /\\ %s ) -> ( 2nd ` ( AllPrimeTD ` s ) ) <_ ( ( # ` s ) x. ( %s + 2 ) ) )' % (RALX('s'), SQ('X'))
def _b(w, goal):
    P = '( X e. NN0 /\\ %s )' % RALX('(/)')
    xn = w.s([], 'simpl', '( %s -> X e. NN0 )' % P)
    v = w.s([], 'allprimetd0', '( AllPrimeTD ` (/) ) = <. 1o , 0 >.')
    e = w.s([v], 'fveq2i', '( 2nd ` ( AllPrimeTD ` (/) ) ) = ( 2nd ` <. 1o , 0 >. )')
    o = w.s([w.s([], '1oex', '1o e. _V'), w.s([], 'c0ex', '0 e. _V')], 'op2nd', '( 2nd ` <. 1o , 0 >. ) = 0')
    l = w.s([w.s([e, o], 'eqtri', '( 2nd ` ( AllPrimeTD ` (/) ) ) = 0')], 'a1i', '( %s -> ( 2nd ` ( AllPrimeTD ` (/) ) ) = 0 )' % P)
    hn = w.s([w.s([w.s([], 'wrd0', '(/) e. Word NN0'), w.inst('lencl')], 'ax-mp', '( # ` (/) ) e. NN0')], 'a1i', '( %s -> ( # ` (/) ) e. NN0 )' % P)
    sqn = w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (P, SQ('X')))
    s2 = w.s([sqn, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % P)], 'nn0addcld', '( %s -> ( %s + 2 ) e. NN0 )' % (P, SQ('X')))
    pr = w.s([hn, s2], 'nn0mulcld', '( %s -> ( ( # ` (/) ) x. ( %s + 2 ) ) e. NN0 )' % (P, SQ('X')))
    w.qed([l, w.s([pr], 'nn0ge0d', '( %s -> 0 <_ ( ( # ` (/) ) x. ( %s + 2 ) ) )' % (P, SQ('X')))], 'eqbrtrd', goal)
def _s(w, A, ih, co):
    A2 = '( %s /\\ ( X e. NN0 /\\ %s ) )' % (A, RALX(CSV))
    IPC = '( 2nd ` ( IsPrimeTD ` P ) )'
    APC = '( 2nd ` ( AllPrimeTD ` V ) )'
    IFE = 'if ( ( 1st ` ( IsPrimeTD ` P ) ) = 1o , ( 1st ` ( AllPrimeTD ` V ) ) , (/) )'
    SUM = '( ( %s + %s ) + 1 )' % (IPC, APC)
    SX = SQ('X')
    vs = w.s([], 'simpl1', '( %s -> V e. Word NN0 )' % A2)
    pn = w.s([], 'simpl2', '( %s -> P e. NN0 )' % A2)
    xn = w.s([], 'simprl', '( %s -> X e. NN0 )' % A2)
    alx = w.s([], 'simprr', '( %s -> %s )' % (A2, RALX(CSV)))
    rc = w.s([pn, vs, w.inst('algrncs')], 'syl2anc', '( %s -> ran %s = ( { P } u. ran V ) )' % (A2, CSV))
    pex = w.s([pn], 'elexd', '( %s -> P e. _V )' % A2)
    sbx = w.s([w.s([], 'id', '( p = P -> p = P )')], 'breq1d', '( p = P -> ( p <_ X <-> P <_ X ) )')
    rsp, _ = ralcons(w, A2, 'p', 'p <_ X', 'P <_ X', 'V', rc, pex, sbx)
    both = w.s([rsp, alx], 'mpbid', '( %s -> ( P <_ X /\\ %s ) )' % (A2, RALX('V')))
    px = w.s([both], 'simpld', '( %s -> P <_ X )' % A2)
    alv = w.s([both], 'simprd', '( %s -> %s )' % (A2, RALX('V')))
    ihs = w.s([w.s([], 'simpl3', '( %s -> %s )' % (A2, ih)), w.s([xn, alv], 'jca', '( %s -> ( X e. NN0 /\\ %s ) )' % (A2, RALX('V')))], 'mpd',
              '( %s -> %s <_ ( ( # ` V ) x. ( %s + 2 ) ) )' % (A2, APC, SX))
    cl = w.s([vs, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` V ) e. %s )' % (A2, B2))
    a1, b1 = paircl(w, A2, '( AllPrimeTD ` V )', cl, '2o', 'NN0')
    icl = w.s([pn, w.inst('isprimetdcl')], 'syl', '( %s -> ( IsPrimeTD ` P ) e. %s )' % (A2, B2))
    i1, i2 = paircl(w, A2, '( IsPrimeTD ` P )', icl, '2o', 'NN0')
    cs = w.s([pn, vs, w.inst('allprimetdcs')], 'syl2anc', '( %s -> ( AllPrimeTD ` %s ) = <. %s , %s >. )' % (A2, CSV, IFE, SUM))
    xa = w.s([a1, w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % A2)], 'ifcld', '( %s -> %s e. 2o )' % (A2, IFE))
    xb = w.s([w.s([i2, b1], 'nn0addcld', '( %s -> ( %s + %s ) e. NN0 )' % (A2, IPC, APC)), w.inst('peano2nn0')], 'syl',
             '( %s -> %s e. NN0 )' % (A2, SUM))
    p2 = projeq(w, A2, '( AllPrimeTD ` %s )' % CSV, cs, IFE, SUM, xa, xb, 2)
    ipc = w.s([pn, w.inst('isprimetdcost')], 'syl', '( %s -> %s <_ ( %s + 1 ) )' % (A2, IPC, SQ('P')))
    sqm = w.s([w.s([w.s([pn, xn], 'jca', '( %s -> ( P e. NN0 /\\ X e. NN0 ) )' % A2), px], 'jca',
                   '( %s -> ( ( P e. NN0 /\\ X e. NN0 ) /\\ P <_ X ) )' % A2), w.inst('nsqrtmo')], 'syl',
              '( %s -> %s <_ %s )' % (A2, SQ('P'), SX))
    lc = w.s([pn, vs, w.inst('alglencs')], 'syl2anc', '( %s -> ( # ` %s ) = ( ( # ` V ) + 1 ) )' % (A2, CSV))
    lenn = w.s([vs, w.inst('lencl')], 'syl', '( %s -> ( # ` V ) e. NN0 )' % A2)
    lenr = w.s([lenn], 'nn0red', '( %s -> ( # ` V ) e. RR )' % A2)
    sxr = w.s([w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A2, SX))], 'nn0red', '( %s -> %s e. RR )' % (A2, SX))
    spr = w.s([w.s([pn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (A2, SQ('P')))], 'nn0red', '( %s -> %s e. RR )' % (A2, SQ('P')))
    ipr = w.s([i2], 'nn0red', '( %s -> %s e. RR )' % (A2, IPC))
    apr = w.s([b1], 'nn0red', '( %s -> %s e. RR )' % (A2, APC))
    lge = w.s([lenn], 'nn0ge0d', '( %s -> 0 <_ ( # ` V ) )' % A2)
    RHS = '( ( ( # ` V ) + 1 ) x. ( %s + 2 ) )' % SX
    li = lin.nlinarith(w, A2, [ipc, sqm, ihs, lge], '%s <_ %s' % (SUM, RHS),
                       leaves={SX: sxr, SQ('P'): spr, '( # ` V )': lenr, IPC: ipr, APC: apr})
    rr, _ = rweq(w, A2, '( ( # ` %s ) x. ( %s + 2 ) )' % (CSV, SX), '( # ` %s )' % CSV, '( ( # ` V ) + 1 )', lc)
    w.qed([w.s([w.s([p2, li], 'eqbrtrd', '( %s -> ( 2nd ` ( AllPrimeTD ` %s ) ) <_ %s )' % (A2, CSV, RHS)), rr], 'breqtrrd',
               '( %s -> ( 2nd ` ( AllPrimeTD ` %s ) ) <_ ( ( # ` %s ) x. ( %s + 2 ) ) )' % (A2, CSV, CSV, SX))], 'ex', '( %s -> %s )' % (A, co))
def _f(w, st, phit):
    T = '( ( S e. Word NN0 /\\ X e. NN0 ) /\\ %s )' % RALX('S')
    w.qed([w.s([w.s([], 'simpll', '( %s -> S e. Word NN0 )' % T),
                w.s([st], 'a1i', '( %s -> ( S e. Word NN0 -> %s ) )' % (T, phit))], 'mpd', '( %s -> %s )' % (T, phit)),
           w.s([w.s([], 'simplr', '( %s -> X e. NN0 )' % T), w.s([], 'simpr', '( %s -> %s )' % (T, RALX('S')))], 'jca',
               '( %s -> ( X e. NN0 /\\ %s ) )' % (T, RALX('S')))], 'mpd',
          '( %s -> ( 2nd ` ( AllPrimeTD ` S ) ) <_ ( ( # ` S ) x. ( %s + 2 ) ) )' % (T, SQ('X')))
family(run, 'allprimetdcost', PHI, _b, _s, finish=_f, desc='The cost of allPrimeTD (Lean: allPrimeTD_snd).', only=only)

# ======================================================================= verify
KORD = lambda x: 'A. p e. ran %s ( p - 1 ) || ( M - 1 )' % x
KORM = lambda x: 'A. p e. ran %s ( ( M - 1 ) mod ( p - 1 ) ) = 0' % x
if not only or 'verifykor' in only:
    w = W('verifykor', "Korselt's divisibility in the form korseltTD tests (Lean: Nat.mod_eq_zero_of_dvd inside verify_spec).")
    T = '( ( ( M e. NN0 /\\ W e. Word NN0 ) /\\ %s ) /\\ %s )' % (RALP('W'), KORD('W'))
    mn = w.s([], 'simplll', '( %s -> M e. NN0 )' % T)
    ws = w.s([], 'simpllr', '( %s -> W e. Word NN0 )' % T)
    alp = w.s([], 'simplr', '( %s -> %s )' % (T, RALP('W')))
    kd = w.s([], 'simpr', '( %s -> %s )' % (T, KORD('W')))
    R = '( %s /\\ r e. ran W )' % T
    rr = w.s([], 'simpr', '( %s -> r e. ran W )' % R)
    sbp = w.s([w.s([], 'id', '( p = r -> p = r )')], 'eleq1d', '( p = r -> ( p e. Prime <-> r e. Prime ) )')
    rp = w.s([sbp, w.s([alp], 'adantr', '( %s -> %s )' % (R, RALP('W'))), rr], 'rspcdva', '( %s -> r e. Prime )' % R)
    sbd = w.s([w.s([w.s([], 'id', '( p = r -> p = r )')], 'oveq1d', '( p = r -> ( p - 1 ) = ( r - 1 ) )')], 'breq1d',
              '( p = r -> ( ( p - 1 ) || ( M - 1 ) <-> ( r - 1 ) || ( M - 1 ) ) )')
    rd = w.s([sbd, w.s([kd], 'adantr', '( %s -> %s )' % (R, KORD('W'))), rr], 'rspcdva', '( %s -> ( r - 1 ) || ( M - 1 ) )' % R)
    rm1 = w.s([w.s([rp, w.inst('prmuz2')], 'syl', '( %s -> r e. ( ZZ>= ` 2 ) )' % R), w.inst('uz2m1nn')], 'syl', '( %s -> ( r - 1 ) e. NN )' % R)
    mz = w.s([w.s([w.s([mn], 'adantr', '( %s -> M e. NN0 )' % R)], 'nn0zd', '( %s -> M e. ZZ )' % R),
              w.s([w.s([], '1z', '1 e. ZZ')], 'a1i', '( %s -> 1 e. ZZ )' % R)], 'zsubcld', '( %s -> ( M - 1 ) e. ZZ )' % R)
    md = w.s([w.s([rm1, mz, w.inst('dvdsval3')], 'syl2anc', '( %s -> ( ( r - 1 ) || ( M - 1 ) <-> ( ( M - 1 ) mod ( r - 1 ) ) = 0 ) )' % R), rd], 'mpbid',
             '( %s -> ( ( M - 1 ) mod ( r - 1 ) ) = 0 )' % R)
    ralr = w.s([md], 'ralrimiva', '( %s -> A. r e. ran W ( ( M - 1 ) mod ( r - 1 ) ) = 0 )' % T)
    cbv = w.s([w.s([w.s([w.s([], 'id', '( p = r -> p = r )')], 'oveq1d', '( p = r -> ( p - 1 ) = ( r - 1 ) )')], 'oveq2d',
                   '( p = r -> ( ( M - 1 ) mod ( p - 1 ) ) = ( ( M - 1 ) mod ( r - 1 ) ) )')], 'eqeq1d',
              '( p = r -> ( ( ( M - 1 ) mod ( p - 1 ) ) = 0 <-> ( ( M - 1 ) mod ( r - 1 ) ) = 0 ) )')
    cb = w.s([cbv], 'cbvralvw', '( %s <-> A. r e. ran W ( ( M - 1 ) mod ( r - 1 ) ) = 0 )' % KORM('W'))
    w.qed([w.s([cb], 'a1i', '( %s -> ( %s <-> A. r e. ran W ( ( M - 1 ) mod ( r - 1 ) ) = 0 ) )' % (T, KORM('W'))), ralr], 'mpbird',
          '( %s -> %s )' % (T, KORM('W')))
    run(w)

VV = '( M Verify W )'
COST = '( ( ( ( ( 2nd ` ( NodupTD ` W ) ) + ( 2nd ` ( AllPrimeTD ` W ) ) ) + ( 2nd ` ( ProdL ` W ) ) ) + ( 2nd ` ( M KorseltTD W ) ) ) + 2 )'

def costcl(w, T, mn, ws):
    nd = w.s([w.s([ws, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. %s )' % (T, B2)), w.inst('xp2nd')], 'syl',
             '( %s -> ( 2nd ` ( NodupTD ` W ) ) e. NN0 )' % T)
    ap = w.s([w.s([ws, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. %s )' % (T, B2)), w.inst('xp2nd')], 'syl',
             '( %s -> ( 2nd ` ( AllPrimeTD ` W ) ) e. NN0 )' % T)
    pd = w.s([w.s([ws, w.inst('prodlcl')], 'syl', '( %s -> ( ProdL ` W ) e. ( NN0 X. NN0 ) )' % T), w.inst('xp2nd')], 'syl',
             '( %s -> ( 2nd ` ( ProdL ` W ) ) e. NN0 )' % T)
    ko = w.s([w.s([mn, ws, w.inst('korselttdcl')], 'syl2anc', '( %s -> ( M KorseltTD W ) e. %s )' % (T, B2)), w.inst('xp2nd')], 'syl',
             '( %s -> ( 2nd ` ( M KorseltTD W ) ) e. NN0 )' % T)
    s1 = w.s([nd, ap], 'nn0addcld', '( %s -> ( ( 2nd ` ( NodupTD ` W ) ) + ( 2nd ` ( AllPrimeTD ` W ) ) ) e. NN0 )' % T)
    s2 = w.s([s1, pd], 'nn0addcld', '( %s -> ( ( ( 2nd ` ( NodupTD ` W ) ) + ( 2nd ` ( AllPrimeTD ` W ) ) ) + ( 2nd ` ( ProdL ` W ) ) ) e. NN0 )' % T)
    s3 = w.s([s2, ko], 'nn0addcld',
             '( %s -> ( ( ( ( 2nd ` ( NodupTD ` W ) ) + ( 2nd ` ( AllPrimeTD ` W ) ) ) + ( 2nd ` ( ProdL ` W ) ) ) + ( 2nd ` ( M KorseltTD W ) ) ) e. NN0 )' % T)
    s4 = w.s([s3, w.s([w.s([], '2nn0', '2 e. NN0')], 'a1i', '( %s -> 2 e. NN0 )' % T)], 'nn0addcld', '( %s -> %s e. NN0 )' % (T, COST))
    return s4, nd, ap, pd, ko
ND = '( 1st ` ( NodupTD ` W ) )'
AP = '( 1st ` ( AllPrimeTD ` W ) )'
PD = '( 1st ` ( ProdL ` W ) )'
KO = '( 1st ` ( M KorseltTD W ) )'
OK4 = 'if ( %s = 1o , %s , (/) )' % ('if ( %s = M , 1o , (/) )' % PD, KO)
OK3 = 'if ( %s = 1o , %s , (/) )' % (AP, OK4)
OK2 = 'if ( %s = 1o , %s , (/) )' % (ND, OK3)
OK1 = 'if ( 3 <_ ( # ` W ) , %s , (/) )' % OK2
if not only or 'verifyspec' in only:
    w = W('verifyspec', 'verify accepts a certified output (Lean: verify_spec, with Korselt\'s divisibility in place of the necessity half of Korselt).')
    T = ('( ( M e. NN0 /\\ W e. Word NN0 ) /\\ ( Fun `\' W /\\ %s /\\ 3 <_ ( # ` W ) ) /\\ ( M = %s /\\ %s ) )'
         % (RALP('W'), PRD('W'), KORD('W')))
    mn = w.s([], 'simp1l', '( %s -> M e. NN0 )' % T)
    ws = w.s([], 'simp1r', '( %s -> W e. Word NN0 )' % T)
    alp = w.s([], 'simp2', '( %s -> ( Fun `\' W /\\ %s /\\ 3 <_ ( # ` W ) ) )' % (T, RALP('W')))
    fu = w.s([alp], 'simp1d', "( %s -> Fun `' W )" % T)
    alp2 = w.s([alp], 'simp2d', '( %s -> %s )' % (T, RALP('W')))
    l3 = w.s([alp], 'simp3d', '( %s -> 3 <_ ( # ` W ) )' % T)
    meq = w.s([], 'simp3l', '( %s -> M = %s )' % (T, PRD('W')))
    kd = w.s([], 'simp3r', '( %s -> %s )' % (T, KORD('W')))
    v = w.s([mn, ws, w.inst('verifyval')], 'syl2anc',
            '( %s -> %s = <. %s , %s >. )' % (T, VV, OK1, COST))
    # the four conditions
    c1 = w.s([w.s([ws, w.inst('noduptdfst')], 'syl', "( %s -> ( %s = 1o <-> Fun `' W ) )" % (T, ND)), fu], 'mpbird', '( %s -> %s = 1o )' % (T, ND))
    c2 = w.s([w.s([ws, w.inst('allprimetdfst')], 'syl', '( %s -> ( %s = 1o <-> %s ) )' % (T, AP, RALP('W'))), alp2], 'mpbird',
             '( %s -> %s = 1o )' % (T, AP))
    pl = w.s([w.s([ws, w.inst('prodlspec')], 'syl', '( %s -> %s = %s )' % (T, PD, PRD('W'))), meq], 'eqtr4d', '( %s -> %s = M )' % (T, PD))
    c3 = w.s([pl], 'iftrued', '( %s -> if ( %s = M , 1o , (/) ) = 1o )' % (T, PD))
    kom = w.s([w.s([w.s([mn, ws], 'jca', '( %s -> ( M e. NN0 /\\ W e. Word NN0 ) )' % T), alp2], 'jca',
                   '( %s -> ( ( M e. NN0 /\\ W e. Word NN0 ) /\\ %s ) )' % (T, RALP('W'))), kd], 'jca',
              '( %s -> ( ( ( M e. NN0 /\\ W e. Word NN0 ) /\\ %s ) /\\ %s ) )' % (T, RALP('W'), KORD('W')))
    korm = w.s([kom, w.inst('verifykor')], 'syl', '( %s -> %s )' % (T, KORM('W')))
    c4 = w.s([w.s([mn, ws, w.inst('korselttdfst')], 'syl2anc', '( %s -> ( %s = 1o <-> %s ) )' % (T, KO, KORM('W'))), korm], 'mpbird',
             '( %s -> %s = 1o )' % (T, KO))
    # unwind the nested ifs
    i4 = w.s([c3], 'iftrued', '( %s -> %s = %s )' % (T, OK4, KO))
    v4 = w.s([i4, c4], 'eqtrd', '( %s -> %s = 1o )' % (T, OK4))
    i3 = w.s([c2], 'iftrued', '( %s -> %s = %s )' % (T, OK3, OK4))
    v3 = w.s([i3, v4], 'eqtrd', '( %s -> %s = 1o )' % (T, OK3))
    i2 = w.s([c1], 'iftrued', '( %s -> %s = %s )' % (T, OK2, OK3))
    v2 = w.s([i2, v3], 'eqtrd', '( %s -> %s = 1o )' % (T, OK2))
    i1 = w.s([l3], 'iftrued', '( %s -> %s = %s )' % (T, OK1, OK2))
    v1 = w.s([i1, v2], 'eqtrd', '( %s -> %s = 1o )' % (T, OK1))
    ok2o = w.s([v1, w.s([w.s([], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % T)], 'eqeltrd', '( %s -> %s e. 2o )' % (T, OK1))
    cnn = costcl(w, T, mn, ws)[0]
    p1 = projeq(w, T, VV, v, OK1, COST, ok2o, cnn, 1)
    w.qed([p1, v1], 'eqtrd', '( %s -> ( 1st ` %s ) = 1o )' % (T, VV))
    run(w)

# ======================================================================= verify cost
RALX2 = lambda x: 'A. p e. ran %s p <_ X' % x
if not only or 'verifycost' in only:
    w = W('verifycost', 'The cost of verify (Lean: verify_cost).')
    SX = SQ('X')
    LW = '( # ` W )'
    T = '( ( M e. NN0 /\\ X e. NN0 /\\ W e. Word NN0 ) /\\ %s )' % RALX2('W')
    mn = w.s([], 'simpl1', '( %s -> M e. NN0 )' % T)
    xn = w.s([], 'simpl2', '( %s -> X e. NN0 )' % T)
    ws = w.s([], 'simpl3', '( %s -> W e. Word NN0 )' % T)
    alx = w.s([], 'simpr', '( %s -> %s )' % (T, RALX2('W')))
    v = w.s([mn, ws, w.inst('verifyval')], 'syl2anc', '( %s -> %s = <. %s , %s >. )' % (T, VV, OK1, COST))
    cnn, nd, ap, pd, ko = costcl(w, T, mn, ws)
    nd1 = w.s([w.s([ws, w.inst('noduptdcl')], 'syl', '( %s -> ( NodupTD ` W ) e. %s )' % (T, B2)), w.inst('xp1st')], 'syl',
              '( %s -> %s e. 2o )' % (T, ND))
    ap1 = w.s([w.s([ws, w.inst('allprimetdcl')], 'syl', '( %s -> ( AllPrimeTD ` W ) e. %s )' % (T, B2)), w.inst('xp1st')], 'syl',
              '( %s -> %s e. 2o )' % (T, AP))
    ko1 = w.s([w.s([mn, ws, w.inst('korselttdcl')], 'syl2anc', '( %s -> ( M KorseltTD W ) e. %s )' % (T, B2)), w.inst('xp1st')], 'syl',
              '( %s -> %s e. 2o )' % (T, KO))
    z2 = w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % T)
    o2 = w.s([w.s([], '1oel2o', '1o e. 2o')], 'a1i', '( %s -> 1o e. 2o )' % T)
    ok4 = w.s([ko1, z2], 'ifcld', '( %s -> %s e. 2o )' % (T, OK4))
    ok3 = w.s([ok4, z2], 'ifcld', '( %s -> %s e. 2o )' % (T, OK3))
    ok2o = w.s([ok3, z2], 'ifcld', '( %s -> %s e. 2o )' % (T, OK2))
    ok1 = w.s([ok2o, w.s([w.s([], '0el2o', '(/) e. 2o')], 'a1i', '( %s -> (/) e. 2o )' % T)], 'ifcld', '( %s -> %s e. 2o )' % (T, OK1))
    p2 = projeq(w, T, VV, v, OK1, COST, ok1, cnn, 2)
    # the four bounds
    b1 = w.s([ws, w.inst('noduptdcost')], 'syl', '( %s -> ( 2nd ` ( NodupTD ` W ) ) <_ ( %s x. ( %s + 1 ) ) )' % (T, LW, LW))
    b2 = w.s([w.s([ws, xn], 'jca', '( %s -> ( W e. Word NN0 /\\ X e. NN0 ) )' % T), alx, w.inst('allprimetdcost')], 'syl2anc',
             '( %s -> ( 2nd ` ( AllPrimeTD ` W ) ) <_ ( %s x. ( %s + 2 ) ) )' % (T, LW, SX))
    b3 = w.s([ws, w.inst('prodlcost')], 'syl', '( %s -> ( 2nd ` ( ProdL ` W ) ) = %s )' % (T, LW))
    b4 = w.s([mn, ws, w.inst('korselttdcost')], 'syl2anc', '( %s -> ( 2nd ` ( M KorseltTD W ) ) = %s )' % (T, LW))
    lenn = w.s([ws, w.inst('lencl')], 'syl', '( %s -> %s e. NN0 )' % (T, LW))
    lenr = w.s([lenn], 'nn0red', '( %s -> %s e. RR )' % (T, LW))
    lge = w.s([lenn], 'nn0ge0d', '( %s -> 0 <_ %s )' % (T, LW))
    sxr = w.s([w.s([xn, w.inst('nsqrtcl')], 'syl', '( %s -> %s e. NN0 )' % (T, SX))], 'nn0red', '( %s -> %s e. RR )' % (T, SX))
    ndr = w.s([nd], 'nn0red', '( %s -> ( 2nd ` ( NodupTD ` W ) ) e. RR )' % T)
    apr = w.s([ap], 'nn0red', '( %s -> ( 2nd ` ( AllPrimeTD ` W ) ) e. RR )' % T)
    pdr = w.s([pd], 'nn0red', '( %s -> ( 2nd ` ( ProdL ` W ) ) e. RR )' % T)
    kor = w.s([ko], 'nn0red', '( %s -> ( 2nd ` ( M KorseltTD W ) ) e. RR )' % T)
    GOAL = '( ( %s x. ( ( %s + %s ) + 6 ) ) + 4 )' % (LW, SX, LW)
    li = lin.nlinarith(w, T, [b1, b2, b3, b4, lge], '%s <_ %s' % (COST, GOAL),
                       leaves={LW: lenr, SX: sxr, '( 2nd ` ( NodupTD ` W ) )': ndr, '( 2nd ` ( AllPrimeTD ` W ) )': apr,
                               '( 2nd ` ( ProdL ` W ) )': pdr, '( 2nd ` ( M KorseltTD W ) )': kor})
    w.qed([p2, li], 'eqbrtrd', '( %s -> ( 2nd ` %s ) <_ %s )' % (T, VV, GOAL))
    run(w)
