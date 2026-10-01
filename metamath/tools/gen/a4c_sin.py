"""Sortie A4c, batch 2: setIfNone (Lean: AlgExtract.setIfNone_*)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from a4alib import *

only = sys.argv[1:]
def run(w):
    if only and w.label not in only: return True
    return w.run()

NONE = '( inr ` (/) )'
RES = '( T |` ( NN0 \\ { R } ) )'
UPD = '( %s u. { <. R , V >. } )' % RES
UPDS = '( %s u. { <. R , ( inl ` S ) >. } )' % RES
SIN = '( ( T SetIfNone R ) ` S )'
T3 = '( T e. Tbl /\\ R e. NN0 /\\ V e. W )'

def upctx(w, A):
    """T Fn NN0, the restriction Fn, and the singleton Fn, under antecedent A"""
    tt = w.s([], 'simp1', '( %s -> T e. Tbl )' % A)
    rr = w.s([], 'simp2', '( %s -> R e. NN0 )' % A)
    vv = w.s([], 'simp3', '( %s -> V e. W )' % A)
    fn = w.s([w.s([tt, w.inst('tblf')], 'syl', '( %s -> T : NN0 --> ( Word NN0 |_| 1o ) )' % A), w.inst('ffn')], 'syl',
             '( %s -> T Fn NN0 )' % A)
    rfn = w.s([fn, w.s([w.s([], 'difss', '( NN0 \\ { R } ) C_ NN0')], 'a1i', '( %s -> ( NN0 \\ { R } ) C_ NN0 )' % A),
               w.inst('fnssres')], 'syl2anc', '( %s -> %s Fn ( NN0 \\ { R } ) )' % (A, RES))
    rex = w.s([rr], 'elexd', '( %s -> R e. _V )' % A)
    vex = w.s([vv], 'elexd', '( %s -> V e. _V )' % A)
    sfn = w.s([rex, vex, w.inst('fnsng')], 'syl2anc', '( %s -> { <. R , V >. } Fn { R } )' % A)
    return tt, rr, vv, fn, rfn, rex, vex, sfn

# ------------------------------------------------------------------ sinupd1
if not only or 'sinupd1' in only:
    w = W('sinupd1', 'The updated table at the updated residue (Lean: Function.update_same).')
    tt, rr, vv, fn, rfn, rex, vex, sfn = upctx(w, T3)
    dm = w.s([rfn, w.inst('fndm')], 'syl', '( %s -> dom %s = ( NN0 \\ { R } ) )' % (T3, RES))
    bi = w.s([], 'eldifsn', '( R e. ( NN0 \\ { R } ) <-> ( R e. NN0 /\\ R =/= R ) )')
    im = w.s([w.s([bi], 'biimpi', '( R e. ( NN0 \\ { R } ) -> ( R e. NN0 /\\ R =/= R ) )')], 'simprd',
             '( R e. ( NN0 \\ { R } ) -> R =/= R )')
    nir = w.s([], 'neirr', '-. R =/= R')
    nel = w.s([nir, im], 'mto', '-. R e. ( NN0 \\ { R } )')
    nel2 = w.s([w.s([dm], 'eleq2d', '( %s -> ( R e. dom %s <-> R e. ( NN0 \\ { R } ) ) )' % (T3, RES)),
                w.s([nel], 'a1i', '( %s -> -. R e. ( NN0 \\ { R } ) )' % T3)], 'mtbird',
               '( %s -> -. R e. dom %s )' % (T3, RES))
    w.qed([rex, vex, nel2, w.inst('fsnunfv')], 'syl3anc', '( %s -> ( %s ` R ) = V )' % (T3, UPD))
    run(w)

# ------------------------------------------------------------------ sinupd2
if not only or 'sinupd2' in only:
    w = W('sinupd2', 'The updated table away from the updated residue (Lean: Function.update_noteq).')
    A = '( %s /\\ ( C e. NN0 /\\ C =/= R ) )' % T3
    tt, rr, vv, fn, rfn, rex, vex, sfn = upctx(w, T3)
    rfnA = w.s([rfn], 'adantr', '( %s -> %s Fn ( NN0 \\ { R } ) )' % (A, RES))
    sfnA = w.s([sfn], 'adantr', '( %s -> { <. R , V >. } Fn { R } )' % A)
    dj = w.s([w.s([w.s([], 'disjdif', '( { R } i^i ( NN0 \\ { R } ) ) = (/)')], 'a1i',
                  '( %s -> ( { R } i^i ( NN0 \\ { R } ) ) = (/) )' % A),
              w.s([w.s([], 'incom', '( ( NN0 \\ { R } ) i^i { R } ) = ( { R } i^i ( NN0 \\ { R } ) )')], 'a1i',
                  '( %s -> ( ( NN0 \\ { R } ) i^i { R } ) = ( { R } i^i ( NN0 \\ { R } ) ) )' % A)], 'eqtrd',
             '( %s -> ( ( NN0 \\ { R } ) i^i { R } ) = (/) )' % A)
    cin = w.s([w.s([w.s([], 'simprl', '( %s -> C e. NN0 )' % A), w.s([], 'simprr', '( %s -> C =/= R )' % A)], 'jca',
                   '( %s -> ( C e. NN0 /\\ C =/= R ) )' % A),
               w.s([w.s([], 'eldifsn', '( C e. ( NN0 \\ { R } ) <-> ( C e. NN0 /\\ C =/= R ) )')], 'a1i',
                   '( %s -> ( C e. ( NN0 \\ { R } ) <-> ( C e. NN0 /\\ C =/= R ) ) )' % A)], 'mpbird',
              '( %s -> C e. ( NN0 \\ { R } ) )' % A)
    u1 = w.s([rfnA, sfnA, w.s([dj, cin], 'jca', '( %s -> ( ( ( NN0 \\ { R } ) i^i { R } ) = (/) /\\ C e. ( NN0 \\ { R } ) ) )' % A),
              w.inst('fvun1')], 'syl3anc', '( %s -> ( %s ` C ) = ( %s ` C ) )' % (A, UPD, RES))
    rv = w.s([cin, w.inst('fvres')], 'syl', '( %s -> ( %s ` C ) = ( T ` C ) )' % (A, RES))
    w.qed([u1, rv], 'eqtrd', '( %s -> ( %s ` C ) = ( T ` C ) )' % (A, UPD))
    run(w)

# ------------------------------------------------------------------ sinapply
T4 = '( ( T e. Tbl /\\ R e. NN0 /\\ S e. Word NN0 ) /\\ C e. NN0 )'
COND = '( ( T ` R ) = %s /\\ C = R )' % NONE
RHS = 'if ( %s , ( inl ` S ) , ( T ` C ) )' % COND

def sinctx(w, A):
    tt = w.s([], 'simpl1', '( %s -> T e. Tbl )' % A)
    rr = w.s([], 'simpl2', '( %s -> R e. NN0 )' % A)
    ss = w.s([], 'simpl3', '( %s -> S e. Word NN0 )' % A)
    cc = w.s([], 'simpr', '( %s -> C e. NN0 )' % A)
    ie = w.s([w.s([], 'fvex', '( inl ` S ) e. _V')], 'a1i', '( %s -> ( inl ` S ) e. _V )' % A)
    tr = w.s([tt, rr, ie], '3jca', '( %s -> ( T e. Tbl /\\ R e. NN0 /\\ ( inl ` S ) e. _V ) )' % A)
    val = w.s([w.s([tt, rr], 'jca', '( %s -> ( T e. Tbl /\\ R e. NN0 ) )' % A), ss, w.inst('setifnoneval')], 'syl2anc',
              '( %s -> %s = if ( ( T ` R ) = %s , %s , T ) )' % (A, SIN, NONE, UPDS))
    return tt, rr, ss, cc, ie, tr, val

if not only or 'sinapply' in only:
    w = W('sinapply', 'The value of a conditional table update at a residue (Lean: setIfNone_apply).')
    tt, rr, ss, cc, ie, tr, val = sinctx(w, T4)
    # ---- case ( T ` R ) = NONE
    A1 = '( %s /\\ ( T ` R ) = %s )' % (T4, NONE)
    hyp = w.s([], 'simpr', '( %s -> ( T ` R ) = %s )' % (A1, NONE))
    vA = w.s([w.s([val], 'adantr', '( %s -> %s = if ( ( T ` R ) = %s , %s , T ) )' % (A1, SIN, NONE, UPDS)),
              w.s([hyp], 'iftrued', '( %s -> if ( ( T ` R ) = %s , %s , T ) = %s )' % (A1, NONE, UPDS, UPDS))], 'eqtrd',
             '( %s -> %s = %s )' % (A1, SIN, UPDS))
    #   subcase C = R
    A1a = '( %s /\\ C = R )' % A1
    v1 = w.s([vA], 'adantr', '( %s -> %s = %s )' % (A1a, SIN, UPDS))
    ceq = w.s([], 'simpr', '( %s -> C = R )' % A1a)
    l1 = w.s([w.s([v1], 'fveq1d', '( %s -> ( %s ` C ) = ( %s ` C ) )' % (A1a, SIN, UPDS)),
              w.s([ceq], 'fveq2d', '( %s -> ( %s ` C ) = ( %s ` R ) )' % (A1a, UPDS, UPDS))], 'eqtrd',
             '( %s -> ( %s ` C ) = ( %s ` R ) )' % (A1a, SIN, UPDS))
    u1 = w.s([w.s([w.s([tr], 'adantr', '( %s -> ( T e. Tbl /\\ R e. NN0 /\\ ( inl ` S ) e. _V ) )' % A1)], 'adantr',
                  '( %s -> ( T e. Tbl /\\ R e. NN0 /\\ ( inl ` S ) e. _V ) )' % A1a), w.inst('sinupd1')], 'syl',
             '( %s -> ( %s ` R ) = ( inl ` S ) )' % (A1a, UPDS))
    lhs1 = w.s([l1, u1], 'eqtrd', '( %s -> ( %s ` C ) = ( inl ` S ) )' % (A1a, SIN))
    ct = w.s([w.s([hyp], 'adantr', '( %s -> ( T ` R ) = %s )' % (A1a, NONE)), ceq], 'jca', '( %s -> %s )' % (A1a, COND))
    rhs1 = w.s([ct], 'iftrued', '( %s -> %s = ( inl ` S ) )' % (A1a, RHS))
    e1 = w.s([lhs1, rhs1], 'eqtr4d', '( %s -> ( %s ` C ) = %s )' % (A1a, SIN, RHS))
    #   subcase C =/= R
    A1b = '( %s /\\ -. C = R )' % A1
    v2 = w.s([vA], 'adantr', '( %s -> %s = %s )' % (A1b, SIN, UPDS))
    cne = w.s([w.s([], 'simpr', '( %s -> -. C = R )' % A1b), w.inst('neqned')], 'syl', '( %s -> C =/= R )' % A1b)
    ccb = w.s([w.s([cc], 'adantr', '( %s -> C e. NN0 )' % A1)], 'adantr', '( %s -> C e. NN0 )' % A1b)
    u2 = w.s([w.s([w.s([w.s([tr], 'adantr', '( %s -> ( T e. Tbl /\\ R e. NN0 /\\ ( inl ` S ) e. _V ) )' % A1)], 'adantr',
                       '( %s -> ( T e. Tbl /\\ R e. NN0 /\\ ( inl ` S ) e. _V ) )' % A1b),
                   w.s([ccb, cne], 'jca', '( %s -> ( C e. NN0 /\\ C =/= R ) )' % A1b)], 'jca',
                  '( %s -> ( ( T e. Tbl /\\ R e. NN0 /\\ ( inl ` S ) e. _V ) /\\ ( C e. NN0 /\\ C =/= R ) ) )' % A1b),
              w.inst('sinupd2')], 'syl', '( %s -> ( %s ` C ) = ( T ` C ) )' % (A1b, UPDS))
    lhs2 = w.s([w.s([v2], 'fveq1d', '( %s -> ( %s ` C ) = ( %s ` C ) )' % (A1b, SIN, UPDS)), u2], 'eqtrd',
               '( %s -> ( %s ` C ) = ( T ` C ) )' % (A1b, SIN))
    cf = w.s([w.s([], 'simpr', '( %s -> -. C = R )' % A1b)], 'intnand', '( %s -> -. %s )' % (A1b, COND))
    rhs2 = w.s([cf], 'iffalsed', '( %s -> %s = ( T ` C ) )' % (A1b, RHS))
    e2 = w.s([lhs2, rhs2], 'eqtr4d', '( %s -> ( %s ` C ) = %s )' % (A1b, SIN, RHS))
    caseA = w.s([e1, e2], 'pm2.61dan', '( %s -> ( %s ` C ) = %s )' % (A1, SIN, RHS))
    # ---- case ( T ` R ) =/= NONE
    B1 = '( %s /\\ -. ( T ` R ) = %s )' % (T4, NONE)
    bh = w.s([], 'simpr', '( %s -> -. ( T ` R ) = %s )' % (B1, NONE))
    vB = w.s([w.s([val], 'adantr', '( %s -> %s = if ( ( T ` R ) = %s , %s , T ) )' % (B1, SIN, NONE, UPDS)),
              w.s([bh], 'iffalsed', '( %s -> if ( ( T ` R ) = %s , %s , T ) = T )' % (B1, NONE, UPDS))], 'eqtrd',
             '( %s -> %s = T )' % (B1, SIN))
    lhsB = w.s([vB], 'fveq1d', '( %s -> ( %s ` C ) = ( T ` C ) )' % (B1, SIN))
    cfB = w.s([bh], 'intnanrd', '( %s -> -. %s )' % (B1, COND))
    rhsB = w.s([cfB], 'iffalsed', '( %s -> %s = ( T ` C ) )' % (B1, RHS))
    caseB = w.s([lhsB, rhsB], 'eqtr4d', '( %s -> ( %s ` C ) = %s )' % (B1, SIN, RHS))
    w.qed([caseA, caseB], 'pm2.61dan', '( %s -> ( %s ` C ) = %s )' % (T4, SIN, RHS))
    run(w)

T3S = '( T e. Tbl /\\ R e. NN0 /\\ S e. Word NN0 )'

def sinap(w, A, c):
    """the sinapply instance at column c, applied under an antecedent A that
    carries T3S (as its own left conjunct) and c e. NN0"""
    return w.s([], 'sinapply', '( ( %s /\\ %s e. NN0 ) -> ( %s ` %s ) = if ( ( ( T ` R ) = %s /\\ %s = R ) , ( inl ` S ) , ( T ` %s ) ) )'
                % (T3S, c, SIN, c, NONE, c, c))

def inlne(w, A, sstep):
    z = w.s([w.s([], '0ex', '(/) e. _V')], 'a1i', '( %s -> (/) e. _V )' % A)
    return w.s([sstep, z, w.inst('inlneinr')], 'syl2anc', '( %s -> ( inl ` S ) =/= %s )' % (A, NONE))

# ------------------------------------------------------------------ sinpers
if not only or 'sinpers' in only:
    w = W('sinpers', 'A conditional table update leaves a nonempty entry alone (Lean: setIfNone_persist).')
    A = '( %s /\\ ( C e. NN0 /\\ ( T ` C ) =/= %s ) )' % (T3S, NONE)
    t3 = w.s([], 'simpl', '( %s -> %s )' % (A, T3S))
    cc = w.s([], 'simprl', '( %s -> C e. NN0 )' % A)
    nn = w.s([], 'simprr', '( %s -> ( T ` C ) =/= %s )' % (A, NONE))
    ap = w.s([w.s([t3, cc], 'jca', '( %s -> ( %s /\\ C e. NN0 ) )' % (A, T3S)), sinap(w, A, 'C')], 'syl',
             '( %s -> ( %s ` C ) = %s )' % (A, SIN, RHS))
    B = '( %s /\\ %s )' % (A, COND)
    h1 = w.s([], 'simprl', '( %s -> ( T ` R ) = %s )' % (B, NONE))
    h2 = w.s([], 'simprr', '( %s -> C = R )' % B)
    tc = w.s([w.s([h2], 'fveq2d', '( %s -> ( T ` C ) = ( T ` R ) )' % B), h1], 'eqtrd',
             '( %s -> ( T ` C ) = %s )' % (B, NONE))
    ncond = w.s([w.s([tc], 'ex', '( %s -> ( %s -> ( T ` C ) = %s ) )' % (A, COND, NONE)),
                 w.s([nn, w.inst('neneqd')], 'syl', '( %s -> -. ( T ` C ) = %s )' % (A, NONE))], 'mtod',
                '( %s -> -. %s )' % (A, COND))
    w.qed([ap, w.s([ncond], 'iffalsed', '( %s -> %s = ( T ` C ) )' % (A, RHS))], 'eqtrd',
          '( %s -> ( %s ` C ) = ( T ` C ) )' % (A, SIN))
    run(w)

# ------------------------------------------------------------------ sinnn
if not only or 'sinnn' in only:
    w = W('sinnn', 'A conditional table update keeps a nonempty entry nonempty.')
    A = '( %s /\\ ( C e. NN0 /\\ ( T ` C ) =/= %s ) )' % (T3S, NONE)
    p = w.s([], 'sinpers', '( %s -> ( %s ` C ) = ( T ` C ) )' % (A, SIN))
    nn = w.s([], 'simprr', '( %s -> ( T ` C ) =/= %s )' % (A, NONE))
    w.qed([p, nn], 'eqnetrd', '( %s -> ( %s ` C ) =/= %s )' % (A, SIN, NONE))
    run(w)

# ------------------------------------------------------------------ sinself
if not only or 'sinself' in only:
    w = W('sinself', 'A conditional table update fills the target residue (Lean: setIfNone_self).')
    rr = w.s([], 'simp2', '( %s -> R e. NN0 )' % T3S)
    ss = w.s([], 'simp3', '( %s -> S e. Word NN0 )' % T3S)
    RH = 'if ( ( ( T ` R ) = %s /\\ R = R ) , ( inl ` S ) , ( T ` R ) )' % NONE
    ap = w.s([w.s([w.s([], 'id', '( %s -> %s )' % (T3S, T3S)), rr], 'jca', '( %s -> ( %s /\\ R e. NN0 ) )' % (T3S, T3S)),
              sinap(w, T3S, 'R')], 'syl', '( %s -> ( %s ` R ) = %s )' % (T3S, SIN, RH))
    A1 = '( %s /\\ ( T ` R ) = %s )' % (T3S, NONE)
    ct = w.s([w.s([], 'simpr', '( %s -> ( T ` R ) = %s )' % (A1, NONE)),
              w.s([w.s([], 'eqid', 'R = R')], 'a1i', '( %s -> R = R )' % A1)], 'jca',
             '( %s -> ( ( T ` R ) = %s /\\ R = R ) )' % (A1, NONE))
    inn = inlne(w, A1, w.s([ss], 'adantr', '( %s -> S e. Word NN0 )' % A1))
    c1 = w.s([w.s([w.s([ap], 'adantr', '( %s -> ( %s ` R ) = %s )' % (A1, SIN, RH)),
                   w.s([ct], 'iftrued', '( %s -> %s = ( inl ` S ) )' % (A1, RH))], 'eqtrd',
                  '( %s -> ( %s ` R ) = ( inl ` S ) )' % (A1, SIN)), inn], 'eqnetrd',
             '( %s -> ( %s ` R ) =/= %s )' % (A1, SIN, NONE))
    B1 = '( %s /\\ -. ( T ` R ) = %s )' % (T3S, NONE)
    cf = w.s([w.s([], 'simpr', '( %s -> -. ( T ` R ) = %s )' % (B1, NONE))], 'intnanrd',
             '( %s -> -. ( ( T ` R ) = %s /\\ R = R ) )' % (B1, NONE))
    c2 = w.s([w.s([w.s([ap], 'adantr', '( %s -> ( %s ` R ) = %s )' % (B1, SIN, RH)),
                   w.s([cf], 'iffalsed', '( %s -> %s = ( T ` R ) )' % (B1, RH))], 'eqtrd',
                  '( %s -> ( %s ` R ) = ( T ` R ) )' % (B1, SIN)),
              w.s([w.s([], 'simpr', '( %s -> -. ( T ` R ) = %s )' % (B1, NONE)), w.inst('neqned')], 'syl',
                  '( %s -> ( T ` R ) =/= %s )' % (B1, NONE))], 'eqnetrd',
             '( %s -> ( %s ` R ) =/= %s )' % (B1, SIN, NONE))
    w.qed([c1, c2], 'pm2.61dan', '( %s -> ( %s ` R ) =/= %s )' % (T3S, SIN, NONE))
    run(w)

# ------------------------------------------------------------------ sincases
if not only or 'sincases' in only:
    w = W('sincases', 'Every nonempty entry after a conditional update is old or the new one (Lean: setIfNone_cases).')
    A = '( %s /\\ ( C e. NN0 /\\ ( %s ` C ) =/= %s ) )' % (T3S, SIN, NONE)
    CONC = '( ( T ` C ) = ( %s ` C ) \\/ ( C = R /\\ ( 2nd ` ( %s ` C ) ) = S ) )' % (SIN, SIN)
    t3 = w.s([], 'simpl', '( %s -> %s )' % (A, T3S))
    cc = w.s([], 'simprl', '( %s -> C e. NN0 )' % A)
    ss = w.s([t3], 'simp3d', '( %s -> S e. Word NN0 )' % A)
    ap = w.s([w.s([t3, cc], 'jca', '( %s -> ( %s /\\ C e. NN0 ) )' % (A, T3S)), sinap(w, A, 'C')], 'syl',
             '( %s -> ( %s ` C ) = %s )' % (A, SIN, RHS))
    A1 = '( %s /\\ %s )' % (A, COND)
    v1 = w.s([w.s([ap], 'adantr', '( %s -> ( %s ` C ) = %s )' % (A1, SIN, RHS)),
              w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, COND))], 'iftrued', '( %s -> %s = ( inl ` S ) )' % (A1, RHS))], 'eqtrd',
             '( %s -> ( %s ` C ) = ( inl ` S ) )' % (A1, SIN))
    pay = w.s([w.s([v1], 'fveq2d', '( %s -> ( 2nd ` ( %s ` C ) ) = ( 2nd ` ( inl ` S ) ) )' % (A1, SIN)),
               w.s([w.s([ss], 'adantr', '( %s -> S e. Word NN0 )' % A1), w.inst('alginl2')], 'syl',
                   '( %s -> ( 2nd ` ( inl ` S ) ) = S )' % A1)], 'eqtrd',
              '( %s -> ( 2nd ` ( %s ` C ) ) = S )' % (A1, SIN))
    c1 = w.s([w.s([w.s([w.s([], 'simpr', '( %s -> %s )' % (A1, COND))], 'simprd', '( %s -> C = R )' % A1), pay], 'jca',
                  '( %s -> ( C = R /\\ ( 2nd ` ( %s ` C ) ) = S ) )' % (A1, SIN))], 'olcd', '( %s -> %s )' % (A1, CONC))
    B1 = '( %s /\\ -. %s )' % (A, COND)
    v2 = w.s([w.s([ap], 'adantr', '( %s -> ( %s ` C ) = %s )' % (B1, SIN, RHS)),
              w.s([w.s([], 'simpr', '( %s -> -. %s )' % (B1, COND))], 'iffalsed', '( %s -> %s = ( T ` C ) )' % (B1, RHS))], 'eqtrd',
             '( %s -> ( %s ` C ) = ( T ` C ) )' % (B1, SIN))
    c2 = w.s([w.s([v2], 'eqcomd', '( %s -> ( T ` C ) = ( %s ` C ) )' % (B1, SIN))], 'orcd', '( %s -> %s )' % (B1, CONC))
    w.qed([c1, c2], 'pm2.61dan', '( %s -> %s )' % (A, CONC))
    run(w)
