#!/usr/bin/env python3
"""Sortie A1b: emit the definition block of sorties/a1b.mm (Algorithm.lean).

Writes the section header, the 47 $c declarations, their syntax axioms and
the df- statements.  Run once; it appends to the database named by MM_DB and
refuses to run twice (it checks for df-algrec).
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DB = os.path.join(ROOT, os.environ.get('MM_DB', 'carmichael.mm'))

# ---------------------------------------------------------------- expressions
W0 = 'Word NN0'
HD = '( c ` 0 )'
TL = '( c substr <. 1 , ( # ` c ) >. )'
B2 = '( 2o X. NN0 )'
WN = '( Word NN0 X. NN0 )'
N2 = '( NN0 X. NN0 )'
OPL = '( ( NN0 X. Word NN0 ) |_| 1o )'
OPN = '( ( ( NN0 X. Word NN0 ) |_| 1o ) X. NN0 )'
EX = '( Word NN0 X. ( NN0 X. ( Word NN0 X. Tbl ) ) )'
NONE = '( inr ` (/) )'


def P(*a):
    return '<. %s >.' % ' , '.join(a)


def IF(ph, a, b):
    return 'if ( %s , %s , %s )' % (ph, a, b)


def LET(v, e, body):
    return '( ( %s e. _V |-> %s ) ` %s )' % (v, body, e)


def STEP(dom, cod, clause, fixed=()):
    """( a1 e. D1 |-> ... ( h e. ( cod ^m dom ) , u e. NN0 |-> ( c e. dom |-> clause ) ) )"""
    s = '( h e. ( %s ^m %s ) , u e. NN0 |-> ( c e. %s |-> %s ) )' % (cod, dom, dom, clause)
    for v, d in reversed(fixed):
        s = '( %s e. %s |-> %s )' % (v, d, s)
    return s


def MPOSTEP(dom, cod, clause, a, da, b, db, rest=()):
    """two leading arguments as an operation, the remaining ones as mappings"""
    s = '( h e. ( %s ^m %s ) , u e. NN0 |-> ( c e. %s |-> %s ) )' % (cod, dom, dom, clause)
    for v, d in reversed(rest):
        s = '( %s e. %s |-> %s )' % (v, d, s)
    return '( %s e. %s , %s e. %s |-> %s )' % (a, da, b, db, s)


def FUN(dom, base, stepinst, level, ctuple):
    return '( ( ( ( g e. %s |-> %s ) AlgRec %s ) ` %s ) ` %s )' % (dom, base, stepinst, level, ctuple)


DEFS = []


def D(token, syn, label, body, syncom, com):
    DEFS.append((token, syn, label, body, syncom, com))


# ------------------------------------------------------------ infrastructure
D('AlgRec', 'calgrec', 'df-algrec',
  '( b e. _V , s e. _V |-> seq 0 ( s , ( k e. NN0 |-> if ( k = 0 , b , ( k - 1 ) ) ) ) )',
  'Syntax: primitive recursion on a fuel argument over a space of functions.',
  """Definition of the recursion operator of lean/Carmichael/Algorithm.lean.
     Every recursion of that file is structural on an explicit fuel or on a
     list ("All recursion is structural on an explicit fuel or on a list;
     there is no well-founded recursion, so every spec is a plain
     induction"), so the recursion depth is itself an argument and the
     function can be built by primitive recursion on it over the space of
     functions of the remaining arguments: ` ( B AlgRec S ) ` is the sequence
     of levels, level ` 0 ` being ` B ` and level ` N + 1 ` being
     ` ( level_N S N ) ` (~ algrec0 , ~ algrecp1 ).  The input function of
     ` seq ` serves two purposes at once, as ~ seq1 reads it only at ` 0 `
     and ~ seqp1 only above ` 0 `: at ` 0 ` it delivers the base level
     ` B `, and at ` N + 1 ` it delivers the index ` N `, which ~ seqp1
     hands to the step as its second operand (only the clause of ` dpGo `
     reads that index).  Unlike ~ df-tm2sa , no least fixed point and no
     monotonicity are needed, because the depth is an argument.""")

D('Tbl', 'ctbl', 'df-tbl', '( ( Word NN0 |_| 1o ) ^m NN0 )',
  'Syntax: the dynamic-programming table of step 4.',
  """Definition of the table of step 4.  Lean:
     abbrev Tbl := NN -> Option (List NN), "the DP table: residue |-> one
     witness list (a nonempty list of processed primes whose product has
     that residue), or none".  A total function on ` NN0 `, so that
     Function.update keeps it in ` Tbl `.""")

D('Scales', 'cscales', 'df-scales', '( ( ( NN X. NN0 ) X. ( NN X. NN0 ) ) X. NN0 )',
  'Syntax: the five integer scale parameters of step 1.',
  """Definition of the scale parameters of step 1.  Lean:
     structure Scales where (z : NN) (z99 : NN) (y : NN) (T : NN) (theta : NN),
     "z = ceil (C1 l2 l3)", "floor (z^(99/100)), the reservoir floor",
     "y = ceil (z^(1-E)), the smoothness bound", "T = ceil (3 l2) = |Q|",
     "theta = ceil ((log n)^1.2), the pool threshold".  A tuple
     ` <. <. <. z , z99 >. , <. y , T >. >. , th >. `: the first component is
     exactly the right-hand argument of ~ df-inwindow , so that
     ` <. <. C , E >. , n >. InWindow ( 1st ` sc ) ` is literal.  ` z ` and
     ` y ` are in ` NN ` because ` reservoir ` subtracts ` 1 ` from ` z ` and
     ` smoothTD ` from ` y `, and set.mm's subtraction is not truncated.""")

# ---------------------------------------------------------------- primitives
D('PrimeGoS', 'cprimegos', 'df-primegos',
  STEP('NN0', B2,
       IF('m < ( c x. c )', P('1o', '1'),
          IF('( m mod c ) = 0', P('(/)', '1'),
             P('( 1st ` ( h ` ( c + 1 ) ) )', '( ( 2nd ` ( h ` ( c + 1 ) ) ) + 1 )'))),
       fixed=[('m', 'NN0')]),
  'Syntax: the step clause of the trial-division loop (auxiliary to ~ df-primego ).',
  """Definition of the recursive clause of the trial-division loop.  Lean:
     def primeGo (m : NN) : NN -> NN -> Bool x. NN
     | _, 0 => (true, 0)
     | d, fuel + 1 =>
       if m < d * d then (true, 1)
       else if m % d = 0 then (false, 1)
       else let r := primeGo m (d + 1) fuel ; (r.1, r.2 + 1).
     ` ( H ( PrimeGoS ` M ) U ) ` is the function on the trial divisor ` c `
     given by the second clause with the recursive call made to ` H `; ` U `
     is the recursion index, unused here.  ` Bool ` is ` 2o `,
     ` true ` is ` 1o `, ` false ` is ` (/) `.""")

D('PrimeGo', 'cprimego', 'df-primego',
  '( m e. NN0 , d e. NN0 |-> ( f e. NN0 |-> %s ) )'
  % FUN('NN0', P('1o', '0'), '( PrimeGoS ` m )', 'f', 'd'),
  'Syntax: the trial-division loop of the primality test.',
  """Definition of the trial-division loop.  Lean: primeGo, quoted in
     ~ df-primegos : "tries d, d+1, ... while d * d <_ m; returns false at the
     first divisor.  Charges one unit per d tried (including the final one
     that fails d * d <_ m).  Fuel-exhaustion returns true with no charge."
     ` ( ( M PrimeGo D ) ` F ) = <. flag , cost >. `; the equation lemmas are
     ~ primego0 and ~ primegop1 .""")

D('IsPrimeTD', 'cisprimetd', 'df-isprimetd',
  '( m e. NN0 |-> %s )'
  % IF('m < 2', P('(/)', '1'),
       P('( 1st ` ( ( m PrimeGo 2 ) ` m ) )', '( ( 2nd ` ( ( m PrimeGo 2 ) ` m ) ) + 1 )')),
  'Syntax: primality by trial division.',
  """Definition of the primality test of the algorithm.  Lean:
     def isPrimeTD (m : NN) : Bool x. NN :=
       if m < 2 then (false, 1) else let r := primeGo m 2 m ; (r.1, r.2 + 1),
     "Primality by trial division: 2 <_ m and no divisor d with 2 <_ d,
     d * d <_ m.  Fuel m (the loop stops at d <_ Nat.sqrt m + 1 <_ m).
     Charges 1 plus the loop, so at most Nat.sqrt m + 1." """)

D('DivOutS', 'cdivouts', 'df-divouts',
  STEP('NN0', N2,
       IF('( c mod d ) = 0',
          P('( 1st ` ( h ` ( |_ ` ( c / d ) ) ) )',
            '( ( 2nd ` ( h ` ( |_ ` ( c / d ) ) ) ) + 1 )'),
          P('c', '0')),
       fixed=[('d', 'NN')]),
  'Syntax: the step clause of the divide-out loop (auxiliary to ~ df-divout ).',
  """Definition of the recursive clause of the divide-out loop.  Lean:
     def divOut (d : NN) : NN -> NN -> NN x. NN
     | r, 0 => (r, 0)
     | r, fuel + 1 =>
       if r % d = 0 then let s := divOut d (r / d) fuel ; (s.1, s.2 + 1)
       else (r, 0).
     Lean's Nat.div is ` ( |_ ` ( c / d ) ) `; the divisor is restricted to
     ` NN ` so that the clause is total (Lean totalises by r / 0 = 0 and
     r % 0 = r, and every call site has 2 <_ d).""")

D('DivOut', 'cdivout', 'df-divout',
  '( d e. NN , r e. NN0 |-> ( f e. NN0 |-> %s ) )'
  % FUN('NN0', P('g', '0'), '( DivOutS ` d )', 'f', 'r'),
  'Syntax: the divide-out loop of the smoothness test.',
  """Definition of the divide-out loop.  Lean: divOut, quoted in
     ~ df-divouts : "Divide d out of r while d || r (fuel-bounded).  Charges
     one unit per successful division; the failing test is charged to the
     caller's loop body."  Equation lemmas ~ divout0 , ~ divoutp1 .""")

D('SmoothGoS', 'csmoothgos', 'df-smoothgos',
  STEP('( NN X. NN0 )', N2,
       P('( 1st ` ( h ` <. ( ( 1st ` c ) + 1 ) , ( 1st ` ( ( ( 1st ` c ) DivOut ( 2nd ` c ) ) '
         '` ( 2nd ` c ) ) ) >. ) )',
         '( ( ( 2nd ` ( h ` <. ( ( 1st ` c ) + 1 ) , ( 1st ` ( ( ( 1st ` c ) DivOut ( 2nd ` c ) ) '
         '` ( 2nd ` c ) ) ) >. ) ) + ( 2nd ` ( ( ( 1st ` c ) DivOut ( 2nd ` c ) ) ` ( 2nd ` c ) ) ) ) + 1 )')),
  'Syntax: the step clause of the outer smoothness loop (auxiliary to ~ df-smoothgo ).',
  """Definition of the recursive clause of the outer loop of the smoothness
     test.  Lean:
     def smoothGo : NN -> NN -> NN -> NN x. NN
     | _, r, 0 => (r, 0)
     | d, r, fuel + 1 =>
       let s := divOut d r r ; let t := smoothGo (d + 1) s.1 fuel ;
       (t.1, t.2 + s.2 + 1).
     Both ` d ` and ` r ` change in the recursive call, so the parameter is
     the pair ` c = <. d , r >. `.""")

D('SmoothGo', 'csmoothgo', 'df-smoothgo',
  '( d e. NN , r e. NN0 |-> ( f e. NN0 |-> %s ) )'
  % FUN('( NN X. NN0 )', P('( 2nd ` g )', '0'), 'SmoothGoS', 'f', '<. d , r >.'),
  'Syntax: the outer loop of the smoothness test.',
  """Definition of the outer loop of the smoothness test.  Lean: smoothGo,
     quoted in ~ df-smoothgos : "Outer loop of smoothTD: for d, d+1, ...
     (fuel values) divide d out of r completely (inner fuel r).  Charges one
     unit per d plus the successful divisions."  Equation lemmas
     ~ smoothgo0 , ~ smoothgop1 .""")

D('SmoothTD', 'csmoothtd', 'df-smoothtd',
  '( y e. NN , k e. NN0 |-> %s )'
  % P(IF('( 1st ` ( ( 2 SmoothGo k ) ` ( y - 1 ) ) ) = 1', '1o', '(/)'),
      '( ( 2nd ` ( ( 2 SmoothGo k ) ` ( y - 1 ) ) ) + 1 )'),
  'Syntax: smoothness by trial division.',
  """Definition of the smoothness test.  Lean:
     def smoothTD (y k : NN) : Bool x. NN :=
       let s := smoothGo 2 k (y - 1) ; (s.1 == 1, s.2 + 1),
     "y-smoothness of k by trial division: divide out d = 2, ..., y and test
     whether 1 remains.  Charges 1 plus y - 1 outer bodies plus at most
     Nat.log 2 k successful divisions (each at least halves r >= 1), so at
     most y + Nat.log 2 k + 2."  Lean's truncated y - 1 is the integer
     ` ( y - 1 ) ` here, which agrees for ` 1 <_ y `; ` y ` is restricted to
     ` NN ` accordingly.  The boolean ` s.1 == 1 ` is
     ` if ( ... = 1 , 1o , (/) ) `.""")

D('MulAllS', 'cmulalls', 'df-mulalls',
  STEP(W0, WN,
       IF('c = (/)', P('(/)', '0'),
          P('( <" ( %s x. q ) "> ++ ( 1st ` ( h ` %s ) ) )' % (HD, TL),
            '( ( 2nd ` ( h ` %s ) ) + 1 )' % TL)),
       fixed=[('q', 'NN0')]),
  'Syntax: the step clause of the scaling map (auxiliary to ~ df-mulall ).',
  """Definition of the recursive clause of the scaling map.  Lean:
     def mulAll (q : NN) : List NN -> List NN x. NN
     | [] => ([], 0)
     | d :: ds => let r := mulAll q ds ; (d * q :: r.1, r.2 + 1),
     "ds.map (. * q), charging one unit per element".  A ` List NN ` is a
     ` Word NN0 `: the empty list is ` (/) `, the head of ` c ` is
     ` ( c ` 0 ) `, its tail is ` ( c substr <. 1 , ( # ` c ) >. ) ` and
     ` d :: l ` is ` ( <" d "> ++ l ) `.  The recursion index of the level is
     the length of the list.""")

D('MulAll', 'cmulall', 'df-mulall',
  '( q e. NN0 , l e. %s |-> %s )'
  % (W0, FUN(W0, P('(/)', '0'), '( MulAllS ` q )', '( # ` l )', 'l')),
  'Syntax: the scaling map of the divisor enumeration.',
  """Definition of the scaling map.  Lean: mulAll, quoted in ~ df-mulalls .
     Equation lemmas ~ mulall0 (the empty list) and ~ mulallcs (a cons).""")

D('DivisorsOfS', 'cdivisorsofs', 'df-divisorsofs',
  STEP(W0, WN,
       IF('c = (/)', P('<" 1 ">', '0'),
          P('( ( 1st ` ( h ` %s ) ) ++ ( 1st ` ( %s MulAll ( 1st ` ( h ` %s ) ) ) ) )' % (TL, HD, TL),
            '( ( 2nd ` ( h ` %s ) ) + ( 2nd ` ( %s MulAll ( 1st ` ( h ` %s ) ) ) ) )' % (TL, HD, TL)))),
  'Syntax: the step clause of the divisor enumeration (auxiliary to ~ df-divisorsof ).',
  """Definition of the recursive clause of the divisor enumeration.  Lean:
     def divisorsOf : List NN -> List NN x. NN
     | [] => ([1], 0)
     | q :: Q => let r := divisorsOf Q ; let s := mulAll q r.1 ;
                 (r.1 ++ s.1, r.2 + s.2),
     "All subset products of Q (the divisors of Q.prod when Q is a list of
     distinct primes), as a list of length 2 ^ Q.length: ds := [1], then for
     each q, ds := ds ++ ds.map (. * q).  Charges one unit per
     multiplication, 2 ^ Q.length - 1 in total." """)

D('DivisorsOf', 'cdivisorsof', 'df-divisorsof',
  '( l e. %s |-> %s )' % (W0, FUN(W0, P('<" 1 ">', '0'), 'DivisorsOfS', '( # ` l )', 'l')),
  'Syntax: the divisor enumeration of step 3.',
  """Definition of the divisor enumeration.  Lean: divisorsOf, quoted in
     ~ df-divisorsofs .  Equation lemmas ~ divisorsof0 , ~ divisorsofcs .""")

D('CoprimeToS', 'ccoprimetos', 'df-coprimetos',
  STEP(W0, B2,
       IF('c = (/)', P('1o', '0'),
          IF('( k mod %s ) = 0' % HD, P('(/)', '1'),
             P('( 1st ` ( h ` %s ) )' % TL, '( ( 2nd ` ( h ` %s ) ) + 1 )' % TL))),
       fixed=[('k', 'NN0')]),
  'Syntax: the step clause of the coprimality test (auxiliary to ~ df-coprimeto ).',
  """Definition of the recursive clause of the coprimality test.  Lean:
     def coprimeTo : List NN -> NN -> Bool x. NN
     | [], _ => (true, 0)
     | q :: Q, k => if k % q = 0 then (false, 1)
                    else let r := coprimeTo Q k ; (r.1, r.2 + 1),
     "for all q e. Q, q does not divide k, with early exit.  Charges one unit
     per q tested, at most Q.length." """)

D('CoprimeTo', 'ccoprimeto', 'df-coprimeto',
  '( l e. %s , k e. NN0 |-> %s )'
  % (W0, FUN(W0, P('1o', '0'), '( CoprimeToS ` k )', '( # ` l )', 'l')),
  'Syntax: the coprimality test of step 3.',
  """Definition of the coprimality test.  Lean: coprimeTo, quoted in
     ~ df-coprimetos .  Equation lemmas ~ coprimeto0 , ~ coprimetocs .""")

D('ProdLS', 'cprodls', 'df-prodls',
  STEP(W0, N2,
       IF('c = (/)', P('1', '0'),
          P('( %s x. ( 1st ` ( h ` %s ) ) )' % (HD, TL),
            '( ( 2nd ` ( h ` %s ) ) + 1 )' % TL))),
  'Syntax: the step clause of the list product (auxiliary to ~ df-prodl ).',
  """Definition of the recursive clause of the list product.  Lean:
     def prodL : List NN -> NN x. NN
     | [] => (1, 0)
     | p :: S => let r := prodL S ; (p * r.1, r.2 + 1),
     "The product of a list, charging one unit per multiplication (S.length
     in total)." """)

D('ProdL', 'cprodl', 'df-prodl',
  '( l e. %s |-> %s )' % (W0, FUN(W0, P('1', '0'), 'ProdLS', '( # ` l )', 'l')),
  'Syntax: the list product with its operation count.',
  """Definition of the list product.  Lean: prodL, quoted in ~ df-prodls .
     Equation lemmas ~ prodl0 , ~ prodlcs .""")

# ------------------------------------------------------------------- step 2
RESPR = '( IsPrimeTD ` c )'
RESSM = '( y SmoothTD ( c - 1 ) )'
RESKEEP = IF('z < c', IF('( 1st ` %s ) = 1o' % RESPR, '( 1st ` %s )' % RESSM, '(/)'), '(/)')
RESH = '( h ` ( c + 1 ) )'

D('ResGoS', 'cresgos', 'df-resgos',
  MPOSTEP('NN', WN,
          P(IF('%s = 1o' % RESKEEP, '( <" c "> ++ ( 1st ` %s ) )' % RESH, '( 1st ` %s )' % RESH),
            '( ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % (RESH, RESPR, RESSM)),
          'z', 'NN0', 'y', 'NN'),
  'Syntax: the step clause of the reservoir loop (auxiliary to ~ df-resgo ).',
  """Definition of the recursive clause of the reservoir loop of step 2.
     Lean:
     def resGo (z99 y : NN) : NN -> NN -> List NN x. NN
     | _, 0 => ([], 0)
     | q, fuel + 1 =>
       let pr := isPrimeTD q ; let sm := smoothTD y (q - 1) ;
       let rest := resGo z99 y (q + 1) fuel ;
       let keep := if z99 < q then pr.1 && sm.1 else false ;
       ((if keep then q :: rest.1 else rest.1), rest.2 + pr.2 + sm.2 + 1),
     "for q, q+1, ... (fuel values, ascending) keep q iff z99 < q,
     isPrimeTD q, smoothTD y (q - 1).  Charges one unit per q plus the two
     tests (both always run)."  Lean's b && c is
     ` if ( b = 1o , c , (/) ) `; the trial divisor ` q ` is restricted to
     ` NN ` so that ` ( q - 1 ) ` is a nonnegative integer, as Lean's
     truncated subtraction gives.""")

D('ResGo', 'cresgo', 'df-resgo',
  '( z e. NN0 , y e. NN |-> ( q e. NN |-> ( f e. NN0 |-> %s ) ) )'
  % FUN('NN', P('(/)', '0'), '( z ResGoS y )', 'f', 'q'),
  'Syntax: the reservoir loop of step 2.',
  """Definition of the reservoir loop.  Lean: resGo, quoted in ~ df-resgos .
     Equation lemmas ~ resgo0 , ~ resgop1 .""")

D('Reservoir', 'creservoir', 'df-reservoir',
  '( z e. NN , w e. NN0 |-> ( y e. NN |-> ( ( ( w ResGo y ) ` 2 ) ` ( z - 1 ) ) ) )',
  'Syntax: step 2 of the algorithm, the reservoir of smooth-shifted primes.',
  """Definition of step 2.  Lean:
     def reservoir (z z99 y : NN) : List NN x. NN := resGo z99 y 2 (z - 1),
     "the primes q e. (z99, z] with q - 1 being y-smooth, in ascending order
     (q = 2, ..., z, fuel z - 1).  Charges at most
     (z - 1) * (Nat.sqrt z + y + Nat.log 2 z + 4)."  ` z ` is restricted to
     ` NN ` so that the fuel ` ( z - 1 ) ` is a nonnegative integer.""")

# ------------------------------------------------------------------- step 3
PGP = '( ( ( c ` 0 ) x. k ) + 1 )'
PGPR = '( IsPrimeTD ` %s )' % PGP
PGH = '( h ` %s )' % TL

D('PoolGoS', 'cpoolgos', 'df-poolgos',
  MPOSTEP(W0, WN,
          IF('c = (/)', P('(/)', '0'),
             IF('( %s <_ x /\\ z < %s )' % (PGP, PGP),
                P(IF('( 1st ` %s ) = 1o' % PGPR,
                     '( <" %s "> ++ ( 1st ` %s ) )' % (PGP, PGH), '( 1st ` %s )' % PGH),
                  '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (PGH, PGPR)),
                P('( 1st ` %s )' % PGH, '( ( 2nd ` %s ) + 1 )' % PGH))),
          'x', 'NN0', 'z', 'NN0', rest=[('k', 'NN0')]),
  'Syntax: the step clause of the pool loop (auxiliary to ~ df-poolgo ).',
  """Definition of the recursive clause of the pool loop of step 3.  Lean:
     def poolGo (x z k : NN) : List NN -> List NN x. NN
     | [] => ([], 0)
     | d :: ds =>
       let p := d * k + 1 ; let rest := poolGo x z k ds ;
       if p <_ x /\\ z < p then
         let pr := isPrimeTD p ;
         ((if pr.1 then p :: rest.1 else rest.1), rest.2 + pr.2 + 1)
       else (rest.1, rest.2 + 1),
     "for each divisor d, p := d * k + 1; keep p iff p <_ x, z < p,
     isPrimeTD p.  Charges one unit per d plus the primality test, which runs
     only when p <_ x (so costs <_ Nat.sqrt x + 1)." """)

D('PoolGo', 'cpoolgo', 'df-poolgo',
  '( x e. NN0 , z e. NN0 |-> ( k e. NN0 |-> ( l e. %s |-> %s ) ) )'
  % (W0, FUN(W0, P('(/)', '0'), '( ( x PoolGoS z ) ` k )', '( # ` l )', 'l')),
  'Syntax: the pool loop of step 3.',
  """Definition of the pool loop.  Lean: poolGo, quoted in ~ df-poolgos .
     Equation lemmas ~ poolgo0 , ~ poolgocs .""")

PALG = '( ( ( x PoolGo z ) ` k ) ` ( 1st ` ( DivisorsOf ` q ) ) )'
D('PoolAlg', 'cpoolalg', 'df-poolalg',
  '( q e. %s , x e. NN0 |-> ( z e. NN0 |-> ( k e. NN0 |-> %s ) ) )'
  % (W0, P('( 1st ` %s )' % PALG,
           '( ( 2nd ` ( DivisorsOf ` q ) ) + ( 2nd ` %s ) )' % PALG)),
  'Syntax: the pool of step 3.',
  """Definition of the pool of step 3.  Lean:
     def poolAlg (Q : List NN) (x z k : NN) : List NN x. NN :=
       let ds := divisorsOf Q ; let r := poolGo x z k ds.1 ; (r.1, ds.2 + r.2),
     "Step 3 pool P_k = {d k + 1 : d || L, d k + 1 <_ x, d k + 1 prime,
     z < d k + 1} with d ranging over divisorsOf Q.  Charges divisorsOf plus
     the loop: at most 2 ^ Q.length * (Nat.sqrt x + 3)." """)

SCP = '( q CoprimeTo c )'
SPA = '( ( ( q PoolAlg x ) ` z ) ` c )'
SRC = '( h ` ( c + 1 ) )'
D('ScanS', 'cscans', 'df-scans',
  MPOSTEP('NN0', OPN,
          IF('( 1st ` %s ) = 1o' % SCP,
             IF('o <_ ( # ` ( 1st ` %s ) )' % SPA,
                P('( inl ` <. c , ( 1st ` %s ) >. )' % SPA,
                  '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (SCP, SPA)),
                P('( 1st ` %s )' % SRC,
                  '( ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % (SRC, SCP, SPA))),
             P('( 1st ` %s )' % SRC,
               '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (SRC, SCP))),
          'q', W0, 'x', 'NN0', rest=[('z', 'NN0'), ('o', 'NN0')]),
  'Syntax: the step clause of the scan for the shift (auxiliary to ~ df-scan ).',
  """Definition of the recursive clause of the scan of step 3.  Lean:
     def scan (Q : List NN) (x z theta : NN) : NN -> NN ->
         Option (NN x. List NN) x. NN
     | _, 0 => (none, 0)
     | k, fuel + 1 =>
       let cp := coprimeTo Q k ;
       if cp.1 then
         let P := poolAlg Q x z k ;
         if theta <_ P.1.length then (some (k, P.1), cp.2 + P.2 + 1)
         else let r := scan Q x z theta (k + 1) fuel ;
              (r.1, r.2 + cp.2 + P.2 + 1)
       else let r := scan Q x z theta (k + 1) fuel ; (r.1, r.2 + cp.2 + 1),
     "The scan for k: for k, k+1, ... (fuel values) return the first
     (k, P_k) with coprimeTo Q k and theta <_ P_k.length.  Charges one unit
     per k plus coprimeTo plus (when coprime) poolAlg."  ` theta ` is the set
     variable ` o `; ` some ` is ` inl `, ` none ` is ` ( inr ` (/) ) `.""")

D('Scan', 'cscan', 'df-scan',
  '( q e. %s , x e. NN0 |-> ( z e. NN0 |-> ( o e. NN0 |-> ( k e. NN0 |-> ( f e. NN0 |-> %s ) ) ) ) )'
  % (W0, FUN('NN0', P(NONE, '0'), '( ( ( q ScanS x ) ` z ) ` o )', 'f', 'k')),
  'Syntax: the scan of step 3 for an accepted shift.',
  """Definition of the scan of step 3.  Lean: scan, quoted in ~ df-scans .
     Equation lemmas ~ scan0 , ~ scanp1 .""")

# ------------------------------------------------------------------- step 4
D('EmptyTbl', 'cemptytbl', 'df-emptytbl', '( r e. NN0 |-> ( inr ` (/) ) )',
  'Syntax: the empty dynamic-programming table.',
  """Definition of the empty table.  Lean:
     def emptyTbl : Tbl := fun _ => none.""")

D('SetIfNone', 'csetifnone', 'df-setifnone',
  '( t e. Tbl , r e. NN0 |-> ( w e. %s |-> %s ) )'
  % (W0, IF('( t ` r ) = ( inr ` (/) )',
            '( ( t |` ( NN0 \\ { r } ) ) u. { <. r , ( inl ` w ) >. } )', 't')),
  'Syntax: the guarded table write of step 4.',
  """Definition of the guarded table write.  Lean:
     def setIfNone (t : Tbl) (r : NN) (W : List NN) : Tbl :=
       match t r with
       | none => Function.update t r (some W)
       | some _ => t,
     "Write W at residue r if that entry is empty (one read, one write)."
     Function.update is
     ` ( ( t |` ( NN0 \\ { r } ) ) u. { <. r , x >. } ) `, as in the machine
     model.""")

DPAC = IF('( t ` u ) = ( inr ` (/) )', 'c',
          '( ( c SetIfNone ( ( u x. p ) mod l ) ) ` ( <" p "> ++ ( 2nd ` ( t ` u ) ) ) )')
D('DpGoS', 'cdpgos', 'df-dpgos',
  MPOSTEP('Tbl', '( Tbl X. NN0 )',
          P('( 1st ` ( h ` %s ) )' % DPAC, '( ( 2nd ` ( h ` %s ) ) + 1 )' % DPAC),
          'l', 'NN', 'p', 'NN0', rest=[('t', 'Tbl')]),
  'Syntax: the step clause of the dynamic-programming loop (auxiliary to ~ df-dpgo ).',
  """Definition of the recursive clause of the dynamic-programming loop of
     step 4.  Lean:
     def dpGo (L p : NN) (t : Tbl) : NN -> Tbl -> Tbl x. NN
     | 0, acc => (acc, 0)
     | r + 1, acc =>
       let acc' := match t r with
                   | none => acc
                   | some W => setIfNone acc ((r * p) % L) (p :: W) ;
       let res := dpGo L p t r acc' ; (res.1, res.2 + 1),
     "for r = fuel - 1, ..., 0, if the SNAPSHOT t has a witness W at r, write
     p :: W at (r * p) % L into the accumulator (if empty).  Charges one unit
     per r."  This is the one clause that reads the recursion index: the
     ` r ` of Lean's pattern ` r + 1 ` is the index ` u ` of ~ df-algrec .
     The payload ` W ` of a ` some ` is its second projection (~ algdjun ).
     The modulus ` l ` is restricted to ` NN `, where set.mm's ` mod ` agrees
     with Lean's.""")

DPDG = '( ( ( ( l DpGo p ) ` t ) ` l ) ` ( ( t SetIfNone ( p mod l ) ) ` <" p "> ) )'
D('DpGo', 'cdpgo', 'df-dpgo',
  '( l e. NN , p e. NN0 |-> ( t e. Tbl |-> ( f e. NN0 |-> ( a e. Tbl |-> %s ) ) ) )'
  % FUN('Tbl', P('g', '0'), '( ( l DpGoS p ) ` t )', 'f', 'a'),
  'Syntax: the dynamic-programming loop of step 4.',
  """Definition of the dynamic-programming loop.  Lean: dpGo, quoted in
     ~ df-dpgos .  Equation lemmas ~ dpgo0 , ~ dpgop1 .""")

D('DpStep', 'cdpstep', 'df-dpstep',
  '( l e. NN , p e. NN0 |-> ( t e. Tbl |-> %s ) )'
  % P('( 1st ` %s )' % DPDG, '( ( 2nd ` %s ) + 1 )' % DPDG),
  'Syntax: one dynamic-programming step of step 4.',
  """Definition of one dynamic-programming step.  Lean:
     def dpStep (L p : NN) (t : Tbl) : Tbl x. NN :=
       let res := dpGo L p t L (setIfNone t (p % L) [p]) ; (res.1, res.2 + 1),
     "One DP step: process the prime p.  Start from t with [p] written at
     p % L (if empty), then extend every witness of the snapshot t by p.
     Charges exactly L + 1." """)

PP = '( 1st ` c )'
MM = '( 1st ` ( 2nd ` c ) )'
UU = '( 1st ` ( 2nd ` ( 2nd ` c ) ) )'
TT = '( 2nd ` ( 2nd ` ( 2nd ` c ) ) )'
ST = '( ( l DpStep ( %s ` 0 ) ) ` %s )' % (PP, TT)
ST1 = '( 1st ` %s )' % ST
SS = '( 2nd ` ( %s ` ( 1 mod l ) ) )' % ST1
PR = '( ProdL ` %s )' % SS
MQ = '( %s x. ( 1st ` %s ) )' % (MM, PR)
PTL = '( %s substr <. 1 , ( # ` %s ) >. )' % (PP, PP)
R1 = '( h ` <. %s , <. %s , <. %s , %s >. >. >. )' % (PTL, MM, UU, ST1)
R2 = '( h ` <. %s , <. %s , <. ( %s ++ %s ) , EmptyTbl >. >. >. )' % (PTL, MQ, SS, UU)

D('ExtractGoS', 'cextractgos', 'df-extractgos',
  MPOSTEP(EX, OPN,
          IF('%s = (/)' % PP, P(NONE, '0'),
             IF('( %s ` ( 1 mod l ) ) = ( inr ` (/) )' % ST1,
                P('( 1st ` %s )' % R1,
                  '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (R1, ST)),
                IF('n < %s' % MQ,
                   P('( inl ` <. %s , ( %s ++ %s ) >. )' % (MQ, SS, UU),
                     '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (ST, PR)),
                   P('( 1st ` %s )' % R2,
                     '( ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 1 )' % (R2, ST, PR))))),
          'l', 'NN', 'n', 'NN0'),
  'Syntax: the step clause of the extraction loop (auxiliary to ~ df-extractgo ).',
  """Definition of the recursive clause of the extraction loop of step 4.
     Lean:
     def extractGo (L n : NN) : List NN -> NN -> List NN -> Tbl ->
         Option (NN x. List NN) x. NN
     | [], _, _, _ => (none, 0)
     | p :: P, m, used, t =>
       let st := dpStep L p t ;
       match st.1 (1 % L) with
       | none => let res := extractGo L n P m used st.1 ;
                 (res.1, res.2 + st.2 + 1)
       | some S =>
         let pr := prodL S ; let m' := m * pr.1 ;
         if n < m' then (some (m', S ++ used), st.2 + pr.2 + 1)
         else let res := extractGo L n P m' (S ++ used) emptyTbl ;
              (res.1, res.2 + st.2 + pr.2 + 1),
     "state (m, used, t); at prime p run dpStep; if residue 1 % L now has a
     witness S, multiply m by S.prod, prepend S to used, reset the table, and
     return some (m, used) as soon as n < m.  Charges dpStep plus one unit
     per p, plus prodL S on a hit."  Four arguments change in the recursive
     call, so the parameter is the tuple
     ` c = <. P , <. m , <. used , t >. >. >. `; the payload ` S ` of the
     ` some ` is its second projection (~ algdjun ).""")

D('ExtractGo', 'cextractgo', 'df-extractgo',
  '( l e. NN , n e. NN0 |-> ( p e. %s |-> ( m e. NN0 |-> ( v e. %s |-> ( t e. Tbl |-> %s ) ) ) ) )'
  % (W0, W0, FUN(EX, P(NONE, '0'), '( l ExtractGoS n )', '( # ` p )',
                 '<. p , <. m , <. v , t >. >. >.')),
  'Syntax: the extraction loop of step 4.',
  """Definition of the extraction loop.  Lean: extractGo, quoted in
     ~ df-extractgos .  Equation lemmas ~ extractgo0 , ~ extractgocs .""")

D('Extract', 'cextract', 'df-extract',
  '( l e. NN , n e. NN0 |-> ( p e. %s |-> ( ( ( ( ( l ExtractGo n ) ` p ) ` 1 ) ` (/) ) ` EmptyTbl ) ) )' % W0,
  'Syntax: step 4 of the algorithm, the greedy extraction.',
  """Definition of step 4.  Lean:
     def extract (L n : NN) (P : List NN) : Option (NN x. List NN) x. NN :=
       extractGo L n P 1 [] emptyTbl,
     "greedy extraction of subsets of P with product == 1 (mod L) until the
     running product exceeds n; returns (m, S) with m = S.prod, or none if P
     is exhausted first.  Charges at most P.length * (L + 3)." """)

# ------------------------------------------------------------------- step 5
NMH = '( h ` %s )' % TL
D('NotMemS', 'cnotmems', 'df-notmems',
  STEP(W0, B2,
       IF('c = (/)', P('1o', '0'),
          P(IF('p = %s' % HD, '(/)', '( 1st ` %s )' % NMH),
            '( ( 2nd ` %s ) + 1 )' % NMH)),
       fixed=[('p', 'NN0')]),
  'Syntax: the step clause of the non-membership test (auxiliary to ~ df-notmemtd ).',
  """Definition of the recursive clause of the non-membership test of step 5.
     Lean:
     def notMemTD (p : NN) : List NN -> Bool x. NN
     | [] => (true, 0)
     | q :: S => let r := notMemTD p S ;
                 ((if p = q then false else r.1), r.2 + 1),
     "p not in S, charging one unit per element of S." """)

D('NotMemTD', 'cnotmemtd', 'df-notmemtd',
  '( p e. NN0 , l e. %s |-> %s )'
  % (W0, FUN(W0, P('1o', '0'), '( NotMemS ` p )', '( # ` l )', 'l')),
  'Syntax: the non-membership test of step 5.',
  """Definition of the non-membership test.  Lean: notMemTD, quoted in
     ~ df-notmems .  Equation lemmas ~ notmemtd0 , ~ notmemtdcs .""")

NDNM = '( %s NotMemTD %s )' % (HD, TL)
D('NodupS', 'cnodups', 'df-nodups',
  STEP(W0, B2,
       IF('c = (/)', P('1o', '0'),
          P(IF('( 1st ` %s ) = 1o' % NDNM, '( 1st ` %s )' % NMH, '(/)'),
            '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (NDNM, NMH))),
       ),
  'Syntax: the step clause of the distinctness test (auxiliary to ~ df-noduptd ).',
  """Definition of the recursive clause of the distinctness test of step 5.
     Lean:
     def nodupTD : List NN -> Bool x. NN
     | [] => (true, 0)
     | p :: S => let a := notMemTD p S ; let r := nodupTD S ;
                 (a.1 && r.1, a.2 + r.2 + 1),
     "S.Nodup by pairwise comparison.  Charges at most
     S.length * (S.length + 1)." """)

D('NodupTD', 'cnoduptd', 'df-noduptd',
  '( l e. %s |-> %s )' % (W0, FUN(W0, P('1o', '0'), 'NodupS', '( # ` l )', 'l')),
  'Syntax: the distinctness test of step 5.',
  """Definition of the distinctness test.  Lean: nodupTD, quoted in
     ~ df-nodups .  Equation lemmas ~ noduptd0 , ~ noduptdcs .""")

APIP = '( IsPrimeTD ` %s )' % HD
D('AllPrimeS', 'callprimes', 'df-allprimes',
  STEP(W0, B2,
       IF('c = (/)', P('1o', '0'),
          P(IF('( 1st ` %s ) = 1o' % APIP, '( 1st ` %s )' % NMH, '(/)'),
            '( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + 1 )' % (APIP, NMH)))),
  'Syntax: the step clause of the all-primes test (auxiliary to ~ df-allprimetd ).',
  """Definition of the recursive clause of the all-primes test of step 5.
     Lean:
     def allPrimeTD : List NN -> Bool x. NN
     | [] => (true, 0)
     | p :: S => let a := isPrimeTD p ; let r := allPrimeTD S ;
                 (a.1 && r.1, a.2 + r.2 + 1),
     "for all p e. S, isPrimeTD p.  Charges one unit per element plus the
     tests." """)

D('AllPrimeTD', 'callprimetd', 'df-allprimetd',
  '( l e. %s |-> %s )' % (W0, FUN(W0, P('1o', '0'), 'AllPrimeS', '( # ` l )', 'l')),
  'Syntax: the all-primes test of step 5.',
  """Definition of the all-primes test.  Lean: allPrimeTD, quoted in
     ~ df-allprimes .  Equation lemmas ~ allprimetd0 , ~ allprimetdcs .""")

D('KorseltS', 'ckorselts', 'df-korselts',
  STEP(W0, B2,
       IF('c = (/)', P('1o', '0'),
          P(IF('( ( m - 1 ) mod ( %s - 1 ) ) = 0' % HD, '( 1st ` %s )' % NMH, '(/)'),
            '( ( 2nd ` %s ) + 1 )' % NMH)),
       fixed=[('m', 'NN0')]),
  'Syntax: the step clause of the Korselt test (auxiliary to ~ df-korselttd ).',
  """Definition of the recursive clause of the Korselt test of step 5.  Lean:
     def korseltTD (m : NN) : List NN -> Bool x. NN
     | [] => (true, 0)
     | p :: S => let r := korseltTD m S ;
                 ((if (m - 1) % (p - 1) = 0 then r.1 else false), r.2 + 1),
     "Korselt's condition for all p e. S, (p - 1) || (m - 1).  Charges one
     unit per element."  The two truncated subtractions are the integer ones;
     they agree with Lean's for ` 1 <_ m ` and ` 1 <_ p `, and the test is a
     condition of an ` if `, so the clause is total without a restriction.""")

D('KorseltTD', 'ckorselttd', 'df-korselttd',
  '( m e. NN0 , l e. %s |-> %s )'
  % (W0, FUN(W0, P('1o', '0'), '( KorseltS ` m )', '( # ` l )', 'l')),
  'Syntax: the Korselt test of step 5.',
  """Definition of the Korselt test.  Lean: korseltTD, quoted in
     ~ df-korselts .  Equation lemmas ~ korselttd0 , ~ korselttdcs .""")

ND = '( NodupTD ` l )'
AP = '( AllPrimeTD ` l )'
PD = '( ProdL ` l )'
KO = '( m KorseltTD l )'
OK = IF('( 1st ` %s ) = 1o' % ND,
        IF('( 1st ` %s ) = 1o' % AP,
           IF('%s = 1o' % IF('( 1st ` %s ) = m' % PD, '1o', '(/)'), '( 1st ` %s )' % KO, '(/)'),
           '(/)'),
        '(/)')
D('Verify', 'cverify', 'df-verify',
  '( m e. NN0 , l e. %s |-> %s )'
  % (W0, P(IF('3 <_ ( # ` l )', OK, '(/)'),
           '( ( ( ( ( 2nd ` %s ) + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + ( 2nd ` %s ) ) + 2 )'
           % (ND, AP, PD, KO))),
  'Syntax: step 5 of the algorithm, the output certificate.',
  """Definition of step 5.  Lean:
     def verify (m : NN) (S : List NN) : Bool x. NN :=
       let nd := nodupTD S ; let pr := allPrimeTD S ; let pd := prodL S ;
       let ko := korseltTD m S ;
       let ok := nd.1 && pr.1 && (pd.1 == m) && ko.1 ;
       ((if 3 <_ S.length then ok else false),
        nd.2 + pr.2 + pd.2 + ko.2 + 2),
     "certify (m, S): S.Nodup, every p e. S prime, S.prod = m,
     3 <_ S.length, and Korselt's condition.  All five checks run; charges
     their sum plus 2, at most S.length * (Nat.sqrt x + S.length + 5) + 2
     when every p e. S is <_ x."  Lean's b && c is
     ` if ( b = 1o , c , (/) ) ` and a == b is
     ` if ( a = b , 1o , (/) ) `, so the third conjunct of ok appears as
     ` if ( if ( pd.1 = m , 1o , (/) ) = 1o , ko.1 , (/) ) `, the literal
     transcription.""")

# ------------------------------------------------------------------ assembly
D('ScalesOf', 'cscalesof', 'df-scalesof',
  '( c e. RR , e e. RR |-> ( n e. NN0 |-> <. <. <. ( c zscale n ) , '
  '( Nfloor ` ( ( c zscale n ) ^c ( ; 9 9 / ; ; 1 0 0 ) ) ) >. , '
  '<. ( ( c yscaleE n ) ` e ) , ( Tscale ` n ) >. >. , '
  '( Nceil ` ( ( log ` n ) ^c ( 6 / 5 ) ) ) >. ) )',
  'Syntax: step 1 of the algorithm, the scales at the constants.',
  """Definition of step 1.  Lean:
     noncomputable def scalesOf (C1 E : RR) (n : NN) : Scales :=
       <. zscale C1 n, floor ((zscale C1 n : RR) ^ ((99 : RR) / 100)),
          yscaleE C1 n E, Tscale n, ceil ((Real.log n) ^ (1.2 : RR)) >.,
     "the scales of the paper at constants C1, E.  This is the only place the
     real-valued constants enter."  The five components are tupled as in
     ~ df-scales ; ` zscale `, ` yscaleE `, ` Tscale `, ` Nceil ` and
     ` Nfloor ` are the definitions of the scales block, and Lean's 1.2 is
     ` ( 6 / 5 ) `.""")

SZ = '( 1st ` ( 1st ` ( 1st ` s ) ) )'
SW = '( 2nd ` ( 1st ` ( 1st ` s ) ) )'
SY = '( 1st ` ( 2nd ` ( 1st ` s ) ) )'
STT = '( 2nd ` ( 2nd ` ( 1st ` s ) ) )'
SH = '( 2nd ` s )'
C2 = '( ( ( ( 2nd ` r ) + %s ) + ( 2nd ` g ) ) + 2 )' % STT
SUCC = P(IF('( 1st ` v ) = 1o',
            '( inl ` <. ( 1st ` ( 2nd ` ( 1st ` w ) ) ) , ( 2nd ` ( 2nd ` ( 1st ` w ) ) ) >. )',
            NONE),
         '( ( ( e + ( 2nd ` j ) ) + ( 2nd ` w ) ) + ( 2nd ` v ) )')
MATCH2 = IF('( 1st ` w ) = ( inr ` (/) )',
            P(NONE, '( ( e + ( 2nd ` j ) ) + ( 2nd ` w ) )'),
            LET('v', '( ( 1st ` ( 2nd ` ( 1st ` w ) ) ) Verify ( 2nd ` ( 2nd ` ( 1st ` w ) ) ) )', SUCC))
MATCH1 = IF('( 1st ` j ) = ( inr ` (/) )',
            P(NONE, '( e + ( 2nd ` j ) )'),
            LET('p', '( 2nd ` ( 2nd ` ( 1st ` j ) ) )',
                LET('w', '( ( a Extract n ) ` p )', MATCH2)))
INNER = LET('q', '( ( 1st ` r ) substr <. ( i - %s ) , i >. )' % STT,
            LET('g', '( ProdL ` q )',
                LET('a', '( 1st ` g )',
                    LET('e', C2,
                        LET('j', '( ( ( ( ( q Scan ( a ^ 5 ) ) ` %s ) ` %s ) ` 1 ) ` ( a ^ 5 ) )' % (SZ, SH),
                            MATCH1)))))
SEARCHBODY = LET('r', '( ( %s Reservoir %s ) ` %s )' % (SZ, SW, SY),
                 LET('i', '( # ` ( 1st ` r ) )',
                     IF('i < %s' % STT, P(NONE, '( ( 2nd ` r ) + 1 )'), INNER)))

D('Search', 'csearch', 'df-search',
  '( s e. Scales , n e. NN0 |-> %s )' % SEARCHBODY,
  'Syntax: the algorithm of the paper, with its operation count.',
  """Definition of the algorithm.  Lean:
     def search (sc : Scales) (n : NN) : Option (NN x. List NN) x. NN :=
       let res := reservoir sc.z sc.z99 sc.y ;
       let len := res.1.length ;
       if len < sc.T then (none, res.2 + 1)
       else
         let Q := res.1.drop (len - sc.T) ;
         let Lp := prodL Q ; let L := Lp.1 ; let x := L ^ 5 ;
         let c2 := res.2 + sc.T + Lp.2 + 2 ;
         let s3 := scan Q x sc.z sc.theta 1 x ;
         match s3.1 with
         | none => (none, c2 + s3.2)
         | some (_, P) =>
           let ex := extract L n P ;
           match ex.1 with
           | none => (none, c2 + s3.2 + ex.2)
           | some (m, S) =>
             let v := verify m S ;
             ((if v.1 then some (m, S) else none),
              c2 + s3.2 + ex.2 + v.2),
     "step 2 (reservoir, Q := its T largest elements, L := Q.prod,
     x := L ^ 5), step 3 (scan from k = 1 with fuel x), step 4
     (extract L n P), step 5 (verify); none on any failure.  Costs: step 2
     charges the reservoir plus T (copying Q) plus prodL Q (= T) plus 2 (the
     length test and x := L ^ 5); the other steps charge their own loops."
     This is the one definition of the block that keeps Lean's let bindings,
     as ` ( ( v e. _V |-> BODY ) ` E ) `: inlining them would multiply the
     text by about thirty, since each of the nine intermediates is used more
     than once and carries the ~ df-scales projections with it.  The let
     variables, in Lean's order, are ` r ` for res, ` i ` for len, ` q ` for
     Q, ` g ` for Lp, ` a ` for L, ` e ` for c2, ` j ` for s3, ` p ` for the
     pool list P of the some (_, P) pattern, ` w ` for ex and ` v ` for v;
     ` x = L ^ 5 ` is inlined, and ` m `, ` S ` are the projections
     ` ( 1st ` ( 2nd ` ( 1st ` w ) ) ) ` and
     ` ( 2nd ` ( 2nd ` ( 1st ` w ) ) ) ` of the some (m, S) pattern.
     ` List.drop k l ` is ` ( l substr <. k , ( # ` l ) >. ) `.  The value
     theorem is ~ searchval .""")

def _ad(a, b):
    return '( %s + %s )' % (a, b)


def _ml(a, b):
    return '( %s x. %s )' % (a, b)


_SQZ = '( Nfloor ` ( sqrt ` z ) )'
_SQX = '( Nfloor ` ( sqrt ` x ) )'
_CP2 = _ad(_ml(_ad('z', '1'), _ad(_ad(_ad(_SQZ, 'y'), '( 2 Nlog z )'), '6')), _ml('2', 't'))
_CP3 = _ml('k', _ad(_ad('t', '2'), _ml('( 2 ^ t )', _ad(_SQX, '3'))))
_CP4 = _ml('p', _ad('l', '3'))
_CP5 = _ml('s', _ad(_ad(_SQX, 's'), '6'))
_CPBODY = _ad(_ad(_ad(_ad(_ad(_ad(_CP2, '2'), _CP3), _CP4), '1'), _CP5), '4')

D('CostPieces', 'ccostpieces', 'df-costpieces',
  '( z e. NN0 , y e. NN0 |-> ( t e. NN0 |-> ( l e. NN0 |-> ( x e. NN0 |-> ( k e. NN0 |-> '
  '( p e. NN0 |-> ( s e. NN0 |-> %s ) ) ) ) ) ) )' % _CPBODY,
  'Syntax: the operation budget of the algorithm, one summand per step.',
  """Definition of the operation budget.  Lean:
     def costPieces (z y T L x k P S : NN) : NN :=
         (z + 1) * (Nat.sqrt z + y + Nat.log 2 z + 6) + 2 * T + 2
       + k * (T + 2 + 2 ^ T * (Nat.sqrt x + 3))
       + P * (L + 3) + 1
       + S * (Nat.sqrt x + S + 6) + 4,
     "The operation budget of Alg.search, one summand per step, as a function
     of the scales and of the quantities the analysis controls: the modulus
     L, the ceiling x = L ^ 5, the accepted shift k, the pool size P, the
     number of output factors S."  Nat.sqrt a is
     ` ( Nfloor ` ( sqrt ` a ) ) ` and Nat.log 2 a is ` ( 2 Nlog a ) `;
     Lean's + associates to the left, which is the grouping written here.""")


# ------------------------------------------------------------------- emitter
def wrap(s, indent, width=79):
    out, cur = [], ' ' * indent
    for tok in s.split():
        if len(cur) + 1 + len(tok) > width and cur.strip():
            out.append(cur)
            cur = ' ' * indent + tok
        else:
            cur += (' ' if cur.strip() else '') + tok
    out.append(cur)
    return '\n'.join(out)


HEADER = """
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
              The algorithm of the paper as set-theoretic functions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
  Transcription of lean/Carmichael/Algorithm.lean: the executable algorithm of
  Section 3 of carmichael.tex with its built-in operation counter.  Every
  function returns the pair ` <. value , cost >. ` of its result and the number
  of operations charged, exactly as the Lean code returns ` alpha x. NN `, and
  every recursion is primitive recursion on the fuel argument (or on the length
  of the list) over the space of functions of the remaining arguments
  (~ df-algrec ).  Each definition quotes the Lean text it transcribes, in
  ASCII; the encoding table of A1-blueprint.md section 1 and section 1 of
  A1b-blueprint.md are the audit key, the design is A1b-blueprint.md section 2.
  ` List NN ` is ` Word NN0 ` (the empty list ` (/) `, ` p :: l ` the
  concatenation ` ( <" p "> ++ l ) `, the head ` ( l ` 0 ) `, the tail
  ` ( l substr <. 1 , ( # ` l ) >. ) `), ` Bool ` is ` 2o ` with ` true = 1o `
  and ` false = (/) `, ` Option A ` is ` ( A |_| 1o ) ` with
  ` none = ( inr ` (/) ) ` and ` some a = ( inl ` a ) `, and a function of
  ` k >= 3 ` arguments is curried, ` ( ( ( A f B ) ` C ) ` D ) `.
$)
"""


def main():
    src = open(DB).read()
    if 'df-algrec' in src:
        print('df-algrec already in %s; nothing written' % DB)
        return 1
    out = [HEADER]
    for token, syn, label, body, syncom, com in DEFS:
        out.append('  $c %s $.\n' % token)
        out.append('  $( %s $)\n  %s $a class %s $.\n' % (syncom, syn, token))
        c = ' '.join(com.split())
        out.append(wrap('$( ' + c + ' $)', 2) + '\n')
        out.append(wrap('%s $a |- %s = %s $.' % (label, token, body), 2) + '\n')
        out.append('')
    with open(DB, 'a') as f:
        f.write('\n'.join(out) + '\n')
    print('wrote %d definitions to %s' % (len(DEFS), DB))
    return 0


if __name__ == '__main__':
    sys.exit(main())
