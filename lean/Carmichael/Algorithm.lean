/-
Route A: the algorithm of the paper (Section 3) as executable Lean code with
a built-in operation counter.

## Cost model (the human-verifiable contract)

* Every function below returns `α × ℕ`: the result and the number of
  operations charged. There is no monad; costs are added explicitly.
* Charging rule: ONE UNIT PER LOOP-BODY EXECUTION (plus one unit per
  straight-line block of a function, where one is charged at all). Every
  loop body in this file performs a bounded number (≤ 8) of primitive
  operations — `+ - * / %`, comparisons, and reads/writes of one dictionary
  entry or one list cell — on integers of `O(log x) = O(ℓ₂ℓ₃)` bits
  (steps 2–4) or `O(log n)` bits (step 5). Counters that a loop maintains
  for free (the length of the list it is building) are read off with
  `List.length` in the code and charged nothing: the increment is one of
  the ≤ 8 primitives of the body that appended the element. So the true
  primitive-operation count is at most `8 ×` the charged cost, and
  converting to bit operations costs a further factor polynomial in the bit
  length. The class `exp(O(ℓ₂ℓ₃))` absorbs both, so the running-time
  theorem is machine-model independent.
* Forbidden in the code: `Nat.Prime`, `Nat.decidablePrime*`, `Nat.divisors`,
  `Nat.factorization`, `Nat.gcd`, `Nat.Coprime`, `Nat.primeFactors`, any
  `Finset`, any `Real` (outside `scalesOf`), `decide`, `Classical`,
  `noncomputable` (outside `scalesOf`). Primality is trial division written
  out; smoothness is the divide-out loop written out; divisors of `L` are
  enumerated as subset products of `Q`; coprimality to `L` is `q ∤ k` for
  each `q ∈ Q`.
* All recursion is structural on an explicit fuel or on a list; there is no
  well-founded recursion, so every spec is a plain induction.
* The dictionary of step 4 is a function `ℕ → Option (List ℕ)` with
  unit-cost lookup (`t r`) and update (`Function.update`).
* `search` is a plain `def`: Lean refuses to compile it if anything
  noncomputable leaks in. Only `scalesOf` (which packages the real-valued
  scale parameters of step 1 into integers) is `noncomputable`.
-/
import Carmichael.Defs

set_option autoImplicit false

namespace Carmichael

/-- The five integer scale parameters of step 1. -/
structure Scales where
  /-- `z = ⌈C₁ ℓ₂ ℓ₃⌉`. -/
  z : ℕ
  /-- `⌊z^{99/100}⌋`, the reservoir floor. -/
  z99 : ℕ
  /-- `y = ⌈z^{1-E}⌉`, the smoothness bound. -/
  y : ℕ
  /-- `T = ⌈3 ℓ₂⌉ = |Q|`. -/
  T : ℕ
  /-- `θ = ⌈(log n)^{1.2}⌉`, the pool threshold. -/
  θ : ℕ

/-- Step 1: the scales of the paper at constants `C₁, E`. This is the only
place the real-valued constants enter. -/
noncomputable def scalesOf (C₁ E : ℝ) (n : ℕ) : Scales :=
  ⟨zscale C₁ n, ⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊, yscaleE C₁ n E,
   Tscale n, ⌈(Real.log n) ^ (1.2 : ℝ)⌉₊⟩

namespace Alg

/-! ### Primitives -/

/-- Trial-division loop for `isPrimeTD m`: tries `d, d+1, …` while
`d * d ≤ m`; returns `false` at the first divisor. Charges one unit per
`d` tried (including the final one that fails `d * d ≤ m`). Fuel-exhaustion
returns `true` with no charge. -/
def primeGo (m : ℕ) : ℕ → ℕ → Bool × ℕ
  | _, 0 => (true, 0)
  | d, fuel + 1 =>
    if m < d * d then (true, 1)
    else if m % d = 0 then (false, 1)
    else
      let r := primeGo m (d + 1) fuel
      (r.1, r.2 + 1)

/-- Primality by trial division: `2 ≤ m` and no divisor `d` with `2 ≤ d`,
`d * d ≤ m`. Fuel `m` (the loop stops at `d ≤ Nat.sqrt m + 1 ≤ m`).
Charges `1` plus the loop, so at most `Nat.sqrt m + 1`. -/
def isPrimeTD (m : ℕ) : Bool × ℕ :=
  if m < 2 then (false, 1)
  else
    let r := primeGo m 2 m
    (r.1, r.2 + 1)

/-- Divide `d` out of `r` while `d ∣ r` (fuel-bounded). Charges one unit per
successful division; the failing test is charged to the caller's loop body.
-/
def divOut (d : ℕ) : ℕ → ℕ → ℕ × ℕ
  | r, 0 => (r, 0)
  | r, fuel + 1 =>
    if r % d = 0 then
      let s := divOut d (r / d) fuel
      (s.1, s.2 + 1)
    else (r, 0)

/-- Outer loop of `smoothTD`: for `d, d+1, …` (`fuel` values) divide `d`
out of `r` completely (inner fuel `r`). Charges one unit per `d` plus the
successful divisions. -/
def smoothGo : ℕ → ℕ → ℕ → ℕ × ℕ
  | _, r, 0 => (r, 0)
  | d, r, fuel + 1 =>
    let s := divOut d r r
    let t := smoothGo (d + 1) s.1 fuel
    (t.1, t.2 + s.2 + 1)

/-- `y`-smoothness of `k` by trial division: divide out `d = 2, …, y` and
test whether `1` remains. Charges `1` plus `y - 1` outer bodies plus at most
`Nat.log 2 k` successful divisions (each at least halves `r ≥ 1`), so at
most `y + Nat.log 2 k + 2`. -/
def smoothTD (y k : ℕ) : Bool × ℕ :=
  let s := smoothGo 2 k (y - 1)
  (s.1 == 1, s.2 + 1)

/-- `ds.map (· * q)`, charging one unit per element. -/
def mulAll (q : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | d :: ds =>
    let r := mulAll q ds
    (d * q :: r.1, r.2 + 1)

/-- All subset products of `Q` (the divisors of `Q.prod` when `Q` is a list
of distinct primes), as a list of length `2 ^ Q.length`: `ds := [1]`, then
for each `q`, `ds := ds ++ ds.map (· * q)`. Charges one unit per
multiplication, `2 ^ Q.length - 1` in total. -/
def divisorsOf : List ℕ → List ℕ × ℕ
  | [] => ([1], 0)
  | q :: Q =>
    let r := divisorsOf Q
    let s := mulAll q r.1
    (r.1 ++ s.1, r.2 + s.2)

/-- `∀ q ∈ Q, q ∤ k`, with early exit. Charges one unit per `q` tested, at
most `Q.length`. -/
def coprimeTo : List ℕ → ℕ → Bool × ℕ
  | [], _ => (true, 0)
  | q :: Q, k =>
    if k % q = 0 then (false, 1)
    else
      let r := coprimeTo Q k
      (r.1, r.2 + 1)

/-- The product of a list, charging one unit per multiplication
(`S.length` in total). -/
def prodL : List ℕ → ℕ × ℕ
  | [] => (1, 0)
  | p :: S =>
    let r := prodL S
    (p * r.1, r.2 + 1)

/-! ### Step 2: the reservoir -/

/-- Loop of `reservoir`: for `q, q+1, …` (`fuel` values, ascending) keep `q`
iff `z99 < q`, `isPrimeTD q`, `smoothTD y (q - 1)`. Charges one unit per
`q` plus the two tests (both always run). -/
def resGo (z99 y : ℕ) : ℕ → ℕ → List ℕ × ℕ
  | _, 0 => ([], 0)
  | q, fuel + 1 =>
    let pr := isPrimeTD q
    let sm := smoothTD y (q - 1)
    let rest := resGo z99 y (q + 1) fuel
    let keep := if z99 < q then pr.1 && sm.1 else false
    ((if keep then q :: rest.1 else rest.1), rest.2 + pr.2 + sm.2 + 1)

/-- Step 2: the primes `q ∈ (z99, z]` with `q - 1` being `y`-smooth, in
ascending order (`q = 2, …, z`, fuel `z - 1`). Charges at most
`(z - 1) * (Nat.sqrt z + y + Nat.log 2 z + 4)`. -/
def reservoir (z z99 y : ℕ) : List ℕ × ℕ := resGo z99 y 2 (z - 1)

/-! ### Step 3: the pool and the scan for `k` -/

/-- Loop of `poolAlg`: for each divisor `d`, `p := d * k + 1`; keep `p` iff
`p ≤ x`, `z < p`, `isPrimeTD p`. Charges one unit per `d` plus the
primality test, which runs only when `p ≤ x` (so costs `≤ Nat.sqrt x + 1`).
-/
def poolGo (x z k : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | d :: ds =>
    let p := d * k + 1
    let rest := poolGo x z k ds
    if p ≤ x ∧ z < p then
      let pr := isPrimeTD p
      ((if pr.1 then p :: rest.1 else rest.1), rest.2 + pr.2 + 1)
    else (rest.1, rest.2 + 1)

/-- Step 3 pool `P_k = {d k + 1 : d ∣ L, d k + 1 ≤ x, d k + 1 prime, z < d k + 1}`
with `d` ranging over `divisorsOf Q`. Charges `divisorsOf` plus the loop:
at most `2 ^ Q.length * (Nat.sqrt x + 3)`. -/
def poolAlg (Q : List ℕ) (x z k : ℕ) : List ℕ × ℕ :=
  let ds := divisorsOf Q
  let r := poolGo x z k ds.1
  (r.1, ds.2 + r.2)

/-- The scan for `k`: for `k, k+1, …` (`fuel` values) return the first
`(k, P_k)` with `coprimeTo Q k` and `θ ≤ P_k.length`. Charges one unit per
`k` plus `coprimeTo` plus (when coprime) `poolAlg`. -/
def scan (Q : List ℕ) (x z θ : ℕ) : ℕ → ℕ → Option (ℕ × List ℕ) × ℕ
  | _, 0 => (none, 0)
  | k, fuel + 1 =>
    let cp := coprimeTo Q k
    if cp.1 then
      let P := poolAlg Q x z k
      if θ ≤ P.1.length then (some (k, P.1), cp.2 + P.2 + 1)
      else
        let r := scan Q x z θ (k + 1) fuel
        (r.1, r.2 + cp.2 + P.2 + 1)
    else
      let r := scan Q x z θ (k + 1) fuel
      (r.1, r.2 + cp.2 + 1)

/-! ### Step 4: dynamic programming over residues mod `L` -/

/-- The DP table: residue ↦ one witness list (a nonempty list of processed
primes whose product has that residue), or `none`. -/
abbrev Tbl := ℕ → Option (List ℕ)

/-- The empty table. -/
def emptyTbl : Tbl := fun _ => none

/-- Write `W` at residue `r` if that entry is empty (one read, one write). -/
def setIfNone (t : Tbl) (r : ℕ) (W : List ℕ) : Tbl :=
  match t r with
  | none => Function.update t r (some W)
  | some _ => t

/-- Loop of `dpStep`: for `r = fuel - 1, …, 0`, if the SNAPSHOT `t` has a
witness `W` at `r`, write `p :: W` at `(r * p) % L` into the accumulator
(if empty). Charges one unit per `r`. -/
def dpGo (L p : ℕ) (t : Tbl) : ℕ → Tbl → Tbl × ℕ
  | 0, acc => (acc, 0)
  | r + 1, acc =>
    let acc' :=
      match t r with
      | none => acc
      | some W => setIfNone acc ((r * p) % L) (p :: W)
    let res := dpGo L p t r acc'
    (res.1, res.2 + 1)

/-- One DP step: process the prime `p`. Start from `t` with `[p]` written at
`p % L` (if empty), then extend every witness of the snapshot `t` by `p`.
Charges exactly `L + 1`. -/
def dpStep (L p : ℕ) (t : Tbl) : Tbl × ℕ :=
  let res := dpGo L p t L (setIfNone t (p % L) [p])
  (res.1, res.2 + 1)

/-- Loop of `extract`: state `(m, used, t)`; at prime `p` run `dpStep`; if
residue `1 % L` now has a witness `S`, multiply `m` by `S.prod`, prepend
`S` to `used`, reset the table, and return `some (m, used)` as soon as
`n < m`. Charges `dpStep` plus one unit per `p`, plus `prodL S` on a hit. -/
def extractGo (L n : ℕ) : List ℕ → ℕ → List ℕ → Tbl → Option (ℕ × List ℕ) × ℕ
  | [], _, _, _ => (none, 0)
  | p :: P, m, used, t =>
    let st := dpStep L p t
    match st.1 (1 % L) with
    | none =>
      let res := extractGo L n P m used st.1
      (res.1, res.2 + st.2 + 1)
    | some S =>
      let pr := prodL S
      let m' := m * pr.1
      if n < m' then (some (m', S ++ used), st.2 + pr.2 + 1)
      else
        let res := extractGo L n P m' (S ++ used) emptyTbl
        (res.1, res.2 + st.2 + pr.2 + 1)

/-- Step 4: greedy extraction of subsets of `P` with product `≡ 1 (mod L)`
until the running product exceeds `n`; returns `(m, S)` with `m = S.prod`,
or `none` if `P` is exhausted first. Charges at most
`P.length * (L + 3)`. -/
def extract (L n : ℕ) (P : List ℕ) : Option (ℕ × List ℕ) × ℕ :=
  extractGo L n P 1 [] emptyTbl

/-! ### Step 5: verification of the output -/

/-- `p ∉ S`, charging one unit per element of `S`. -/
def notMemTD (p : ℕ) : List ℕ → Bool × ℕ
  | [] => (true, 0)
  | q :: S =>
    let r := notMemTD p S
    ((if p = q then false else r.1), r.2 + 1)

/-- `S.Nodup` by pairwise comparison. Charges at most
`S.length * (S.length + 1)`. -/
def nodupTD : List ℕ → Bool × ℕ
  | [] => (true, 0)
  | p :: S =>
    let a := notMemTD p S
    let r := nodupTD S
    (a.1 && r.1, a.2 + r.2 + 1)

/-- `∀ p ∈ S, isPrimeTD p`. Charges one unit per element plus the tests. -/
def allPrimeTD : List ℕ → Bool × ℕ
  | [] => (true, 0)
  | p :: S =>
    let a := isPrimeTD p
    let r := allPrimeTD S
    (a.1 && r.1, a.2 + r.2 + 1)

/-- Korselt's condition `∀ p ∈ S, (p - 1) ∣ (m - 1)`. Charges one unit per
element. -/
def korseltTD (m : ℕ) : List ℕ → Bool × ℕ
  | [] => (true, 0)
  | p :: S =>
    let r := korseltTD m S
    ((if (m - 1) % (p - 1) = 0 then r.1 else false), r.2 + 1)

/-- Step 5: certify `(m, S)`: `S.Nodup`, every `p ∈ S` prime, `S.prod = m`,
`3 ≤ S.length`, and Korselt's condition. All five checks run; charges their
sum plus `2`, at most `S.length * (Nat.sqrt x + S.length + 5) + 2` when
every `p ∈ S` is `≤ x`. -/
def verify (m : ℕ) (S : List ℕ) : Bool × ℕ :=
  let nd := nodupTD S
  let pr := allPrimeTD S
  let pd := prodL S
  let ko := korseltTD m S
  let ok := nd.1 && pr.1 && (pd.1 == m) && ko.1
  ((if 3 ≤ S.length then ok else false), nd.2 + pr.2 + pd.2 + ko.2 + 2)

/-! ### Assembly -/

/-- The algorithm: step 2 (reservoir, `Q :=` its `T` largest elements,
`L := Q.prod`, `x := L ^ 5`), step 3 (`scan` from `k = 1` with fuel `x`),
step 4 (`extract L n P`), step 5 (`verify`); `none` on any failure. Costs:
step 2 charges the reservoir plus `T` (copying `Q`) plus `prodL Q` (`= T`)
plus `2` (the length test and `x := L ^ 5`); the other steps charge their
own loops. -/
def search (sc : Scales) (n : ℕ) : Option (ℕ × List ℕ) × ℕ :=
  let res := reservoir sc.z sc.z99 sc.y
  let len := res.1.length
  if len < sc.T then (none, res.2 + 1)
  else
    let Q := res.1.drop (len - sc.T)
    let Lp := prodL Q
    let L := Lp.1
    let x := L ^ 5
    let c2 := res.2 + sc.T + Lp.2 + 2
    let s3 := scan Q x sc.z sc.θ 1 x
    match s3.1 with
    | none => (none, c2 + s3.2)
    | some (_, P) =>
      let ex := extract L n P
      match ex.1 with
      | none => (none, c2 + s3.2 + ex.2)
      | some (m, S) =>
        let v := verify m S
        ((if v.1 then some (m, S) else none), c2 + s3.2 + ex.2 + v.2)

end Alg

/-- The operation budget of `Alg.search`, one summand per step, as a
function of the scales and of the quantities the analysis controls: the
modulus `L`, the ceiling `x = L ^ 5`, the accepted shift `k`, the pool size
`P`, the number of output factors `S`.

* Step 2, `(z + 1) * (Nat.sqrt z + y + Nat.log 2 z + 6) + 2 * T + 2`:
  `reservoir` runs `z - 1` bodies (`q = 2, …, z`), each charging
  `1 + isPrimeTD q + smoothTD y (q - 1) ≤ 1 + (Nat.sqrt z + 1) + (y + Nat.log 2 z + 2)`;
  then `search` charges `1` (length test), `T` (copying `Q`), `T`
  (`prodL Q`, `Q.length = T`), `1` (`x := L ^ 5`).
* Step 3, `k * (T + 2 + 2 ^ T * (Nat.sqrt x + 3))`: `scan` stops at the
  accepted `k`, having run `k` bodies, each charging
  `1 + coprimeTo Q k' + poolAlg Q x z k' ≤ 1 + T + 2 ^ T * (Nat.sqrt x + 3)`
  (`divisorsOf Q` charges `2 ^ T - 1`; each of the `2 ^ T` divisors charges
  `1` plus, only when `p ≤ x`, `isPrimeTD p ≤ Nat.sqrt x + 1`).
* Step 4, `P * (L + 3) + 1`: `extract` runs at most `P` bodies, each
  charging `dpStep = L + 1` plus `1`, plus `prodL S' = S'.length` on each
  hit; the hit witnesses are disjoint sublists of `P`, so their lengths sum
  to at most `P`.
* Step 5, `S * (Nat.sqrt x + S + 6) + 4`: `verify` charges
  `nodupTD ≤ S * (S + 1)`, `allPrimeTD ≤ S * (Nat.sqrt x + 2)` (every
  factor is `≤ x`), `prodL = S`, `korseltTD = S`, plus `2`. -/
def costPieces (z y T L x k P S : ℕ) : ℕ :=
    (z + 1) * (Nat.sqrt z + y + Nat.log 2 z + 6) + 2 * T + 2   -- step 2
  + k * (T + 2 + 2 ^ T * (Nat.sqrt x + 3))                    -- step 3
  + P * (L + 3) + 1                                           -- step 4
  + S * (Nat.sqrt x + S + 6) + 4                              -- step 5

end Carmichael
