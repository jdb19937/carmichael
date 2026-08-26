# BVPLAN — Battle plan for eliminating `Assumptions.pigeonhole` (AGP Theorem 3.1)

*Intelligence assessment, 2026-08-26. Sources: AGP, "There are infinitely many Carmichael
numbers," Annals 140 (1994) 703–722 (read in full, §§0–3); Heath-Brown, "Zero-free regions
for Dirichlet L-functions, and the least prime in an arithmetic progression" (1992);
Thorner–Zaman, "An explicit version of Bombieri's log-free density estimate…"
(arXiv:2208.11123, Forum Math. 2024); Tao 254A Notes 6–7; PNT+ repo; the pinned Mathlib
(`v4.33.1`) under `.lake/packages/mathlib`.*

---

## 0. Executive summary — read this first

**The headline finding is negative and it changes the campaign:** the Bombieri–Vinogradov
theorem is *neither sufficient nor necessary* for AGP Theorem 3.1. What Theorem 3.1
actually consumes is AGP's class-𝓑 property (their (0.3)): a *pointwise lower bound*
π(y;d,1) ≥ π(y)/(2φ(d)) for **every** d ≤ x^B outside a **structured exceptional set**
(multiples of at most D_B integers). BV controls the error *summed over all moduli*, with
an *unstructured* exceptional set of size up to x^B/log^A x. The moduli we care about are
the divisors of L, and there are only τ(L) = x^{o(1)} of them (in this project,
polylog(n) of them: ω(L) = |Q| ≈ 3ℓ₂). A BV-shaped exceptional set can swallow *all* of
them. No averaging trick fixes this — the main term ∑_{d|L, d≤x^B} π(x)/φ(d) is
x^{1+o(1)}/x^B·τ(L) ≪ x/log^A x, i.e. *smaller than the BV error budget*. Verified
against the actual proof on pp. 714–716: the argument is pointwise-per-divisor +
pigeonhole; there is no route to it from a ∑_d max_a bound or from a
Barban–Davenport–Halberstam variance bound.

**What is actually needed** (and what AGP prove in their §2, Theorem 2.1) is
*Linnik-theorem technology*: the explicit formula for ψ(y,χ), a crude zero count
N(1/2,T,d) ≪ Td·log(Td), and — the crux — a **log-free zero-density estimate**
∑_{χ mod d} N(σ,T,χ) ≤ γ₂·(dT^c)^{A(1−σ)} with **d-aspect exponent A < 1/B**, plus a
log-free *census* of near-1 zeros aggregated over all conductors (any exponent) to bound
the exceptional set by a constant. Since the structural analysis allows any B > 1/5, we
need A < 5 — and this is exactly the regime σ ≥ 4/5, where Jutila-quality estimates give
A = 12/5+ε (Heath-Brown 1992, eq. (1.4)). The margin (needed ≤ ~4.6, available 2.4) is
the campaign's feasibility cushion: a factor ~2 of allowable slop in the hardest sortie.

**Good news found along the way** (each independently verified against the AGP proof):

1. **Siegel's theorem is NOT needed.** AGP §2 is already Siegel-free (that is why their
   Theorem 1 is effective). Better: **Landau–Page is not needed either.** The exceptional
   set 𝓓(x) members are simply *removed from L* in the 3.1 proof (one prime factor
   each); nothing requires them to exceed log x. The only thing that must be checked is
   1 ∉ 𝓓(x), i.e. ζ has no zeros in the fixed box [τ,1]×[−ν,ν] for large x — which
   follows from Mathlib's `riemannZeta_ne_zero_of_one_le_re` + compactness
   (`IsCompact.inter_riemannZetaZeros_finite`), both in the pinned Mathlib.
2. **Vaughan's identity, Gauss sums, Siegel–Walfisz, and the classical large sieve
   transfer to multiplicative characters are all off the critical path.** They belong to
   the BV proof chain, which we are not walking.
3. **T can be taken polylogarithmic** (T = log⁴x) in the explicit formula, so all zero
   information is needed only up to height polylog(x); the t-aspect of every estimate is
   trivialized (Pólya–Vinogradov + partial summation covers it). AGP's T = x³ was
   convenience, not necessity.
4. **All multiplicative constants are free.** The consumer takes D as a *field of the
   structure we get to instantiate*, and downstream absorbs any constant D via ∀ᶠ
   (τ(L)/log x grows like (log n)^{2+}); ineffective/outrageous constants (D ~ e^{20000})
   are acceptable. Only the *exponents* (A < 1/B in the d-aspect) are rigid.
5. **PNT for the modulus d = 1 falls out of our own machinery** (Theorem 2.1 at d = 1
   gives ψ(y) = (1±ε)y), so π(y) ≥ (1−ε)y/log y — needed in step (3.2) of the 3.1 proof
   — costs nothing extra. Chebyshev's π(y) ≤ (log 4+ε)y/log y comes from Mathlib's
   `Chebyshev.theta_le_log4_mul_x`.

**Route decision: Route Z ("Linnik-zone log-free density"), described in §3.** Roughly
20 Lean sorties plus 2 paper-math gate documents. Highest risk: the pre-sifted log-free
zero-density estimate (sortie Z6). A hedge route via smooth-moduli character sums
(Graham–Ringrose) is catalogued in §5 but has its own research-grade hole (quadratic
characters).

---

## 1. The exact target statement chain

### 1.1 What the repo needs (the consumer)

`Carmichael/Assumptions.lean`, field `pigeonhole` — AGP Theorem 3.1 at B = 2/5:

> ∀ x L, z₃ < x → 1 < L → Squarefree L → (∀ prime q ∣ L, q ≤ x^{3/10}) →
> ∑_{q∣L} 1/q ≤ 3/160 →
> ∃ k, 0 < k ≤ x^{3/5}, gcd(k,L)=1, and
> #{d ∣ L : dk+1 ≤ x, dk+1 prime} ≥ 2^{−D−2}/log x · #{d ∣ L : d ≤ x^{2/5}}.

Since `Defs.lean` sets x = L⁵, every divisor of L is ≤ x^{1/5}, so the filter
`d ≤ x^{2/5}` is vacuous downstream (`Step3.lean:325` proves exactly this). The
**B-generic pass** (user's plan) replaces 2/5 by a parameter B ∈ (1/5, 2/5]; the only
downstream statement that genuinely moves is `k ≤ x^{3/5}` → `k ≤ x^{1−B}` (the proof of
3.1 produces k = (p−1)/d ≤ x^{1−B}, and Step3/Budget must carry x^{1−B} instead of
x^{3/5}). The hypotheses get *weaker* as B decreases (x^{3/10} ≤ x^{(1−B)/2} and
3/160 ≤ (1−B)/32 for B ≤ 2/5), so the existing hypothesis pack still discharges them.

**We fix B := 21/100** (rational, comfortably above the hard floor 1/5, and small enough
to leave a factor-2 exponent cushion in the analytic core; see §3.3).

### 1.2 AGP Theorem 3.1 (target, math form at generic B)

> **Thm 3.1.** Let B ∈ 𝓑 with constants (x₂(B), D_B, 𝓓_B(·)). There is x₃(B) such that
> for x ≥ x₃(B), if L is squarefree, P⁺(L) ≤ x^{(1−B)/2}, and ∑_{q|L} 1/q ≤ (1−B)/32,
> then ∃ k ≤ x^{1−B}, (k,L)=1, with
> #{d|L : dk+1 ≤ x prime} ≥ (2^{−D_B−2}/log x)·#{d|L : d ≤ x^B}.

Its proof (p. 716, verified line-by-line) consumes exactly:

* **(0.3), one-sided, residue a = 1 only, at the single point y = d·x^{1−B}** for each
  divisor d ≤ x^B of L′ (AGP themselves note before their Theorem 4 that a = 1 suffices);
* **π(y) ≥ y/log y** (Rosser–Schoenfeld; any (1−ε) constant works, absorbed into D);
* **Brun–Titchmarsh** π(y; dq, 1) ≤ C_BT·y/(φ(dq)·log(y/dq)) for the moduli dq ≤ y^{(1+B)/2…};
  AGP use Montgomery–Vaughan C_BT = 2; **any C_BT ≤ 3 fits the verbatim 3/160 budget**
  (see §1.5);
* **divisor-transfer lemma (3.1)**: L′ := L with one prime factor of each member of
  𝓓_B(x)∩divisors removed; then #{d|L′ : d ≤ y} ≥ 2^{−D_B}·#{d|L : d ≤ y} (fiber map
  d ↦ (largest divisor of d dividing L′), fibers ≤ τ(L/L′) ≤ 2^{D_B});
* a **counting pigeonhole** over k ∈ [1, x^{1−B}].

All elementary given 𝓑-membership. No max over residues, no summation over all moduli.

### 1.3 The 𝓑-membership target (the deep input), math form

> **Def (AGP p. 705).** B ∈ 𝓑 iff ∃ x₂(B), D_B ∈ ℕ, and for each x a set 𝓓_B(x) of at
> most D_B integers, each > 1 (AGP say > log x; we only need > 1 — see §0.1), such that
> for x ≥ x₂(B), (a,d) = 1, 1 ≤ d ≤ min{x^B, y/x^{1−B}}, d divisible by no member of
> 𝓓_B(x):  π(y; d, a) ≥ π(y)/(2φ(d)).

We prove it via the ψ-weighted version (AGP Thm 2.1 shape), which implies the π version
by partial summation + Chebyshev upper bound + our own d = 1 PNT:

> **Target T2.1 (at B = 21/100, δ = 1/100, level 1/A−δ with A := 9/2).** For every
> ε > 0 there are D(ε), x₂(ε), and for each x a set 𝓓(x) of ≤ D(ε) integers ≥ 2, s.t.
> for x ≥ x₂(ε), (a,d)=1, d ≤ min{x^{2/9−1/100}, y/x^{7/9+1/100}}, no member of 𝓓(x)
> dividing d:  |∑_{p≤y, p≡a (d)} log p − y/φ(d)| ≤ ε·y/φ(d).

(We then instantiate ε = 1/4 and check 2/9 − 1/100 > 21/100 = B.)

### 1.4 Lean sketches

```lean
/-- 𝓑-membership package, the analytic core deliverable. -/
structure BMembership (B : ℝ) where
  D    : ℕ                       -- bound on the exceptional count
  x₂   : ℕ
  bad  : ℕ → Finset ℕ            -- 𝓓(x)
  bad_card : ∀ x, (bad x).card ≤ D
  bad_ge_two : ∀ x, ∀ m ∈ bad x, 2 ≤ m
  lower : ∀ x y d a : ℕ, x₂ ≤ x → 0 < d → Nat.Coprime a d →
    (d : ℝ) ≤ (x : ℝ) ^ B → (d : ℝ) * (x : ℝ) ^ (1 - B) ≤ (y : ℝ) → (y : ℝ) ≤ x →
    (∀ m ∈ bad x, ¬ m ∣ d) →
    (primePi y : ℝ) / (2 * Nat.totient d) ≤
      (((Finset.range (y+1)).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℝ)

/-- Final deliverable, replacing `Assumptions.pigeonhole` after the B-generic pass. -/
theorem pigeonhole_of_BMembership (B : ℝ) (hB : 1/5 < B) (hB' : B ≤ 2/5)
    (𝓑 : BMembership B) :
    ∃ D z₃ : ℕ, ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
      (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x:ℝ) ^ ((1-B)/2)) →
      (∑ q ∈ L.primeFactors, (1:ℝ)/q) ≤ (1-B)/32 →
      ∃ k : ℕ, 0 < k ∧ (k:ℝ) ≤ (x:ℝ)^(1-B) ∧ k.Coprime L ∧
        (2:ℝ)^(-(D:ℝ)-2) / Real.log x *
          ((L.divisors.filter (fun d : ℕ => (d:ℝ) ≤ (x:ℝ)^B)).card : ℝ)
        ≤ ((L.divisors.filter (fun d => d*k+1 ≤ x ∧ (d*k+1).Prime)).card : ℝ)
```

The analytic intermediate statements (all for `χ : DirichletCharacter ℂ d`, using
Mathlib's `DirichletCharacter.LFunction`):

```lean
-- Z4 (crude zero count): N(1/2,T,d) ≤ C·T·d·log(d·(T+2))
theorem zero_count_box (d : ℕ) (T : ℝ) (hT : 2 ≤ T) :
    zeroCount d (1/2) T ≤ C * T * d * Real.log (d * (T+2))

-- Z5 (explicit formula, primitive χ, sharp cutoff, 2 ≤ T ≤ y):
-- |ψ(y,χ) − δ_χ·y + ∑_{ρ : L(ρ,χ)=0, β≥1/2, |γ|≤T} y^ρ/ρ|
--   ≤ C·( y·log²(d·T·y)/T + √y·log²(d·T) )

-- Z6 (log-free density, THE crux; see §3.3):
-- ∑_{χ mod d} N(σ,T,χ) ≤ γ₂ · (d·T^{c₀})^{(9/2)·(1−σ)}   for σ ≥ 79/100, T ≥ 2

-- Z7 (census, aggregated over conductors, any exponent c₃):
-- ∑_{d' ≤ Z} ∑*_{χ mod d' primitive} N(σ, ν, χ) ≤ c₂ · Z^{c₃(1−σ)}   for σ ≥ 39/40
```

### 1.5 The constant budget (must be respected verbatim by executors)

With Chebyshev lower constant c_cheb (π(y) ≥ y/(c_cheb log y)) and Brun–Titchmarsh
constant C_BT, the good-prime count per divisor d of L′ is at least

  [ 1/(2·c_cheb) − (4·C_BT/(1−B))·S ] · d·x^{1−B}/(φ(d)·log x),   S := ∑_{q|L} 1/q.

Against the **verbatim hypothesis S ≤ 3/160** and B ≤ 2/5 (so 4/(1−B) ≤ 20/3):
c_cheb = 1+ε (from our own d=1 PNT) and C_BT = 3 give 1/2 − 3·(20/3)·(3/160) = 1/8 > 0. ✓
The surviving constant 2^{−j} is absorbed by instantiating D := D_census + j. Executors
must NOT weaken c_cheb below ~1.3 or C_BT above ~3.9 without re-running this budget.

---

## 2. Inventory: what exists (pinned Mathlib v4.33.1, PNT+, local)

### 2.1 Pinned Mathlib — surprisingly strong L-function base

| Item | Name (verified in `.lake/packages/mathlib`) |
|---|---|
| Dirichlet L-function, entire continuation | `DirichletCharacter.LFunction`, `differentiable_LFunction` (`NumberTheory/LSeries/DirichletContinuation.lean`) |
| Completed L-function + **functional equation** | `completedLFunction`, `IsPrimitive.completedLFunction_one_sub`, `rootNumber`, `gammaFactor` (same file) |
| Trivial zeros; L vs completed/gamma | `Even.LFunction_neg_two_mul_nat`, `LFunction_eq_completed_div_gammaFactor` |
| **Non-vanishing on Re s = 1** (all χ) | `LFunction_ne_zero_of_one_le_re`, `LFunction_apply_one_ne_zero` (`LSeries/Nonvanishing.lean`) |
| ζ zero set: closed, discrete, finite-in-compacts | `riemannZetaZeros`, `IsCompact.inter_riemannZetaZeros_finite` (`LSeries/ZetaZeros.lean`) |
| Dirichlet's theorem machinery (Λ restricted to class, L-series identities) | `LSeries/PrimesInAP.lean` |
| Conductor / primitive theory | `DirichletCharacter.conductor`, `IsPrimitive`, `primitiveCharacter`, `changeLevel_primitiveCharacter`, `LFunction_changeLevel` |
| Character orthogonality | `sum_char_inv_mul_char_eq` (`DirichletCharacter/Orthogonality.lean`) |
| **Jensen's formula + disk zero-count** | `AnalyticOnNhd.circleAverage_log_norm`, **`AnalyticOnNhd.sum_divisor_le`** (`Analysis/Complex/JensenFormula.lean`) |
| **Borel–Carathéodory** | `Analysis/Complex/BorelCaratheodory.lean` |
| Chebyshev ψ, θ; θ ≤ (log 4)x | `NumberTheory/Chebyshev.lean` (`theta_le_log4_mul_x`) |
| Selberg sieve structures | `NumberTheory/SelbergSieve.lean` |
| Abel summation | `NumberTheory/AbelSummation.lean` |
| Gauss sums (not needed on Route Z) | `DirichletCharacter/GaussSum.lean` |

**Absent from Mathlib:** any large sieve; any mean-value theorem for Dirichlet
polynomials; Perron formula; explicit formula; any zero count N(T,χ); any zero-free
region beyond Re s = 1; Hadamard factorization (not needed — Borel–Carathéodory + Jensen
suffice for the Landau partial-fraction lemma); Brun–Titchmarsh.

### 2.2 PNT+ (github.com/AlexKontorovich/PrimeNumberTheoremAnd) — crib source

Files (sizes): `PerronFormula.lean` (54K), `ResidueCalcOnRectangles.lean` (65K),
`Rectangle.lean`, `RectangleArgumentPrinciple.lean` (17K), `ZetaBounds.lean` (170K),
`MediumPNT.lean` (179K — PNT with exp(−c(log x)^θ) error), `StrongPNT.lean` (185K —
classical zero-free region for ζ), `BrunTitchmarsh.lean` (21K, **no sorries**, Selberg
sieve, interval form `primesBetween x (x+y) ≤ 2y/log z + 6z(1+log z)³`), `Wiener.lean`,
`MellinCalculus.lean`, `BorelCaratheodory.lean`, `HadamardFactorization.lean` (196-byte
stub). **PNT in arithmetic progressions: not done** (stated goal only). So: PNT+ has the
full ζ-precedent for contour/explicit-formula work and a Brun–Titchmarsh precedent, but
*nothing* on Dirichlet L zero counts, densities, or progressions. Porting pattern already
established in this repo (`Contrib/Mertens.lean` was ported from PNT+ via zeta-23-lean).

### 2.3 Local repo

`SelbergBound.lean`: Selberg-sieve fundamental theorem
`siftedSum ≤ X/S + ∑_{d|P, d≤y} 3^{ω(d)}|R_d|` — directly powers Brun–Titchmarsh for
progressions. `PrimeCount.lean`: π(z) ≥ z/(3 log z) eventually (too weak for §1.5 alone;
superseded by d=1 PNT output). `Contrib/Mertens.lean`: Mertens' first theorem.
`ZeroSum.lean`, `Korselt.lean`, Steps 2–4: consumers, untouched.

---

## 3. Route decision

### 3.1 Rejected: BV and its relatives (task item 3, adversarial answers)

* **(3a) BDH variance bound:** NO. Same defect as BV: unstructured exceptions vs. a
  x^{o(1)}-sparse target family (divisors of L). The 3.1 proof needs per-divisor lower
  bounds; a variance bound over *all* d ≤ Q cannot see divisors of one L.
* **BV proper (any proof: Vaughan, Motohashi, Gallagher):** NO, for the same reason.
  Formalizing BV would be a fine independent goal but *would not eliminate the
  assumption*. Do not spend sorties on Vaughan's identity, Gauss-sum transfer,
  Siegel–Walfisz.
* **(3b) Siegel-free route:** YES — this is free. AGP §2 is Siegel-free, and even
  Landau–Page drops out (§0, item 1). No effectivity sacrifices anywhere.
* **(3d) assumption-shaped shortcut via smooth moduli:** partially viable, kept as the
  hedge Route S (§5); it has an unresolved research hole (quadratic characters) and
  requires adding a smoothness hypothesis on L to the assumption statement (downstream
  provides P⁺(L) ≤ zscale = O(ℓ₂ℓ₃) = (log x)^{1+o(1)}-smooth, so the hypothesis is
  available).

### 3.2 Chosen: Route Z — AGP §2 verbatim at generic B, with three simplifications

Prove `BMembership (21/100)` following AGP Theorem 2.1's proof with:

1. **T = log⁴x** in the explicit formula (not x³). The truncation error
   y·log²(dTy)/T ≤ εy/9 holds with polylog T; every subsequent estimate then only needs
   zero information to height polylog(x), and t-aspects of character-sum bounds come from
   Pólya–Vinogradov + partial summation with |t| ≤ polylog — trivial.
2. **Landau–Page deleted**, replaced by: 𝓓(x) := set of conductors d′ ≤ x^{2/9} having a
   zero with β ≥ τ := 1 − ρ/log x, |γ| ≤ ν (ρ, ν absolute constants fixed by the (2.8)
   budget); |𝓓(x)| ≤ D by the census (Z7); 1 ∉ 𝓓(x) for large x by ζ-nonvanishing +
   compactness (Z8).
3. **Zero-density split** by σ (all bounds single-modulus, ∑_{χ mod d}, reduced to
   primitive conductors d′|d at the cost of τ(d) ≤ d^{o(1)}, absorbed):
   * σ ∈ [1/2, σ_min], σ_min := 79/100: **trivial count** (Z4) — contribution
     y^{σ_min−1}·d·polylog ≤ εy/9 because y ≥ d·x^{79/100} forces y^{1−σ_min} ≥ d·x^{κ}.
   * σ ∈ [σ_min, σ*], σ* := 1 − C*·loglog x/log x: **logged density suffices**, any
     exponent coefficient ≤ 4.6 with any log power (logs absorbed by
     (d^{A}/y)^{1−σ} ≤ exp(−κ(1−σ)log x) ≤ log^{−(K+1)}x here). Huxley-large-values
     coefficient 3/(3σ−1) ≤ 2.2 on this range, or even Halász 3/(2σ−1) ≤ 5.17 — note
     Halász alone FAILS (see 3.3), Huxley-LV passes.
   * σ ∈ [σ*, τ]: **log-free density with coefficient ≤ 4.6 required** (sortie Z6). No
     dodge exists: any log factor here is fatal (RHS at σ = τ is O(1)), and any
     coefficient ≥ 1/B is fatal (level dies). Both proved impossible to relax during this
     assessment (three separate absorption/census schemes checked and rejected).
   * σ ∈ [τ, 1]: exceptional census (Z7) → members of 𝓓(x), removed from L in 3.1.

### 3.3 Why B = 21/100, and the exponent cliff

Level = 1/A − δ must exceed B, so the d-aspect coefficient of the density estimate must
satisfy **A < 1/B ≈ 4.76 throughout σ ∈ [σ_min, τ]**. Calibration facts (derived and
double-checked during this assessment):

* Raw Halász–Montgomery density (coefficient 3/(2σ−1), the cheapest known) is
  self-consistent **exactly at level 1/5**: 3/(1−2B) ≤ 1/B ⟺ B ≤ 1/5. The project's
  B > 1/5 floor sits precisely on the Halász wall. Any strict improvement over Halász on
  part of the range is mandatory; Huxley's large-values theorem (subdivision; needs only
  the mean-value theorem + Halász–Montgomery inequality, **no moments of L-functions**)
  gives coefficient 3/(3σ−1) ≤ 2.2 on σ ≥ 0.79 — big margin.
* Jutila-quality log-free (HB92 (1.4)): ∑_{χ mod q}N(σ,T,χ) ≪_ε (qT)^{(12/5+ε)(1−σ)},
  T ≥ 1 — the canonical citation ([Ju] = Jutila, *On Linnik's constant*, Math. Scand. 41
  (1977) 45–62; explicit-constant treatment: S. Graham, *On Linnik's constant*, Acta
  Arith. 39 (1981); pseudo-character simplification: Motohashi). We need ≤ 4.6 where
  they deliver 2.4: **a lossy formalization can burn a factor ~1.9 in the exponent and
  still win.** This is the margin the whole campaign rests on.
* Explicit-constant Gallagher-method estimates are **not** usable for Z6: Thorner–Zaman
  (2023) obtained Q-aspect exponent **99** (and 170) even after optimization; anything
  ≥ 1/B is dead. They ARE usable for the census Z7 (any exponent works there:
  |𝓓| ≤ 10^{88}·exp(99·(B+δ)·ρ) = O(1)).

**Kill-criterion for the campaign:** if the paper-math gate (sortie Z0b) cannot produce a
self-contained proof of Z6 with coefficient ≤ 4.6 on σ ≥ 0.79 (single modulus, T ≥ 2),
the assumption cannot be eliminated by this or any currently known route — 𝓓-structured
equidistribution at level > x^{1/5} *is* Linnik technology, full stop.

---

## 4. Phased sortie list

Sizing calibrated to this repo's past sorties (200–800-line files, one agent each,
cribbing published proofs). Names Z0–Z13. Dependencies in brackets. Risk:
E(asy)/M(edium)/H(ard)/R(esearch-risk).

### Phase 0 — paper-math gates (no Lean; both are GO/NO-GO)

* **Z0a. Constant ledger** [—] (M). Redo AGP (2.3)–(2.8) at B = 21/100, A = 9/2,
  δ = 1/100, ε = 1/4, T = log⁴x, with the σ-splits of §3.2 and *every* constant pinned
  (ρ, ν, γ₂, c₂, κ, C*, K). One LaTeX/markdown doc, 6–10 pp. All Phase-2/3 Lean
  statements are frozen from this doc. Failure mode: hidden constraint surfaces (e.g.
  the σ_min/coefficient interplay tightens); mitigations: B may retreat toward 0.205,
  A toward 4.7.
* **Z0b. Log-free density blueprint** [Z0a] (**R — campaign crux**). Self-contained
  lossy proof of Z6 (coefficient ≤ 4.6, σ ≥ 0.79, single modulus, T ≥ 2, d-uniform).
  Cribs, in order of preference: Graham (Acta Arith. 39, 1981 — explicit constants,
  English), Jutila (Math. Scand. 41, 1977), Motohashi's pseudo-character notes,
  Bombieri (Astérisque 18, Thm 14 environs), Tao 254A Notes 7 §1 (structure only — his
  exponents are deliberately enormous: detector lengths T^{500..1000}). Exploit: T
  polylog (t-aspect via PV), coefficient budget 4.6 vs literature 2.4, multiplicative
  constants unlimited. Deliverable: 10–20 pp with every lemma Lean-shaped.

### Phase 1 — elementary/sieve (parallel, start immediately)

* **Z1. 3.1 skeleton** [—] (M, ~500 lines). `pigeonhole_of_BMembership` (§1.4) from the
  `BMembership` structure + Brun–Titchmarsh + π-bounds as *hypotheses*: divisor-transfer
  lemma (3.1) (fiber-counting on `Nat.divisors`), the L′ construction (induction removing
  one prime per bad member), the pairs/pigeonhole count. Pure Finset/`Nat.ArithmeticFunction`.
* **Z2. Brun–Titchmarsh for progressions** [—] (M–H, ~800 lines). π(y; m, 1) ≤
  3y/(φ(m)·log(y/m)) for m ≤ y^{0.95}, m squarefree suffices (moduli are dq, d|L, q|L).
  From local `SelbergBound.lean` + two classical lemmas: ∑_{l≤ξ} μ²(l)/φ(l) ≥ log ξ and
  the coprimality-restriction factor m/φ(m). Crib PNT+ `BrunTitchmarsh.lean` (interval
  case, same sieve).
* **Z3. π/ψ/θ conversion pack** [—] (E–M, ~300 lines). Abel summation between π, θ, ψ
  (Mathlib `AbelSummation`, `Chebyshev`); π ≤ (log4+ε)y/log y; orthogonality
  decomposition ψ(y;d,a) = φ(d)^{−1}∑_χ χ̄(a)ψ(y,χ) (Mathlib
  `sum_char_inv_mul_char_eq`); imprimitive→primitive correction ≤ ω(d)·log y·log d.

### Phase 2 — L-function analytics (the classical mountain; crib PNT+ ζ-precedent)

* **Z4a. Growth bounds** [—] (M–H, ~600 lines). |L(s,χ)| ≤ C(d(2+|s|))^{c} on
  σ ≥ −1/2: PV + partial summation for σ ≥ ε; functional equation
  (`completedLFunction_one_sub`) + Γ-ratio bounds on vertical strips for σ < ε (needs
  complex Stirling-type bounds — check `Complex.Gamma` API; PNT+ `ZetaBounds` has the ζ
  analogues). Also |L(2+it,χ)| ≥ ζ(4)/ζ(2)-type lower bound (Euler product, easy).
* **Z4b. Zero counting** [Z4a] (M, ~400 lines). Unit-box counts
  n_χ(t₀) ≤ C·log(d(|t₀|+2)) via Jensen disks centered 2+it₀ (Mathlib
  `AnalyticOnNhd.sum_divisor_le` is tailor-made); sum to N(T,χ) ≤ CT log(d(T+2)) and
  (2.2): N(1/2,T,d) ≤ C·T·d·log(dT).
* **Z4c. Landau partial fractions** [Z4a, Z4b] (H, ~600 lines).
  L′/L(s,χ) = ∑_{|ρ−s₀|≤r} 1/(s−ρ) + O(log d(|t|+2)) on σ ∈ [−1/4, 3]. Borel–Carathéodory
  (Mathlib) + Jensen; NO Hadamard product needed. PNT+ `StrongPNT` did this for ζ.
* **Z5. Explicit formula for ψ(y,χ)** [Z4a–c] (**H, the biggest classical sortie**;
  2 files, ~1600 lines total). Perron with sharp cutoff (crib PNT+ `PerronFormula`,
  `ResidueCalcOnRectangles`, `RectangleArgumentPrinciple` — all exist), rectangle to
  Re s = −1/4, good horizontal lines via Z4b, trivial-zero row via functional equation.
  Output as in §1.4 (β ≥ 1/2 folding via Z4b crude count, error √y·log²(dT)).
  d-uniformity is the only new content vs PNT+.

### Phase 3 — densities (the novel mountain; nothing like this exists in any prover)

* **Z6a. Single-modulus mean-value theorem + Gallagher lemma** [—] (M, ~500 lines).
  ∑_{χ mod d} ∫_{−T}^{T} |∑_{n≤N} a_n χ(n) n^{−it}|² dt ≤ C(N + dT)·∑|a_n|² via
  orthogonality + Gallagher's L² lemma (short-interval smoothing).
* **Z6b. Halász–Montgomery + Huxley large values (single modulus, T polylog)** [Z6a]
  (H, ~700 lines). Off-diagonal via PV + partial summation (|t| ≤ polylog keeps this
  soft). Output: the large-values bound R ≪ GNV^{−2} + G³NTV^{−6}·(dT)^{o(1)}.
* **Z6c. Zero detector** [Z0b, Z4a] (H, ~500 lines). Mollified/pre-sifted detector per
  Z0b: coefficients (μ_{≤X}*1), pre-sifting set, |detector(ρ)| ≥ 1/2 at any zero with
  β ≥ 0.79, |γ| ≤ T, from the truncated-L bound (Z4a PV-truncation).
* **Z6d. THE log-free density** [Z0b, Z6a–c] (**R — flagship risk**; 1–3 files,
  ~800–2000 lines). ∑_{χ mod d} N(σ,T,χ) ≤ γ₂(dT^{c₀})^{(9/2)(1−σ)}, σ ≥ 79/100, T ≥ 2.
  Includes the logged range as a by-product (single machine per Z0b).
* **Z7. Census** [Z6a or TZ-crib] (H, ~700 lines). ∑_{d′≤Z}∑*_{χ} N(σ,ν,χ) ≤ c₂Z^{c₃(1−σ)}
  for σ ≥ 39/40, any c₃. Crib Thorner–Zaman 2208.11123 (fully explicit, Gallagher
  method + Turán power-sum lemma) with maximal loss-taking, OR aggregate Z6d's machinery
  with the classical (N+Q²) large sieve. Needs: multiplicative large sieve over q ≤ Z
  (new, M) and possibly a Turán power-sum lemma (elementary, M).
* **Z8. ζ box clearance** [—] (E, ~150 lines). For large x, ζ has no zero in
  [τ,1]×[−ν,ν]: Mathlib nonvanishing + `IsCompact.inter_riemannZetaZeros_finite`.

### Phase 4 — assembly

* **Z9. T2.1 assembly** [Z0a, Z3, Z4b, Z5, Z6d, Z7, Z8] (H, ~800 lines). The (2.4)–(2.8)
  σ-integration bookkeeping producing `BMembership (21/100)`; includes d = 1 ⇒ PNT ⇒
  π(y) ≥ (1−ε)y/log y.
* **Z10. Splice** [Z1, Z2, Z3, Z9] (M, ~300 lines). `pigeonhole_of_BMembership` applied;
  produce the exact `Assumptions.pigeonhole` field shape at B = 21/100.
* **Z11. B-generic pass downstream** [Z10] (M — user-owned). `Defs/Step3/Budget/Main`:
  x = L⁵ still works (divisors ≤ x^{1/5} < x^{21/100}); the k-bound relaxes to
  k ≤ x^{79/100}; re-verify `Budget.lean` op-count with the larger k range and the
  `Extraction` window x^{N*}.

**Totals:** 2 paper-math gates + ~18–20 Lean sorties ≈ 12–15k lines. Critical path:
Z0a → Z0b → Z6c/d → Z9 → Z10. Phases 1 and 2 are parallel to Phase 0/3 up to statement
freezing.

**Single highest-risk piece: Z6d** (log-free zero-density, coefficient ≤ 4.6 on
σ ≥ 0.79). It has never been formalized in any prover, the published proofs
(Jutila/Graham/Motohashi) are dense 1970s analytic number theory, and — unlike every
other sortie — it has a hard *exponent* ceiling that lossy formalization cannot buy back
beyond factor ~1.9. Second: Z0b itself (the blueprint may take longer than any Lean
file). Third: Z5 (explicit formula d-uniformly; mitigated by the complete PNT+
ζ-precedent).

---

## 5. Hedge: Route S (smooth-moduli), and open questions

### Route S sketch (viable-but-holed)

The application's L is (log x)^{1+o(1)}-smooth (prime factors ≤ zscale = O(ℓ₂ℓ₃);
verified in `Defs.lean`). Task item 3(d) invites adding `P⁺(L) ≤ (log x)^2` to the
assumption. Then all conductors d′|L are squarefree and ultra-smooth, and
Graham–Ringrose-type iterated character-sum bounds give cancellation in ∑_{n≤N}χ(n) for
log N ≍ (log d′)^{θ'}, θ' < 1, hence a **complex-zero-free region of width
(log x)^{−θ'} ≫ loglog x/log x** for all such χ — wide enough to delete sortie Z6d *for
complex zeros* entirely (the [σ*,1] zone becomes zero-free; Z7 + removal handles [τ,1]).
**The hole: real (quadratic) characters.** Character-sum zero-free regions never exclude
real zeros; the elementary repulsion β ≤ 1 − c/(√d′·log²d′) clears only d′ ≤ log^{2−ε}x;
and a census of quadratic χ with zeros in [σ*, τ] over conductors up to x^{0.22} again
needs a log-free-type estimate with coefficient < 1/B — now only for the quadratic
family (size Z, not Z²), where Heath-Brown's quadratic large sieve might make it easier,
but that is itself research-grade. **Decision: do not base the campaign on Route S; keep
it as the fallback if Z0b stalls, and as a potential Z6d-simplifier (restricting Z6d to
quadratic characters only, with GR covering the rest).**

### Open questions (tracked; owners = Z0a/Z0b agents)

1. **Z0b existence proof**: exact coefficient achievable by the simplest pre-sifted
   detector at σ ≥ 0.79 with T polylog. Needs Graham 1981 / Jutila 1977 in hand (paper
   copies; neither is online-searchable in detail). If > 4.6 but < 5: retreat B toward
   1/5 + ε and re-run Z0a (works for any coefficient < 5 — B is only pinned from below
   by the *user's* structural floor 1/5, strictly).
2. Does Z6b's Huxley large-values route at σ near 0.79 survive the pre-sifting
   modification log-free, or does Z0b's blueprint bifurcate (logged Huxley on
   [0.79, σ*] + separate log-free on [σ*, τ])? Both architectures are budgeted in §3.2;
   the bifurcated one is likelier and adds ~1 sortie.
3. Complex-Stirling/Γ-ratio API adequacy in pinned Mathlib for Z4a (if thin, +1 easy
   sortie porting from PNT+ `ZetaBounds`).
4. Whether `Assumptions.pigeonhole`'s hypothesis set should, during the B-generic pass,
   also gain `P⁺(L) ≤ (log x)^2` (free for downstream) to keep Route S open as mid-course
   correction. Recommended: yes, add it — costs nothing, preserves optionality.
5. Census Z7 alternative: derive from Z6d aggregated instead of TZ-crib (saves the Turán
   lemma + all-moduli large sieve; costs re-plumbing Z6d to primitive-conductor families).
   Decide after Z0b.

---

## 6. What NOT to build (explicit de-scoping)

Vaughan's identity; Gauss-sum/primitive-character transfer for the large sieve;
Siegel–Walfisz; Siegel's theorem; Landau–Page; Deuring–Heilbronn repulsion; Hadamard
factorization; 4th moments / approximate functional equation of L-functions; BV itself.
None are on the critical path of Route Z. Any agent proposing them is off-plan.
