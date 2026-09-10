# Lean formalization of carmichael.tex

A Lean 4 / Mathlib formalization of *"A deterministic quasi-polylogarithmic
algorithm for constructing Carmichael numbers"* (`../carmichael.tex`). The
headline theorem is unconditional (no hypotheses beyond Lean's three standard
axioms) and is stated in Mathlib's Turing-machine model: an explicit
multi-stack machine which, given `n` in binary, outputs a Carmichael number in
`(n, n^{1+ε}]` together with its complete prime factorization, in time
`exp(C · log N · log log N)` for inputs of `N` bits. Everything in the
dependency tree is proved here or in Mathlib, including the two analytic
inputs the paper cites from Alford, Granville and Pomerance.

## The theorem

`Carmichael/Main.lean` (40 lines) contains one definition and one theorem:

```lean
def encodeOutput : ℕ × List ℕ → List Γ'
  | (m, S) => (encodeNat m).map inclusionBoolΓ' ++ Γ'.comma ::
      S.flatMap (fun p => (encodeNat p).map inclusionBoolΓ' ++ [Γ'.comma])

theorem main_theorem :
    ∃ (f : ℕ → ℕ × List ℕ)
      (h : TM2ComputableInTime encodingNatΓ'.encode encodeOutput f),
      (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
          (h.time N : ℝ) ≤ Real.exp (C * Real.log N * Real.log (Real.log N))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
          (f n).2.Nodup ∧ (∀ p ∈ (f n).2, p.Prime) ∧ 3 ≤ (f n).2.length ∧
          (f n).1 = (f n).2.prod ∧
          (1 < (f n).1 ∧ ¬ (f n).1.Prime ∧
            ∀ a : ℤ, ((f n).1 : ℤ) ∣ a ^ (f n).1 - a) ∧
          n < (f n).1 ∧ ((f n).1 : ℝ) ≤ (n : ℝ) ^ (1 + ε))
```

`TM2ComputableInTime`, `FinTM2`, `encodingNatΓ'`, `Γ'`, `encodeNat`,
`inclusionBoolΓ'`, `Nodup`, `Prime`, `prod` are Mathlib's. The Carmichael
property is inlined (composite, and `m ∣ a^m − a` for every integer `a`).
The input length is `N = ⌊log₂ n⌋ + 1`, so the time bound is
`exp(O(log log n · log log log n))`; the proof gives `C = 2000`. The machine
has eight stacks over Mathlib's alphabet `Γ'`. `#print axioms main_theorem`
reports `[propext, Classical.choice, Quot.sound]`.

## The layers

Six audited theorems, each implied by the next. All are kept and all are
guarded by `AxiomCheck.lean`.

| theorem | file | hypotheses | statement |
|---|---|---|---|
| `carmichael_exists_of_assumptions` | `ExistsOfAssumptions.lean` | AGP Theorem 3 at `E = 1/3` and Theorem 3.1 at `B = 2/5`, as a structure `Assumptions` | existence of `m ∈ (n, n^{1+ε}]` with factorization, plus the paper's operation budget `opBudget ≤ exp(C ℓ₂ℓ₃)` |
| `carmichael_exists_of_assumptionsWeak` | `ExistsOfAssumptionsWeak.lean` | AGP Theorem 3.1 only (`AssumptionsWeak`) | the same at the sieve-delivered smoothness exponent `Eweak` |
| `carmichael_exists_of_loggedDensity` | `Exists.lean` | a zero-density estimate for Dirichlet `L`-functions (`LoggedDensity`) | the same |
| `carmichael_exists` | `Exists.lean` | none | the same |
| `carmichael_search_alg` | `SearchAlg.lean` | none | the algorithm as a computable Lean function `Alg.search` with a built-in operation counter: it succeeds for all large `n` and charges at most `exp(100 ℓ₂ℓ₃)` |
| `main_theorem` | `Main.lean` | none | the Turing machine above; the machine refines `Alg.search` exactly, step by step |

## Files

`Carmichael/` holds 77 modules and `Carmichael/TM/` 16, about 83,000 lines
in all. Grouped by role:

**Statement, definitions, assembly**

| file | contents |
|---|---|
| `Defs.lean` | `IsCarmichael`, the scales `z, y, T`, reservoir, `L`, `x = L⁵`, `λ(L)`, `N*`, pool |
| `Main.lean` | `encodeOutput`, `main_theorem` |
| `TM/MainProof.lean` | the machine `searchTM`, its `TM2ComputableInTime` structure, the time function, both clauses |
| `SearchAlg.lean` | `carmichael_search_alg`, `search_successW` (the windowed form consumed by the machine layer), `carmichaelSearch` |
| `Exists.lean` | `carmichael_exists`, `carmichael_exists_of_loggedDensity`, `pigeonhole_unconditional` (AGP Theorem 3.1 at `B = 21/100` with no hypothesis) |
| `ExistsOfAssumptions.lean`, `ExistsOfAssumptionsWeak.lean` | the two conditional theorems |
| `Assumptions.lean`, `WeakE.lean` | the assumption packs and the weak-exponent constants (`Eweak`, `gammaWeak`, `C₁weak`) |
| `Lemmas.lean` | re-exports the Section 4 lemmas |

**Elementary inputs, proved here**

| file | contents |
|---|---|
| `Korselt.lean` | Korselt's criterion, both directions |
| `ZeroSum.lean` | the van Emde Boas–Kruyswijk zero-sum theorem (AGP's character-theoretic proof); to our knowledge the first formalization in any prover |
| `PrimeCount.lean` | Chebyshev: `π(z) ≥ z/(3 log z)` eventually, from Mathlib's bounds on `ψ` |
| `RecipSum.lean` | `∑_{w<p≤z} 1/p` from Mertens' first theorem |
| `Mertens.lean`, `EulerMaclaurin.lean` | vendored Mertens' first theorem and its Euler–Maclaurin helper, ported from PrimeNumberTheoremAnd via anthropics/zeta-23-lean (Apache 2.0; provenance and modifications in the file headers) |

**The five step lemmas of the paper's Section 4**, in three forms: exact
scales (`Step2`, `Step3`, `Extraction`, `Output`, `Budget`), generic
smoothness exponent `E` (`Step2E`, `Step3E`, `ExtractionE`, `OutputE`,
`BudgetE`, helper `LogPow`), and windowed scales for the machine, which can
only compute the scales up to constant factors from bit lengths (`DefsW`,
`Step2W`, `Step3W`, `ExtractionW`, `OutputW`).

**AGP Theorem 3 (smooth shifted primes), weak form, by sieve**

| file | contents |
|---|---|
| `SelbergBound.lean` | the fundamental theorem of the Selberg sieve, completing Mathlib's `NumberTheory.SelbergSieve` |
| `TwinSieve.lean` | uniform twin-type bound `#{q ≤ t : q, mq+1 prime} ≤ C₀ (m/φ(m))² t / log² t` |
| `TotientSum.lean`, `TotientSumSq.lean`, `DivisorMean.lean` | totient and divisor-power mean values |
| `SmoothShifted.lean` | `smooth_shifted_weak`: for some `E ∈ (0, 1/2]`, a positive proportion of `p ≤ x` have `p − 1` free of prime factors above `x^{1−E}` |

**AGP Theorem 3.1 (pigeonhole over shifts), unconditional, by zero density**

| file | contents |
|---|---|
| `LGrowth.lean`, `ZeroCount.lean`, `PartialFractions.lean` | growth bounds, zero counting and the Landau partial-fraction expansion of `L′/L` for Dirichlet `L`-functions, uniform in the modulus |
| `LConvexity.lean`, `LConvexityCorollaries.lean` | the convexity bound |
| `PerronKernel.lean`, `ExplicitFormula.lean` | rectangle contour integrals and the truncated explicit formula |
| `ZetaZeroFree.lean`, `ZetaBox.lean`, `PsiTheta.lean` | the de la Vallée Poussin zero-free region, ζ box clearance, π/ψ/θ conversions |
| `GammaStrip.lean` | Γ-function bounds on a strip |
| `MeanValue.lean`, `LargeValues.lean` | mean value and large-values estimates for character-twisted Dirichlet polynomials (Halász–Montgomery, Huxley) |
| `Detector.lean`, `Detection.lean`, `DetectionShift.lean`, `DetectionShiftHalf.lean` | the pre-sifted zero detector and the discharge of its interface hypotheses |
| `LoggedParams.lean`, `LoggedDetector.lean`, `LoggedDensity.lean` | the logged zero detector and the logged zero-density theorem `loggedDensity` |
| `GramFunction.lean`, `Representatives.lean`, `BVL2.lean`, `ZeroDensity.lean`, `DensityInterface.lean` | the log-free zero-density theorem: Gram function, well-spaced representatives, the Barban–Vehov `L²` bound, the assembly `logfree_of_logged` |
| `TuranPowerSum.lean`, `LargeSieve.lean`, `SmallDiskZeroCount.lean`, `KDerivDetect.lean`, `Census.lean`, `CensusMid.lean` | Turán power sums, the pre-sifted multiplicative large sieve (Gallagher), zero mass in small disks, the `k`-th logarithmic-derivative detector, and the exceptional-zero census |
| `BrunTitchmarsh.lean`, `T21.lean`, `BMembership.lean`, `BMembership21.lean` | Brun–Titchmarsh in the progression `1 mod m`, the θ-in-progressions bound with exceptional set, and AGP's `𝓑`-membership at `B = 21/100`, ending in `pigeonhole_unconditional` |

**The algorithm as a Lean function**

| file | contents |
|---|---|
| `Algorithm.lean` | `Alg.search : Scales → ℕ → Option (ℕ × List ℕ) × ℕ`, a plain computable `def` of the paper's five steps with an operation counter; trial division for primality; no `Nat.Prime`, `Finset`, `Real` or `Classical` in the code |
| `AlgScan.lean`, `AlgExtract.lean`, `AlgBudget.lean` | correctness and cost of every primitive and step against the Mathlib predicates; `costPieces ≤ exp(100 ℓ₂ℓ₃)` in the window |
| `ScalesTM.lean` | `scalesTM C₁ K n`, the scales computed from bit lengths only, and the proof they lie in the window |

**The machine**

| file | contents |
|---|---|
| `TM/Frag.lean`, `TM/Cost.lean` | the fragment framework on Mathlib's `TM2`: fragments with an exit continuation, `Runs` (a Hoare triple with a step bound), `seq`, `loop`, closing to `FinTM2`; the per-tick budget `B b = 64 (b+2)³` |
| `TM/Arith.lean`, `TM/Sub.lean`, `TM/MulDiv.lean`, `TM/Prims.lean`, `TM/Canon.lean` | binary arithmetic on stacks: add, compare, subtract, multiply, divide with remainder, increment, decrement, bit length, powers of two, canonical forms |
| `TM/Lists.lean`, `TM/Table.lean` | lists of numbers and the residue table of step 4 |
| `TM/PrimTD.lean`, `TM/PrimList.lean`, `TM/Steps23.lean`, `TM/Step4.lean`, `TM/Step5.lean` | exact refinements of every `Alg.*` function: each fragment's output equals the Lean function's output and its step count is `(ticks + 1) · B(bits)` |
| `TM/Overhead.lean` | the real analysis turning the machine's polynomial overhead into `exp(O(ℓ₂ℓ₃))` and building the length-indexed time function |

`AxiomCheck.lean` is the `#guard_msgs` harness over 25 declarations.

## Design decisions

* **Nothing is postulated.** The conditional theorems take their inputs as a
  structure argument, never as global axioms; the unconditional theorems
  discharge that structure.
* **Two cost models, one refinement.** `Alg.search` charges one unit per
  loop-body execution; the machine's step count is that count times a
  polynomial in the bit lengths, proved fragment by fragment. `main_theorem`
  is therefore a statement about Mathlib's step counter, not about a cost
  convention.
* **Windowed scales.** The machine cannot evaluate `⌈C₁ ℓ₂ ℓ₃⌉` exactly, so it
  computes scales from bit lengths that lie within constant factors of the
  paper's, and the step lemmas are proved for every scale in that window.
* **Parameters of the unconditional proof.** The sieve gives Theorem 3 for
  some `E ∈ (0, 1/2]` rather than every `E < 5/12`, and the zero-density
  route gives Theorem 3.1 at `B = 21/100`, the least value with
  `L = x^{1/5} ≤ x^B`. The paper's `E = 1/3`, `B = 2/5` are used only by
  `carmichael_exists_of_assumptions`.
* **"For n large" is `∀ᶠ n in atTop`**, and `n^{1+o(1)}` is
  `∀ ε > 0, … ≤ n^{1+ε}`. The constants `C`, `n₀`, `N₀` and the machine's
  scale constants are existential; the last enter through `Classical.choice`.

## How to verify

Machine half: `make verify` from the repo root. It runs the full
kernel-checked build, then `AxiomCheck.lean` asserts via `#guard_msgs` that
every audited declaration depends only on `propext`, `Classical.choice`,
`Quot.sound`. Trust base: the Lean kernel, Mathlib, and the pinned toolchain.

Human half, for `main_theorem`: read `Carmichael/Main.lean` (the statement
uses only Mathlib names) and the `main_theorem` entry of `AxiomCheck.lean`.
For the conditional layer add `Carmichael/Assumptions.lean`, the one place a
transcription of AGP 1994 could go wrong.

## Building

```
lake exe cache get   # prebuilt Mathlib (~5 GB)
lake build           # Carmichael and AxiomCheck; zero sorries, zero warnings
```

Pinned: Lean `v4.33.1`, Mathlib `v4.33.1`.

## Status

Complete. Open directions: a smaller time constant than `C = 2000`; explicit
`n₀`, which needs explicit constants in the zero-density inputs; upstreaming
to Mathlib (`korselt`, `vebk`, the Selberg sieve fundamental theorem, the
`TM2` fragment framework).
