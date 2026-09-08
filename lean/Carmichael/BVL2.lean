/-
Route Z, sortie ZBV: the Barban–Vehov `L²` bound (interface I4).
Blueprint: routez/Z0b-density.md §2 (I4), §12.2.
Crib: O. Ramaré and S. Zuniga-Alterman, "An L²-bound for the Barban–Vehov
weights", arXiv:2405.12662 (`routez/sources/bv-l2-2024.pdf`), Corollary 1.3
(their `(X, d)` is our `(Y, δ)`).

DELIVERED (fully proved, no `sorry`, no `axiom`, no `native_decide`):

* `mCheck q σ X` — RZA's `m̌_q(X, σ) = ∑_{n ≤ X, (n,q)=1} μ(n) n^{-σ} log(X/n)`.
* `hyperbola_sum` — the Dirichlet-hyperbola reindexing
  `∑_{n ≤ N} ∑_{m ≤ N/n} f n * g m = ∑_{k ≤ N} ∑_{d ∣ k} f d * g (k/d)`.
* `abs_mHarm_le_one` — `|∑_{n ≤ X} μ(n)/n| ≤ 1` for `X ≥ 1` (elementary, from
  `∑_{n ≤ X} μ(n)⌊X/n⌋ = 1`).
* `abs_mCheck1_le` — `|m̌_1(X, 1)| ≤ 11/3` for `X ≥ 1`.
* `abs_mCheck_sigma_le` — `|m̌_1(X, σ)| ≤ (11/3)(1 + (σ−1) log X)` for `X ≥ 1`,
  `σ ≥ 1`.  Together these are the `q = 1` upper half of RZA's Lemma 3.1, with
  the weaker constant `11/3` in place of their `1.00303`, and proved here FROM
  SCRATCH: RZA quote this from their reference [7] (arXiv:2312.05138), which is
  the one external paper the blueprint's I4 audit flagged.  The route is
  elementary — the hyperbola identity `∑_{n ≤ X} (μ(n)/n) H_{⌊X/n⌋} = 1`,
  `|∑_{n ≤ X} μ(n)/n| ≤ 1`, Mathlib's `eulerMascheroniSeq n < γ <
  eulerMascheroniSeq' n`, and one Taylor-with-integral-remainder step in the
  cut variable `w = log(X/X')`.
* `rankin_alpha` — the α-reduction `∑_{n ≤ Y} n^{1-2α} f(n)² ≤ Y^{2-2α}
  ∑_{n ≤ Y} f(n)²/n` for `α ≤ 1`.  This is the entire content of RZA
  Corollary 1.3 given their Corollary 1.2.
* `bvL2_alpha` — the FROZEN I4 general form, from the harmonic bound.
* `bvL2_star` — the FROZEN I4* specialisation at `τ* = 63/62` with the
  campaign's `z1par`/`z2par`/`ellpar`, constant `927`.
* `tauFactor_tauStar_le` / `tauFactor_tauStar_le_of_no_saving` — the audited
  numeral `62·(1.084·125/62 + 1.301(1 + 3969/3844) − 0.116) = 292.3 ≤ 300`,
  and the same bound `299.4 ≤ 300` with the `−0.116` saving DELETED.
* `zetaR` / `zetaR_le` — `ζ_R(σ) = ∑'_{n:ℕ} n^{-σ} ≤ 1 + 1/(σ−1)` for `σ > 1`
  (telescoping `(σ−1)n^{-σ} ≤ (n−1)^{1−σ} − n^{1−σ}` from
  `(1−1/n)^{-(σ-1)} ≥ 1 + (σ−1)/n`).
* THE SELBERG DIAGONALISATION, RZA (9)–(11) over `tsum`s: `bvA_eq_sum_Icc`
  (`a(n) = ∑_{d ≤ ⌊z₂⌋₊} [d∣n] λ_d`), `tsum_rpow_bvA_sq`
  (`∑'_n n^{-σ} a(n)² = ζ_R(σ) ∑_{d,e ≤ z₂} λ_d λ_e lcm(d,e)^{-σ}`),
  `Ssum` with `sum_lcm_eq_sum_phiSig_Ssum_sq` (`… = ∑_{δ ≤ z₂} φ_σ(δ) S_δ²`),
  `Ssum_eq_mCheckQ` (`S_δ = μ(δ) δ^{-σ}(m̌_δ(z₂/δ,σ) − m̌_δ(z₁/δ,σ))/log(z₂/z₁)`),
  the bound `abs_Ssum_le`, and the assembled `tsum_rpow_bvA_sq_le`
  (`∑'_n n^{-σ} a(n)² ≤ ζ_R(σ)·(484/9)(1+(σ−1)log z₂)²/log²(z₂/z₁)·8(1+log⌊z₂⌋₊)`).
* `sum_bvA_sq_div_le_tsum` — Rankin at `σ = 1 + 1/log Y`:
  `∑_{n ≤ Y} a(n)²/n ≤ e · ∑'_n n^{-σ} a(n)²` (`Y^{1/log Y} = e`).
* `bvHarm_uncond` — the UNCONDITIONAL harmonic bound at the campaign cuts:
  `∑_{n ≤ Y} a(n)²/n ≤ 5·10⁵ · log Y / ℓ` for `Y ≥ z₁`, `z₁ ≥ 100`.  This
  DISCHARGES `hharm` (at the crude constant, not at RZA's `3.09·τ`-form).
* `bvL2_star_uncond` — **UNCONDITIONAL I4***, the Z0b §2 re-freeze at ceiling
  `5·10⁵`: `∑_{n ≤ Y} n^{1−2α} a(n)² ≤ 5·10⁵ · Y^{2−2α} · log Y / ℓ` for
  `α ∈ [1/2, 1]`, `Y ≥ z₁`, `z₁ ≥ 100`, with NO hypothesis beyond the cuts.
  Audited assembled coefficient `e·1.2405·(484/9)(125/62)²·8·77.911 ≈ 4.6·10⁵`
  (`endgame_numeric`), inside the frozen ceiling.

DELTAS vs the blueprint's frozen I4 (all flagged at the statements):

1. HYPOTHESIS-IZED, NOW DISCHARGED.  `bvL2_alpha` and `bvL2_star` take RZA
   Corollary 1.2 (the harmonic bound `∑_{n ≤ Y} a(n)²/n ≤ 3.09 (log Y /
   log(z₂/z₁)) · f(τ)`) as an explicit hypothesis `hharm`; they are kept
   verbatim.  The four items behind it, in dependency order (ALL DONE — see
   the HANDOFF status below; `hharm` itself is discharged at the crude
   constant by `bvHarm_uncond`, giving the unconditional `bvL2_star_uncond`):
     (i)   the `q`-recursion for Lemma 3.1, i.e. `m̌_q(X) = m̌_{q/p}(X) +
           p^{-σ} m̌_q(X/p)` for `p ∣ q` prime, which by induction on `ω(q)`
           upgrades `abs_mCheck_sigma_le` to `|m̌_q(X,σ)| ≤ (q/φ(q))·(11/3)
           (1 + (σ−1)log X)` for squarefree `q` (the `∑_k p^{-k} = (1−1/p)^{-1}`
           telescoping is exactly the `q/φ(q)` factor);
     (ii)  RZA Lemma 3.2, the `U(Y)` estimate (a divisor-expansion of
           `μ²(δ)(δ/φ(δ))²` plus one convergent Euler product);
     (iii) the Selberg diagonalisation RZA (9)–(11), over `tsum`s;
     (iv)  Rankin's trick at `σ = 1 + 1/log Y` together with `∑_n n^{-σ} ≤
           1 + 1/(σ−1)`.
   Only (iii) is analytically heavy; (i), (ii), (iv) are finite algebra.
   Everything downstream of `hharm` is proved here, and `hharm` is now
   discharged unconditionally at the crude constant (`bvHarm_uncond`).
2b. `3.09` IS NOT REPRODUCIBLE IN PINNED MATHLIB.  `3.09 ≥ e^{1 + γ/log 100}`
   needs `γ ≤ 0.590`; pinned Mathlib offers only `1/2 < γ < 2/3`
   (`Real.eulerMascheroniConstant_lt_two_thirds`), which yields `3.143`.
   Sharpening needs `γ < H_n − log n` at `n ≥ 40` plus explicit `log n` bounds.
   With the elementary `ζ(σ) ≤ 1 + 1/(σ−1)` instead of `ζ(σ) ≤ e^{γε}/ε` the
   prefactor is `e(1 + 1/log z₁) ≤ 3.38`, giving `3.38 · 300 = 1014` in place
   of `927`.  Neither substitution has been made in the frozen statements
   above: they carry RZA's `3.09` verbatim, inside `hharm`.
2. RZA Corollary 1.3 as printed DOES support the frozen form verbatim; see the
   audit block below.
3. RZA Lemma 2.2 (the Chebyshev sum `∑_{p ≤ Y} (log p / p) log(Y/p) ≥
   0.318 log²Y`, whose proof is a Pari-GP verification on `[100, 10⁸]`) is NOT
   needed at `τ*`: it contributes only the `−0.116 = −C/e` saving, and
   `tauFactor_tauStar_le_of_no_saving` shows the frozen `≤ 300` survives with
   `C := 0` (`299.4 ≤ 300`).  No Chebyshev/`ϑ` input is used in this file.

AUDIT of the frozen numerals against RZA as printed (p. 2, Cor. 1.2/1.3):

* `3.09 = e^{1 + γ/log 100}` (`= 3.0813…`), from `X^ε ζ(σ) ≤ e·e^{γ/log X}/ε`
  with `ε = 1/log X` and `X ≥ 100`.
* `−0.116` is `−C/e` with `C = 0.318` (`C/e = 0.116988…`), rounded towards
  zero, i.e. weakened.  The printed "`− Ce`" in RZA's display is a typeset
  fraction `C/e`; taking it literally (`−0.864`) would make the corollary
  FALSE-shaped (too strong).  The `u ↦ [B(1+τ²) − C e^{-u}]u` bound on
  `u = ε log z₁ ∈ (0,1]` is by monotonicity (`B(1+τ²) ≥ 2.602 > C`), not by
  bounding the two factors separately.
* At `τ* = 63/62`: `1.084·(125/62) + 1.301·(1 + 3969/3844) − 0.116 = 4.71379…`,
  times `1/(τ*−1) = 62` gives `292.255… ≤ 300`, and `3.09 · 300 = 927`.

HANDOFF (sortie ZBV, COMPLETE; everything below is on disk and verified).

STATUS OF THE FOUR ITEMS BEHIND `hharm` (ALL DONE; `hharm` DISCHARGED at the
crude constant — `bvHarm_uncond`, `bvL2_star_uncond`, ceiling `5·10⁵`):

(i)  `q`-RECURSION → `q/φ(q)`: **DONE**, unconditional.  `mCheckQ q X σ` is
     `m̌_q(X,σ)`; `mCheckQ_rec` is `m̌_{q/p}(X) = m̌_q(X) − p^{-σ} m̌_q(X/p)` for
     prime `p ∣ q`, `q` squarefree; `abs_mCheckQ_le` is
     `|m̌_q(X,σ)| ≤ (q/φ(q))(11/3)(1 + (σ−1) log X)` for squarefree `q`, `X ≥ 1`,
     `σ ≥ 1`, by a lexicographic induction on `(q, ⌊X⌋₊)` (outer: least prime
     factor; inner: `⌊X/p⌋₊ < ⌊X⌋₊`).  Constant `11/3` inherited from
     `abs_mCheck_sigma_le`; NO non-negativity.
(ii) RZA LEMMA 3.2 (`U(Y)`): the infrastructure is **DONE in the crude form**
     that avoids `m̌ ≥ 0` — `sum_divisors_prod_primeFactors` (squarefree divisor
     expansion `∑_{a∣n} ∏_{p∣a} f p = ∏_{p∣n}(1 + f p)`), `phiSig` with
     `sum_divisors_phiSig` (identity RZA (9): `∑_{δ∣n} φ_σ(δ) = n^σ`, squarefree
     `n`) and `phiSig_le_rpow`, `div_totient_eq_prod`, `sq_div_totient_eq_sum`,
     `sum_squarefree_prod_le` (squarefree sum ≤ Euler product),
     `prod_one_add_uSeq_le` (`∏_{2≤n≤M}(1+u n) ≤ 8`, `u n = (2n−1)/(n(n−1)²)`),
     and `W_bound`:
       `∑_{δ ≤ M} μ²(δ) φ_σ(δ) δ^{-2σ} (δ/φ(δ))² ≤ 8 (1 + log M)`  (`σ ≥ 1`).
     RZA's own Lemma 3.2 is NOT formalised: its proof bounds ONE factor of
     `m̌_δ²` by the Lemma 3.1 upper bound and keeps the other signed, which needs
     `m̌ ≥ 0` (see the constant note below).
(iii) SELBERG DIAGONALISATION, RZA (9)–(11): **DONE**, exactly per the plan
     below — `bvA_eq_sum_Icc`, `tsum_rpow_bvA_sq` (via `tsum_rpow_multiples` =
     `Function.Injective.tsum_eq` along `n = mk`, swap by
     `Summable.tsum_finsetSum` over the product finset), `Ssum`,
     `sum_lcm_eq_sum_phiSig_Ssum_sq`, `Ssum_eq_mCheckQ`, `abs_Ssum_le`,
     `tsum_rpow_bvA_sq_le`.  The plan (kept as documentation), in the form
     that needs no coprimality bookkeeping (`D := ⌊z₂⌋₊`, `S_δ := ∑_{d ≤ D, δ∣d}
     λ_d d^{-σ}`):
       `a(n) = ∑_{d ≤ D, d∣n} λ_d`  (λ vanishes for `d ≥ z₂`);
       `a(n)² = ∑_{d,e ≤ D} λ_d λ_e [lcm(d,e) ∣ n]`;
       `∑'_n n^{-σ} a(n)² = ζ(σ) ∑_{d,e ≤ D} λ_d λ_e lcm(d,e)^{-σ}`
         (swap the finite square out of the `tsum`, then
          `∑'_{m ∣ n} n^{-σ} = m^{-σ} ζ(σ)` by `Function.Injective.tsum_eq`
          along `n = m k`);
       `∑_{d,e} λ_d λ_e lcm(d,e)^{-σ} = ∑_{δ ≤ D} φ_σ(δ) S_δ²`
         (insert `∑_{δ ∣ gcd(d,e)} φ_σ(δ) = gcd(d,e)^σ`; the filtered finset
          `(Icc 1 D).filter (δ ∣ d ∧ δ ∣ e)` equals `(gcd d e).divisors`; both
          sides vanish unless `d, e` squarefree, so `gcd` is squarefree;
          `de = gcd·lcm` via `Nat.gcd_mul_lcm`);
       `S_δ = μ(δ) δ^{-σ} (m̌_δ(z₂/δ,σ) − m̌_δ(z₁/δ,σ)) / log(z₂/z₁)`
         (reindex `d = δℓ`; note `⌊z₂⌋₊/δ = ⌊z₂/δ⌋₊` so the `ℓ`-range matches
          `mCheckQ` exactly, and `log⁺` kills `ℓ > z₁/δ` in the `z₁` term).
     Then `|S_δ| ≤ δ^{-σ}(δ/φ(δ))(11/3)·2(1+ε log z₂)/log(z₂/z₁)` and `W_bound`
     closes it.  No second `log Y` appears: the shape is
     `C · log X · log z₂ / log²(z₂/z₁)`, and at the campaign cuts
     `log z₂ = 63 ℓ`, so I4* keeps `C' · Y^{2−2α} log Y / ℓ` as frozen.
(iv) RANKIN AT `σ = 1 + 1/log Y`: **DONE** — `zetaR`, `zetaR_le` (route as
     parked: telescoping `(σ−1) n^{-σ} ≤ (n−1)^{1−σ} − n^{1−σ}` for `n ≥ 2`
     from `(1−1/n)^{-(σ−1)} ≥ exp((σ−1)/n) ≥ 1 + (σ−1)/n`, then
     `Real.tsum_le_of_sum_range_le`), and the Rankin step
     `sum_bvA_sq_div_le_tsum` (`n ≤ Y ⟹ n^{-1} ≤ Y^{σ−1} n^{-σ}`, then
     `Summable.sum_le_tsum`; `Y^{1/log Y} = e`).  The parked scratch at
     `routez/BVL2-scratch-zetaR.lean.txt` is SUPERSEDED by the in-file proof.

THE CONSTANT — RE-FROZEN AND DELIVERED at the unconditional crude route
(Z0b-density.md §2 ceiling `5·10⁵`; `bvL2_star_uncond` below):

RZA's Lemma 3.1 (`0 ≤ m̌_q ≤ 1.00303 (q/φ(q))(k + (σ−1)log X) log^{k−1}X`) is
quoted from [7] = arXiv:2312.05138, whose Theorem 1.1 (paper fetched to
`routez/sources/rza-identity-factory-2312.05138.pdf`) in turn quotes BOTH the
non-negativity and the `1.00303` from O. Ramaré, "Explicit estimates on several
summatory functions involving the Moebius function" [27, Cor. 1.10/1.11].  That
is a computation-heavy explicit-estimates paper; the non-negativity of
`∑_{n≤X}(μ(n)/n) log(X/n)` is NOT reachable from the identity used here
(`1 = m̌₁(X) + γ m(X) + R` with `|m(X)| ≤ 1`, `|R| ≤ 2` only gives
`|m̌₁| ≤ 11/3`; even the best form of this route, `|R| ≤ 0.83`, gives
`|m̌₁| ≤ 2.5`, never a sign).

Consequences, quantified:
* Non-negativity is exactly what lets RZA write `m̌² ≤ (upper bound)·m̌` and keep
  the Möbius cancellation in the second factor, giving `U(Y) ≤ (1.084 +
  1.301 ε log Y) log Y`.  Without it the only route is `m̌² ≤ (upper bound)²`,
  which (a) squares the Lemma 3.1 constant and (b) replaces the `1.08` by
  `∑_{δ≤Y} μ²(δ) δ/φ(δ)² ≤ 8(1 + log Y)` (`W_bound`).
* With `κ = 11/3` the assembled harmonic bound is about
  `866 · (1 + ε log z₂)² · log X · log z₂ / log²(z₂/z₁)`, i.e. at `τ* = 63/62`
  roughly `4.4·10⁵ · log X / ℓ` in place of the frozen `1014`.
* With the sharp input (`m̌ ≥ 0` and `1.00303`) the machinery in this file
  returns to RZA's own constants and the frozen `1014` stands.
The second (crude) route is what `bvL2_star_uncond` delivers: I4* is
UNCONDITIONAL at the constant `5·10⁵` (assembled coefficient
`e·1.2405·(484/9)(125/62)²·8·77.911 ≈ 4.6·10⁵`, `endgame_numeric`), matching
Z0b-density.md §2 as re-frozen there (consumer walk: the bump propagates only
through parametric constants — see the §2 note).  `bvL2_alpha`/`bvL2_star`
still carry `hharm` and are kept verbatim; should a later sortie formalise
Ramaré [27, Cor. 1.10] (non-negativity plus a usable constant), the machinery
in this file returns to RZA's own constants and the `1014` form is restored
by re-running blueprint Lemma 8.1 only.

MATHLIB v4.33.1 TRAPS HIT (beyond those already listed in the campaign notes):
* `Finset.prod_le_prod_of_subset_of_one_le'` needs `MulLeftMono`, which ℝ does
  not have — see the local `prod_le_prod_subset_one_le`.
* `div_le_div_of_nonneg_right'` does not exist; use `gcongr`.
* `Nat.Prime.not_unit` does not exist (`Irreducible.not_unit` is absent); use
  `Nat.isUnit_iff` + `omega`.
* The `tsum` upper bound is `Real.tsum_le_of_sum_range_le`.
* `Finset.sum_Icc_succ_top` is the induction step for `Icc`-indexed sums.
* `linarith` cannot combine hypotheses containing `a/(σ−1)`; multiply the
  statement through by `σ−1` before inducting.
-/
import Carmichael.Detector
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

namespace Carmichael
namespace BVL2

open Finset ArithmeticFunction
open scoped Real ArithmeticFunction.Moebius

/-! ### The τ-fraction and the frozen numerals -/

/-- RZA Corollary 1.2's `τ`-fraction
`(1.084(τ+1) + 1.301(1+τ²) − 0.116)/(τ−1)`. -/
noncomputable def tauFactor (τ : ℝ) : ℝ :=
  (1.084 * (τ + 1) + 1.301 * (1 + τ ^ 2) - 0.116) / (τ - 1)

/-- At `τ* = 63/62` the `τ`-fraction is `292.255… ≤ 300`.  (Blueprint I4: "the
`τ`-fraction is `62(1.084·125/62 + 1.301(1 + 3969/3844) − 0.116) = 292.3`".) -/
lemma tauFactor_tauStar_le : tauFactor (63 / 62) ≤ 300 := by
  rw [tauFactor]
  norm_num

/-- The same bound with RZA's Lemma 2.2 saving `−0.116` DELETED: even with
`C := 0` the `τ`-fraction at `τ*` is `299.4… ≤ 300`.  Hence no Chebyshev
`ϑ`-input is needed for I4*. -/
lemma tauFactor_tauStar_le_of_no_saving :
    (1.084 * ((63 / 62 : ℝ) + 1) + 1.301 * (1 + (63 / 62 : ℝ) ^ 2))
      / ((63 / 62 : ℝ) - 1) ≤ 300 := by
  norm_num

/-- `3.09 · 300 = 927`: the frozen I4* constant. -/
lemma const_tauStar_le : (3.09 : ℝ) * tauFactor (63 / 62) ≤ 927 := by
  have h := tauFactor_tauStar_le
  nlinarith [h]

/-! ### The α-reduction (RZA Corollary 1.3 from Corollary 1.2)

The whole content of Corollary 1.3 is that for `α ≤ 1` the exponent
`2 − 2α` is non-negative, so `n^{1−2α} = n^{2−2α}/n ≤ Y^{2−2α}/n` on `n ≤ Y`. -/

/-- **Rankin/α-reduction.**  For any `f : ℕ → ℝ`, any `Y ≥ 1` and any `α ≤ 1`,
`∑_{n ≤ Y} n^{1−2α} f(n)² ≤ Y^{2−2α} ∑_{n ≤ Y} f(n)²/n`. -/
lemma rankin_alpha {Y α : ℝ} (hY : 1 ≤ Y) (hα1 : α ≤ 1) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℝ) ^ (1 - 2 * α) * (f n) ^ 2
      ≤ Y ^ (2 - 2 * α) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (f n) ^ 2 / n := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro n hn
  simp only [Finset.mem_Icc] at hn
  obtain ⟨hn1, hnY⟩ := hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnY' : (n : ℝ) ≤ Y := by
    calc (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hnY
      _ ≤ Y := Nat.floor_le (by linarith)
  have hexp : (0 : ℝ) ≤ 2 - 2 * α := by linarith
  -- `n ^ (1 - 2α) = n ^ (2 - 2α) / n`
  have hsplit : (n : ℝ) ^ (1 - 2 * α) = (n : ℝ) ^ (2 - 2 * α) / n := by
    rw [eq_div_iff (ne_of_gt hn0)]
    nth_rewrite 2 [show (n : ℝ) = (n : ℝ) ^ (1 : ℝ) by rw [Real.rpow_one]]
    rw [← Real.rpow_add hn0]
    ring_nf
  have hmono : (n : ℝ) ^ (2 - 2 * α) ≤ Y ^ (2 - 2 * α) :=
    Real.rpow_le_rpow hn0.le hnY' hexp
  rw [hsplit]
  have hsq : (0 : ℝ) ≤ (f n) ^ 2 := sq_nonneg _
  rw [div_mul_eq_mul_div, mul_div_assoc]
  gcongr

/-! ### The frozen I4 statements

`bvL2_alpha` is the blueprint's frozen general form and `bvL2_star` is I4*.
Both take RZA Corollary 1.2 — the harmonic (`α = 1`) bound — as the explicit
hypothesis `hharm`; see DELTA 1 in the header. -/

section Frozen

open Detector

set_option linter.unusedVariables false

/-- **FROZEN I4 (general form).**  For the Barban–Vehov weights at cuts
`z₂ = z₁^τ`, `τ > 1`, any `Y ≥ z₁ ≥ 100` and any `α ∈ [1/2, 1]`,
`∑_{n ≤ Y} n^{1−2α} a(n)² ≤ 3.09 · Y^{2−2α} · (log Y / log(z₂/z₁)) ·
(1.084(τ+1) + 1.301(1+τ²) − 0.116)/(τ − 1)`,
given the corresponding harmonic bound `hharm` (RZA Corollary 1.2). -/
theorem bvL2_alpha {z1 z2 Y α τ : ℝ} (hτ : 1 < τ) (hz1 : 100 ≤ z1)
    (hz2 : z2 = z1 ^ τ) (hY : z1 ≤ Y) (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1)
    (hharm : ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (bvA z1 z2 n) ^ 2 / n
        ≤ 3.09 * (Real.log Y / Real.log (z2 / z1)) * tauFactor τ) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℝ) ^ (1 - 2 * α) * (bvA z1 z2 n) ^ 2
      ≤ 3.09 * Y ^ (2 - 2 * α) * (Real.log Y / Real.log (z2 / z1)) * tauFactor τ := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hpow : (0 : ℝ) ≤ Y ^ (2 - 2 * α) := Real.rpow_nonneg (by linarith) _
  calc ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℝ) ^ (1 - 2 * α) * (bvA z1 z2 n) ^ 2
      ≤ Y ^ (2 - 2 * α) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (bvA z1 z2 n) ^ 2 / n :=
        rankin_alpha hY1 hα1 _
    _ ≤ Y ^ (2 - 2 * α) *
          (3.09 * (Real.log Y / Real.log (z2 / z1)) * tauFactor τ) := by
        exact mul_le_mul_of_nonneg_left hharm hpow
    _ = 3.09 * Y ^ (2 - 2 * α) * (Real.log Y / Real.log (z2 / z1)) * tauFactor τ := by
        ring

end Frozen

/-! ### The campaign cuts: `τ* = 63/62`, `log(z₂/z₁) = ℓ` -/

/-- `z₂ = z₁^{63/62}` for the campaign's cuts: `(D^{31/50})^{63/62} = D^{63/100}`. -/
lemma z2par_eq_z1par_rpow {D : ℝ} (hD : 0 ≤ D) :
    Detector.z2par D = (Detector.z1par D) ^ (63 / 62 : ℝ) := by
  rw [Detector.z1par, Detector.z2par, ← Real.rpow_mul hD]
  norm_num

/-- `log(z₂/z₁) = ℓ`: the window width is exactly the blueprint's `ℓ = 𝓛/100`. -/
lemma log_z2par_div_z1par {D : ℝ} (hD : 0 < D) :
    Real.log (Detector.z2par D / Detector.z1par D) = Detector.ellpar D := by
  rw [Detector.z1par, Detector.z2par, ← Real.rpow_sub hD, Real.log_rpow hD,
    Detector.ellpar]
  norm_num

/-- `ℓ > 0` for `D > 1`. -/
lemma ellpar_pos {D : ℝ} (hD : 1 < D) : 0 < Detector.ellpar D := by
  rw [Detector.ellpar]
  have : 0 < Real.log D := Real.log_pos hD
  linarith

section FrozenStar

open Detector

set_option linter.unusedVariables false

/-- **FROZEN I4\*.**  At the campaign's cuts `z₁ = D^{31/50}`, `z₂ = D^{63/100}`
(so `τ* = 63/62` and `log(z₂/z₁) = ℓ`), for `Y ≥ z₁` and `α ∈ [1/2, 1]`:
`∑_{n ≤ Y} n^{1−2α} a(n)² ≤ 927 · Y^{2−2α} · log Y / ℓ`,
given the harmonic bound `hharm` (RZA Corollary 1.2 at `τ*`). -/
theorem bvL2_star {D Y α : ℝ} (hD : 1 < D) (hz1 : 100 ≤ z1par D)
    (hY : z1par D ≤ Y) (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1)
    (hharm : ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (bvA (z1par D) (z2par D) n) ^ 2 / n
        ≤ 3.09 * (Real.log Y / ellpar D) * tauFactor (63 / 62)) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℝ) ^ (1 - 2 * α) * (bvA (z1par D) (z2par D) n) ^ 2
      ≤ 927 * Y ^ (2 - 2 * α) * Real.log Y / ellpar D := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hpow : (0 : ℝ) ≤ Y ^ (2 - 2 * α) := Real.rpow_nonneg (by linarith) _
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hell : 0 < ellpar D := ellpar_pos hD
  have hratio : 0 ≤ Real.log Y / ellpar D := div_nonneg hlogY hell.le
  have hstep : ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℝ) ^ (1 - 2 * α) * (bvA (z1par D) (z2par D) n) ^ 2
      ≤ Y ^ (2 - 2 * α) *
          (3.09 * (Real.log Y / ellpar D) * tauFactor (63 / 62)) :=
    le_trans (rankin_alpha hY1 hα1 _) (mul_le_mul_of_nonneg_left hharm hpow)
  refine le_trans hstep ?_
  have hnum : (3.09 : ℝ) * tauFactor (63 / 62) ≤ 927 := const_tauStar_le
  have : Y ^ (2 - 2 * α) * (3.09 * (Real.log Y / ellpar D) * tauFactor (63 / 62))
      = (Y ^ (2 - 2 * α) * (Real.log Y / ellpar D)) * (3.09 * tauFactor (63 / 62)) := by
    ring
  rw [this]
  have hb : (0 : ℝ) ≤ Y ^ (2 - 2 * α) * (Real.log Y / ellpar D) :=
    mul_nonneg hpow hratio
  calc (Y ^ (2 - 2 * α) * (Real.log Y / ellpar D)) * (3.09 * tauFactor (63 / 62))
      ≤ (Y ^ (2 - 2 * α) * (Real.log Y / ellpar D)) * 927 :=
        mul_le_mul_of_nonneg_left hnum hb
    _ = 927 * Y ^ (2 - 2 * α) * Real.log Y / ellpar D := by
        field_simp

end FrozenStar

/-! ### RZA Lemma 3.1, the elementary core

RZA's Lemma 3.1 (`0 ≤ m̌_q(X,σ) ≤ 1.00303 (q/φ(q))(1 + (σ−1)log X)`) is quoted
from their reference [7] (arXiv:2312.05138).  What follows proves the `σ = 1`,
`q = 1` upper half from scratch, with the weaker constant `11/3` in place of
`1.00303`, using only:

* the Dirichlet-hyperbola reindexing `hyperbola_sum`;
* `∑_{d ∣ k} μ(d) = [k = 1]`;
* Mathlib's `eulerMascheroniSeq n < γ < eulerMascheroniSeq' n`, i.e.
  `log n < H_n − γ < log(n+1)`.

No Chebyshev, no prime number theorem, no Euler products. -/

/-- **Dirichlet hyperbola reindexing.**  Summing `f(n)g(m)` over `{(n,m) : nm ≤ N}`
fibred by `n` equals the same sum fibred by `k = nm`. -/
lemma hyperbola_sum (N : ℕ) (f g : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / n), f n * g m
      = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, f d * g (k / d) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun p => (⟨p.1 * p.2, p.1⟩ : (_ : ℕ) × ℕ))
    (j := fun p => (⟨p.2, p.1 / p.2⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    obtain ⟨⟨hn1, hnN⟩, hm1, hmN⟩ := hp
    have hn0 : 0 < n := hn1
    have hnm : n * m ≤ N := by
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le hn0).mp hmN
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), hnm⟩,
      ⟨Dvd.intro m rfl, by positivity⟩⟩
  · rintro ⟨k, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    obtain ⟨⟨hk1, hkN⟩, hdk, hk0⟩ := hp
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hk0 (zero_dvd_iff.mp hdk))
    have hdk' : d ≤ k := Nat.le_of_dvd hk1 hdk
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨⟨hd1, le_trans hdk' hkN⟩, ?_, Nat.div_le_div_right hkN⟩
    exact Nat.one_le_div_iff hd1 |>.mpr hdk'
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    have hn0 : 0 < n := hp.1.1
    simp [Nat.mul_div_cancel_left _ hn0]
  · rintro ⟨k, d⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    obtain ⟨⟨hk1, hkN⟩, hdk, hk0⟩ := hp
    simp [Nat.mul_div_cancel' hdk]
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hp
    have hn0 : 0 < n := hp.1.1
    simp [Nat.mul_div_cancel_left _ hn0]

/-- `∑_{d ∣ k} μ(d) = [k = 1]`. -/
lemma moebius_divisors_sum (k : ℕ) :
    (∑ d ∈ k.divisors, (μ d : ℤ)) = if k = 1 then 1 else 0 := by
  have h := (ArithmeticFunction.coe_mul_zeta_apply (f := μ) (x := k)).symm
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [h, ArithmeticFunction.one_apply]

/-- `∑_{k ≤ N} c k * [k = 1] = c 1` for `N ≥ 1`. -/
private lemma sum_Icc_indicator_one {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 N, c k * (if k = 1 then (1 : ℝ) else 0) = c 1 := by
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩) h

/-- **Identity (A).**  `∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1` for `N ≥ 1`. -/
lemma sum_moebius_mul_div_eq_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * ((N / n : ℕ) : ℝ) = 1 := by
  have h := hyperbola_sum N (fun n => (μ n : ℝ)) (fun _ => (1 : ℝ))
  have hL : ∑ n ∈ Finset.Icc 1 N, ∑ _m ∈ Finset.Icc 1 (N / n), (μ n : ℝ) * 1
      = ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * ((N / n : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun n _ => by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp [mul_comm])
  rw [hL] at h
  rw [h]
  have hin : ∀ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, (μ d : ℝ) * 1)
      = 1 * (if k = 1 then (1 : ℝ) else 0) := by
    intro k _
    simp only [mul_one]
    have hms := moebius_divisors_sum k
    have hcast : ((∑ d ∈ k.divisors, (μ d : ℤ) : ℤ) : ℝ) = ∑ d ∈ k.divisors, (μ d : ℝ) := by
      push_cast; ring
    rw [← hcast, hms]
    split <;> simp
  rw [Finset.sum_congr rfl hin, sum_Icc_indicator_one hN]

/-- **Identity (B).**  `∑_{n ≤ N} (μ(n)/n) H_{⌊N/n⌋} = 1` for `N ≥ 1`. -/
lemma sum_moebius_div_mul_harmonic_eq_one {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ((μ n : ℝ) / n) * (∑ m ∈ Finset.Icc 1 (N / n), (1 : ℝ) / m) = 1 := by
  have h := hyperbola_sum N (fun n => (μ n : ℝ) / n) (fun m => (1 : ℝ) / m)
  simp only [Finset.mul_sum] at h ⊢
  rw [h]
  have hin : ∀ k ∈ Finset.Icc 1 N,
      (∑ d ∈ k.divisors, ((μ d : ℝ) / d) * (1 / ((k / d : ℕ) : ℝ)))
        = (1 / (k : ℝ)) * (if k = 1 then (1 : ℝ) else 0) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk0 : k ≠ 0 := by omega
    have hterm : ∀ d ∈ k.divisors, ((μ d : ℝ) / d) * (1 / ((k / d : ℕ) : ℝ))
        = (1 / (k : ℝ)) * (μ d : ℝ) := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      obtain ⟨hdk, -⟩ := hd
      have hd0 : d ≠ 0 := by rintro rfl; exact hk0 (zero_dvd_iff.mp hdk)
      have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
      have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
      have hcast : (((k / d : ℕ)) : ℝ) = (k : ℝ) / (d : ℝ) := by
        exact_mod_cast Nat.cast_div hdk hdR
      rw [hcast]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    have := moebius_divisors_sum k
    have hcast : ((∑ d ∈ k.divisors, (μ d : ℤ) : ℤ) : ℝ) = ∑ d ∈ k.divisors, (μ d : ℝ) := by
      push_cast; ring
    rw [← hcast, this]
    split <;> simp
  rw [Finset.sum_congr rfl hin, sum_Icc_indicator_one hN]
  norm_num

/-- `m(X) = ∑_{n ≤ X} μ(n)/n`. -/
noncomputable def mHarm (X : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ) / n

/-- The fractional part `X/n − ⌊X⌋₊/n` lies in `[0, 1)`. -/
private lemma frac_bounds {X : ℝ} (hX : 0 ≤ X) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ X / n - ((⌊X⌋₊ / n : ℕ) : ℝ) ∧ X / n - ((⌊X⌋₊ / n : ℕ) : ℝ) < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfl : ((⌊X⌋₊ / n : ℕ) : ℝ) = ((⌊X / n⌋₊ : ℕ) : ℝ) := by
    rw [Nat.floor_div_natCast X n]
  rw [hfl]
  constructor
  · have := Nat.floor_le (show (0 : ℝ) ≤ X / n by positivity)
    linarith
  · have := Nat.lt_floor_add_one (X / n)
    linarith

/-- **`|m(X)| ≤ 1`.**  Elementary, from `∑_{n ≤ X} μ(n)⌊X/n⌋ = 1`: the `n = 1`
fractional part is `{X}` and the remaining `⌊X⌋ − 1` terms are each `< 1`. -/
lemma abs_mHarm_le_one {X : ℝ} (hX : 1 ≤ X) : |mHarm X| ≤ 1 := by
  set N := ⌊X⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNX : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hXN : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
  have hX0 : (0 : ℝ) < X := by linarith
  -- `X · m(X) = 1 + ∑ μ(n)·frac(X/n)`
  have hkey : X * mHarm X
      = 1 + ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ)) := by
    have hsplit : ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * (X / n)
        = ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * ((N / n : ℕ) : ℝ)
          + ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    have hXm : X * mHarm X = ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * (X / n) := by
      rw [mHarm, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [hXm, hsplit, sum_moebius_mul_div_eq_one hN1]
  -- peel off `n = 1`
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN1⟩
  have hpeel : ∑ n ∈ Finset.Icc 1 N, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ))
      = (X - (N : ℝ))
        + ∑ n ∈ (Finset.Icc 1 N).erase 1, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ)) := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    congr 1
    simp
  -- the remaining terms are each `< 1` in absolute value
  have hbnd : |∑ n ∈ (Finset.Icc 1 N).erase 1, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ))|
      ≤ (N : ℝ) - 1 := by
    have hcard : ((Finset.Icc 1 N).erase 1).card = N - 1 := by
      rw [Finset.card_erase_of_mem h1mem, Nat.card_Icc]
      simp
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ n ∈ (Finset.Icc 1 N).erase 1,
        |(μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ))| ≤ 1 := by
      intro n hn
      have hn' : n ∈ Finset.Icc 1 N := Finset.mem_of_mem_erase hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn').1
      obtain ⟨hf0, hf1⟩ := frac_bounds (le_of_lt hX0) n hn1
      rw [abs_mul, abs_of_nonneg hf0]
      have hmu : |(μ n : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [abs_nonneg ((μ n : ℝ))]
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
    rw [hcard, nsmul_eq_mul, mul_one]
    have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have : (1 : ℕ) ≤ N := hN1
      push_cast [Nat.cast_sub this]
      ring
    rw [this]
  -- assemble
  have habs : |X * mHarm X| ≤ X := by
    rw [hkey, hpeel]
    calc |1 + ((X - (N : ℝ))
            + ∑ n ∈ (Finset.Icc 1 N).erase 1, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ)))|
        ≤ |(1 : ℝ)| + |(X - (N : ℝ))
            + ∑ n ∈ (Finset.Icc 1 N).erase 1, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ))| :=
          abs_add_le _ _
      _ ≤ 1 + ((X - (N : ℝ)) + ((N : ℝ) - 1)) := by
          rw [abs_one]
          have h2 := abs_add_le (X - (N : ℝ))
            (∑ n ∈ (Finset.Icc 1 N).erase 1, (μ n : ℝ) * (X / n - ((N / n : ℕ) : ℝ)))
          have h3 : |X - (N : ℝ)| = X - (N : ℝ) := abs_of_nonneg (by linarith)
          linarith [hbnd, h2, h3]
      _ = X := by ring
  rw [abs_mul, abs_of_pos hX0] at habs
  nlinarith [abs_nonneg (mHarm X)]

/-! ### The Euler–Mascheroni comparison -/

/-- `∑_{m ≤ M} 1/m = H_M` in `ℝ`. -/
private lemma sum_inv_Icc_eq_harmonic (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m = ((harmonic M : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  exact Finset.sum_congr rfl (fun m _ => by rw [one_div])

/-- `⌊y⌋₊ ≥ y/2` for `y ≥ 1`. -/
private lemma floor_ge_half {y : ℝ} (hy : 1 ≤ y) : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
  rcases le_or_gt y 2 with h | h
  · have h1 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
      exact_mod_cast Nat.le_floor (by exact_mod_cast hy)
    linarith
  · have := Nat.sub_one_lt_floor y
    linarith

/-- **The `γ`-comparison.**  If `k = ⌊y⌋₊ ≥ 1` then `|H_k − log y − γ| ≤ 1/k`.
Both halves come from Mathlib's `eulerMascheroniSeq k < γ < eulerMascheroniSeq' k`,
i.e. `log k < H_k − γ < log(k+1)`, together with `log(1 + 1/k) ≤ 1/k`. -/
private lemma abs_harmonic_sub_log_sub_gamma_le {k : ℕ} (hk : 1 ≤ k) {y : ℝ}
    (hky : (k : ℝ) ≤ y) (hyk : y < (k : ℝ) + 1) :
    |((harmonic k : ℚ) : ℝ) - Real.log y - Real.eulerMascheroniConstant| ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlo : ((harmonic k : ℚ) : ℝ) - Real.log ((k : ℝ) + 1) < Real.eulerMascheroniConstant := by
    have := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant k
    rwa [Real.eulerMascheroniSeq] at this
  have hhi : Real.eulerMascheroniConstant < ((harmonic k : ℚ) : ℝ) - Real.log (k : ℝ) := by
    have := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' k
    rwa [Real.eulerMascheroniSeq', if_neg (by omega)] at this
  -- `log(k+1) − log k ≤ 1/k`
  have hgap : Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) ≤ 1 / k := by
    have h1 : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤ ((k : ℝ) + 1) / (k : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (ne_of_gt hk0)] at h1
    have h2 : ((k : ℝ) + 1) / (k : ℝ) - 1 = 1 / k := by
      field_simp
      ring
    linarith
  have hlogmono1 : Real.log (k : ℝ) ≤ Real.log y := Real.log_le_log hk0 hky
  have hlogmono2 : Real.log y ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log (by linarith) (le_of_lt hyk)
  rw [abs_le]
  constructor <;> linarith

/-! ### RZA Lemma 3.1 at `σ = 1`, `q = 1` -/

/-- `m̌_1(X, 1) = ∑_{n ≤ X} (μ(n)/n) log(X/n)`. -/
noncomputable def mCheck1 (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((μ n : ℝ) / n) * Real.log (X / n)

/-- **RZA Lemma 3.1 at `σ = 1`, `q = 1`, with constant `11/3`.**
`|∑_{n ≤ X} (μ(n)/n) log(X/n)| ≤ 11/3` for every `X ≥ 1`.
(RZA get `1.00303`, quoting their [7]; the proof here is self-contained.) -/
theorem abs_mCheck1_le {X : ℝ} (hX : 1 ≤ X) : |mCheck1 X| ≤ 11 / 3 := by
  set N := ⌊X⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNX : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hX0 : (0 : ℝ) < X := by linarith
  set γ := Real.eulerMascheroniConstant with hγ
  -- pointwise: `H_{N/n} = log(X/n) + γ + ρ n` with `|ρ n| ≤ 2n/X`
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ((μ n : ℝ) / n) * (∑ m ∈ Finset.Icc 1 (N / n), (1 : ℝ) / m)
        = ((μ n : ℝ) / n) * Real.log (X / n) + ((μ n : ℝ) / n) * γ
          + ((μ n : ℝ) / n) * (((harmonic (N / n) : ℚ) : ℝ) - Real.log (X / n) - γ) := by
    intro n _
    rw [sum_inv_Icc_eq_harmonic]
    ring
  have hrho : ∀ n ∈ Finset.Icc 1 N,
      |((μ n : ℝ) / n) * (((harmonic (N / n) : ℚ) : ℝ) - Real.log (X / n) - γ)|
        ≤ 2 / X := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnN⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hkeq : N / n = ⌊X / n⌋₊ := by rw [Nat.floor_div_natCast X n]
    have hk1 : 1 ≤ N / n := Nat.one_le_div_iff (by omega) |>.mpr hnN
    have hk1' : 1 ≤ ⌊X / n⌋₊ := hkeq ▸ hk1
    have hXn1 : (1 : ℝ) ≤ X / n := by
      have := Nat.floor_le (show (0:ℝ) ≤ X / n by positivity)
      have h1 : (1 : ℝ) ≤ (⌊X / n⌋₊ : ℝ) := by exact_mod_cast hk1'
      linarith
    have hlo : ((⌊X / n⌋₊ : ℕ) : ℝ) ≤ X / n := Nat.floor_le (by positivity)
    have hhi : X / n < ((⌊X / n⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have habs := abs_harmonic_sub_log_sub_gamma_le (k := ⌊X / n⌋₊) hk1' hlo hhi
    rw [← hkeq] at habs
    -- `1/⌊X/n⌋₊ ≤ 2n/X`
    have hhalf : (X / n) / 2 ≤ ((⌊X / n⌋₊ : ℕ) : ℝ) := floor_ge_half hXn1
    have hkpos : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by
      rw [hkeq]; exact_mod_cast hk1'
    have hXle : X ≤ 2 * (n : ℝ) * ((N / n : ℕ) : ℝ) := by
      rw [hkeq]
      have h2 : X / (n : ℝ) ≤ 2 * ((⌊X / (n : ℝ)⌋₊ : ℕ) : ℝ) := by linarith
      calc X = (X / (n : ℝ)) * (n : ℝ) := by field_simp
        _ ≤ (2 * ((⌊X / (n : ℝ)⌋₊ : ℕ) : ℝ)) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right h2 (le_of_lt hn0)
        _ = 2 * (n : ℝ) * ((⌊X / (n : ℝ)⌋₊ : ℕ) : ℝ) := by ring
    have hinv : 1 / ((N / n : ℕ) : ℝ) ≤ 2 * n / X := by
      rw [div_le_div_iff₀ hkpos hX0]
      linarith [hXle]
    have hmu : |(μ n : ℝ) / n| ≤ 1 / n := by
      rw [abs_div, Nat.abs_cast]
      gcongr
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc |((μ n : ℝ) / n) * (((harmonic (N / n) : ℚ) : ℝ) - Real.log (X / n) - γ)|
        = |(μ n : ℝ) / n| * |((harmonic (N / n) : ℚ) : ℝ) - Real.log (X / n) - γ| := abs_mul _ _
      _ ≤ (1 / n) * (1 / ((N / n : ℕ) : ℝ)) := by
          refine mul_le_mul hmu (le_trans habs (le_of_eq rfl)) (abs_nonneg _) (by positivity)
      _ ≤ (1 / n) * (2 * n / X) := by gcongr
      _ = 2 / X := by field_simp
  -- assemble: `1 = m̌₁(X) + γ·m(X) + R`, `|R| ≤ 2`
  have hidB := sum_moebius_div_mul_harmonic_eq_one hN1
  rw [Finset.sum_congr rfl hpt] at hidB
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hidB
  have hmH : ∑ n ∈ Finset.Icc 1 N, ((μ n : ℝ) / n) * γ = γ * mHarm X := by
    rw [mHarm, ← hNdef, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)
  have hm1 : ∑ n ∈ Finset.Icc 1 N, ((μ n : ℝ) / n) * Real.log (X / n) = mCheck1 X := by
    rw [mCheck1, ← hNdef]
  set R := ∑ n ∈ Finset.Icc 1 N,
      ((μ n : ℝ) / n) * (((harmonic (N / n) : ℚ) : ℝ) - Real.log (X / n) - γ) with hRdef
  rw [hmH, hm1] at hidB
  have hRbnd : |R| ≤ 2 := by
    have h1 : |R| ≤ ∑ n ∈ Finset.Icc 1 N, (2 / X) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hrho)
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
    simp only [Nat.add_sub_cancel] at h1
    have h2 : (N : ℝ) * (2 / X) ≤ 2 := by
      rw [mul_div_assoc'] at h1 ⊢
      rw [div_le_iff₀ hX0]
      nlinarith [hNX, hX0]
    linarith
  have hmHb : |mHarm X| ≤ 1 := abs_mHarm_le_one hX
  have hγlo : (0 : ℝ) < γ := by
    have := Real.one_half_lt_eulerMascheroniConstant
    rw [← hγ] at this; linarith
  have hγhi : γ < 2 / 3 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds
    rw [← hγ] at this; exact this
  have hmC : mCheck1 X = 1 - γ * mHarm X - R := by linarith [hidB]
  rw [hmC]
  have hgm : |γ * mHarm X| ≤ 2 / 3 := by
    rw [abs_mul, abs_of_pos hγlo]
    nlinarith [abs_nonneg (mHarm X), hmHb, hγlo, hγhi]
  calc |1 - γ * mHarm X - R| ≤ |1 - γ * mHarm X| + |R| := abs_sub _ _
    _ ≤ (|(1 : ℝ)| + |γ * mHarm X|) + |R| := by
        have := abs_sub (1 : ℝ) (γ * mHarm X); linarith
    _ ≤ (1 + 2 / 3) + 2 := by rw [abs_one]; linarith
    _ = 11 / 3 := by norm_num

/-! ### The `σ`-extension of Lemma 3.1

Write `ε = σ − 1 ≥ 0`, `L = log Y`, `s_n = log(Y/n)`.  Then
`μ(n) n^{-σ} log(Y/n) = e^{-εL} (μ(n)/n) φ(s_n)` with `φ(s) = s e^{εs}`, and
Taylor with integral remainder gives
`φ(s) = s + ∫_0^L φ''(w) (s − w)_+ dw` for `0 ≤ s ≤ L`.
Summing against `μ(n)/n` turns the remainder into `∫_0^L φ''(w) m̌₁(Y e^{-w}) dw`,
which `abs_mCheck1_le` bounds by `(11/3)(φ'(L) − 1)`.  Hence
`|m̌₁(Y, σ)| ≤ e^{-εL} (11/3) φ'(L) = (11/3)(1 + εL)`. -/

section SigmaExtension

/-- `φ(s) = s·e^{εs}`. -/
private noncomputable def phi (ε s : ℝ) : ℝ := s * Real.exp (ε * s)
/-- `φ'(s) = e^{εs}(1 + εs)`. -/
private noncomputable def phi1 (ε s : ℝ) : ℝ := Real.exp (ε * s) * (1 + ε * s)
/-- `φ''(s) = ε·e^{εs}(2 + εs)`. -/
private noncomputable def phi2 (ε s : ℝ) : ℝ := ε * Real.exp (ε * s) * (2 + ε * s)

private lemma hasDerivAt_phi (ε s : ℝ) : HasDerivAt (phi ε) (phi1 ε s) s := by
  have h1 : HasDerivAt (fun x : ℝ => ε * x) ε s := by
    simpa using (hasDerivAt_id s).const_mul ε
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (ε * x)) (Real.exp (ε * s) * ε) s :=
    (Real.hasDerivAt_exp (ε * s)).comp s h1
  have h3 := (hasDerivAt_id s).mul h2
  simp only [id_eq, one_mul] at h3
  have heq : Real.exp (ε * s) + s * (Real.exp (ε * s) * ε)
      = Real.exp (ε * s) * (1 + ε * s) := by ring
  rw [heq] at h3
  exact h3

private lemma hasDerivAt_phi1 (ε s : ℝ) : HasDerivAt (phi1 ε) (phi2 ε s) s := by
  have h1 : HasDerivAt (fun x : ℝ => ε * x) ε s := by
    simpa using (hasDerivAt_id s).const_mul ε
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (ε * x)) (Real.exp (ε * s) * ε) s :=
    (Real.hasDerivAt_exp (ε * s)).comp s h1
  have h3 : HasDerivAt (fun x : ℝ => 1 + ε * x) ε s := by
    simpa using h1.const_add (1 : ℝ)
  have h4 := h2.mul h3
  have heq : Real.exp (ε * s) * ε * (1 + ε * s) + Real.exp (ε * s) * ε
      = ε * Real.exp (ε * s) * (2 + ε * s) := by ring
  rw [heq] at h4
  exact h4

private lemma continuous_phi2 (ε : ℝ) : Continuous (phi2 ε) := by
  unfold phi2
  fun_prop

/-- Taylor with integral remainder: `∫_0^s φ''(w)(s − w) dw = φ(s) − s`. -/
private lemma integral_phi2_mul_sub (ε s : ℝ) :
    (∫ w in (0 : ℝ)..s, phi2 ε w * (s - w)) = phi ε s - s := by
  have hF : ∀ w ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt (fun x => phi1 ε x * (s - x) + phi ε x) (phi2 ε w * (s - w)) w := by
    intro w _
    have hd1 : HasDerivAt (fun x : ℝ => s - x) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub s
    have h := ((hasDerivAt_phi1 ε w).mul hd1).add (hasDerivAt_phi ε w)
    have heq : phi2 ε w * (s - w) + phi1 ε w * (-1) + phi1 ε w = phi2 ε w * (s - w) := by ring
    rw [heq] at h
    exact h
  have hint : IntervalIntegrable (fun w => phi2 ε w * (s - w)) MeasureTheory.volume 0 s := by
    apply Continuous.intervalIntegrable
    exact (continuous_phi2 ε).mul (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  simp [phi, phi1]

/-- The same with the positive part, over the full window `[0, L]`. -/
private lemma integral_phi2_mul_max {ε s L : ℝ} (hs : 0 ≤ s) (hsL : s ≤ L) :
    (∫ w in (0 : ℝ)..L, phi2 ε w * max (s - w) 0) = phi ε s - s := by
  have hcont : Continuous (fun w : ℝ => phi2 ε w * max (s - w) 0) :=
    (continuous_phi2 ε).mul (by fun_prop)
  have hsplit : (∫ w in (0 : ℝ)..L, phi2 ε w * max (s - w) 0)
      = (∫ w in (0 : ℝ)..s, phi2 ε w * max (s - w) 0)
        + (∫ w in s..L, phi2 ε w * max (s - w) 0) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have h1 : (∫ w in (0 : ℝ)..s, phi2 ε w * max (s - w) 0)
      = ∫ w in (0 : ℝ)..s, phi2 ε w * (s - w) := by
    refine intervalIntegral.integral_congr ?_
    intro w hw
    rw [Set.uIcc_of_le hs, Set.mem_Icc] at hw
    show phi2 ε w * max (s - w) 0 = phi2 ε w * (s - w)
    rw [max_eq_left (by linarith [hw.2])]
  have h2 : (∫ w in s..L, phi2 ε w * max (s - w) 0) = 0 := by
    have : (∫ w in s..L, phi2 ε w * max (s - w) 0) = ∫ _w in s..L, (0 : ℝ) := by
      refine intervalIntegral.integral_congr ?_
      intro w hw
      rw [Set.uIcc_of_le hsL, Set.mem_Icc] at hw
      show phi2 ε w * max (s - w) 0 = 0
      rw [max_eq_right (by linarith [hw.1]), mul_zero]
    rw [this, intervalIntegral.integral_zero]
  rw [hsplit, h1, h2, add_zero, integral_phi2_mul_sub]

end SigmaExtension

section SigmaMain

/-- `Q(w) = ∑_{n ≤ Y} (μ(n)/n)·(log(Y/n) − w)₊`; it equals `m̌₁(Y e^{-w})`. -/
private noncomputable def Qfun (Y w : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ((μ n : ℝ) / n) * max (Real.log (Y / n) - w) 0

private lemma continuous_Qfun (Y : ℝ) : Continuous (Qfun Y) := by
  unfold Qfun
  exact continuous_finsetSum _ (fun n _ => by fun_prop)

/-- `Q(w) = m̌₁(Y e^{-w})` for `0 ≤ w ≤ log Y`. -/
private lemma Qfun_eq_mCheck1 {Y w : ℝ} (hY : 1 ≤ Y) (hw : 0 ≤ w)
    (hwL : w ≤ Real.log Y) : Qfun Y w = mCheck1 (Y * Real.exp (-w)) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  set Y' := Y * Real.exp (-w) with hY'def
  have hY'0 : (0 : ℝ) < Y' := by positivity
  have hlogY' : Real.log Y' = Real.log Y - w := by
    rw [hY'def, Real.log_mul (ne_of_gt hY0) (Real.exp_ne_zero _), Real.log_exp]; ring
  have hY'1 : (1 : ℝ) ≤ Y' := by
    have : 0 ≤ Real.log Y' := by rw [hlogY']; linarith
    exact (Real.le_log_iff_exp_le hY'0).mp (by simpa using this) |>.trans_eq' (by simp)
  have hY'Y : Y' ≤ Y := by
    rw [hY'def]
    nlinarith [Real.exp_le_one_iff.mpr (show -w ≤ 0 by linarith), hY0]
  have hsub : Finset.Icc 1 ⌊Y'⌋₊ ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
    apply Finset.Icc_subset_Icc_right
    exact Nat.floor_le_floor hY'Y
  rw [mCheck1, Qfun]
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    simp only [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnY'⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnle : (n : ℝ) ≤ Y' := le_trans (by exact_mod_cast hnY') (Nat.floor_le hY'0.le)
    have hlogeq : Real.log (Y / n) - w = Real.log (Y' / n) := by
      rw [Real.log_div (ne_of_gt hY0) (ne_of_gt hn0), Real.log_div (ne_of_gt hY'0) (ne_of_gt hn0),
        hlogY']
      ring
    rw [hlogeq, max_eq_left]
    exact Real.log_nonneg ((one_le_div hn0).mpr hnle)
  · intro n hn hn'
    simp only [Finset.mem_Icc] at hn hn'
    have hn1 : 1 ≤ n := hn.1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hgt : Y' < (n : ℝ) := by
      by_contra hcon
      push Not at hcon
      exact hn' ⟨hn1, Nat.le_floor (by exact_mod_cast hcon)⟩
    have hlogeq : Real.log (Y / n) - w = Real.log (Y' / n) := by
      rw [Real.log_div (ne_of_gt hY0) (ne_of_gt hn0), Real.log_div (ne_of_gt hY'0) (ne_of_gt hn0),
        hlogY']
      ring
    rw [hlogeq, max_eq_right, mul_zero]
    exact le_of_lt (Real.log_neg (by positivity) ((div_lt_one hn0).mpr hgt))

/-- **RZA Lemma 3.1 at `q = 1`, general `σ ≥ 1`, with constant `11/3`.**
`|∑_{n ≤ Y} μ(n) n^{-σ} log(Y/n)| ≤ (11/3)(1 + (σ−1) log Y)` for `Y ≥ 1`. -/
theorem abs_mCheck_sigma_le {Y σ : ℝ} (hY : 1 ≤ Y) (hσ : 1 ≤ σ) :
    |∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (μ n : ℝ) * (n : ℝ) ^ (-σ) * Real.log (Y / n)|
      ≤ (11 / 3) * (1 + (σ - 1) * Real.log Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  set ε := σ - 1 with hεdef
  have hε0 : 0 ≤ ε := by simp only [hεdef]; linarith
  set L := Real.log Y with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hY
  set N := ⌊Y⌋₊ with hNdef
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le hY0.le
  -- range facts
  have hs : ∀ n ∈ Finset.Icc 1 N, 0 ≤ Real.log (Y / n) ∧ Real.log (Y / n) ≤ L := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    obtain ⟨hn1, hnN⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnY : (n : ℝ) ≤ Y := le_trans (by exact_mod_cast hnN) hNY
    constructor
    · exact Real.log_nonneg ((one_le_div hn0).mpr hnY)
    · rw [hLdef]
      exact Real.log_le_log (by positivity) (by
        rw [div_le_iff₀ hn0]; nlinarith [hY0, hn1'])
  -- the integral identity
  have hswap : (∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w)
      = ∑ n ∈ Finset.Icc 1 N, ((μ n : ℝ) / n) * (phi ε (Real.log (Y / n)) - Real.log (Y / n)) := by
    have hrw : ∀ w : ℝ, phi2 ε w * Qfun Y w
        = ∑ n ∈ Finset.Icc 1 N, ((μ n : ℝ) / n) * (phi2 ε w * max (Real.log (Y / n) - w) 0) := by
      intro w
      rw [Qfun, ← hNdef, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    simp only [hrw]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [intervalIntegral.integral_const_mul, integral_phi2_mul_max (hs n hn).1 (hs n hn).2]
    · intro n _
      apply Continuous.intervalIntegrable
      exact continuous_const.mul ((continuous_phi2 ε).mul (by fun_prop))
  -- bound the integral
  have hQbnd : ∀ w ∈ Set.Icc (0 : ℝ) L, |Qfun Y w| ≤ 11 / 3 := by
    intro w hw
    rw [Set.mem_Icc] at hw
    rw [Qfun_eq_mCheck1 hY hw.1 (by rw [← hLdef]; exact hw.2)]
    refine abs_mCheck1_le ?_
    have : 0 ≤ Real.log (Y * Real.exp (-w)) := by
      rw [Real.log_mul (ne_of_gt hY0) (Real.exp_ne_zero _), Real.log_exp, ← hLdef]
      linarith [hw.2]
    have hpos : (0 : ℝ) < Y * Real.exp (-w) := by positivity
    nlinarith [Real.add_one_le_exp (Real.log (Y * Real.exp (-w))), Real.exp_log hpos]
  have hphi2nn : ∀ w : ℝ, 0 ≤ w → 0 ≤ phi2 ε w := by
    intro w hw
    unfold phi2
    have : 0 ≤ 2 + ε * w := by nlinarith
    positivity
  have hintbnd : |∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w| ≤ (11 / 3) * (phi1 ε L - 1) := by
    have hc1 : Continuous (fun w => phi2 ε w * Qfun Y w) :=
      (continuous_phi2 ε).mul (continuous_Qfun Y)
    have h1 : |∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w|
        ≤ ∫ w in (0 : ℝ)..L, |phi2 ε w * Qfun Y w| :=
      intervalIntegral.abs_integral_le_integral_abs hL0
    have h2 : (∫ w in (0 : ℝ)..L, |phi2 ε w * Qfun Y w|)
        ≤ ∫ w in (0 : ℝ)..L, (11 / 3) * phi2 ε w := by
      refine intervalIntegral.integral_mono_on hL0 (hc1.abs.intervalIntegrable _ _)
        (((continuous_phi2 ε).const_mul _).intervalIntegrable _ _) ?_
      intro w hw
      rw [abs_mul, abs_of_nonneg (hphi2nn w (Set.mem_Icc.mp hw).1)]
      have := hQbnd w hw
      nlinarith [hphi2nn w (Set.mem_Icc.mp hw).1, abs_nonneg (Qfun Y w)]
    have h3 : (∫ w in (0 : ℝ)..L, (11 / 3 : ℝ) * phi2 ε w) = (11 / 3) * (phi1 ε L - 1) := by
      rw [intervalIntegral.integral_const_mul]
      have hd : ∀ w ∈ Set.uIcc (0 : ℝ) L, HasDerivAt (phi1 ε) (phi2 ε w) w :=
        fun w _ => hasDerivAt_phi1 ε w
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_phi2 ε).intervalIntegrable _ _)]
      have : phi1 ε 0 = 1 := by unfold phi1; simp
      rw [this]
    linarith [h1, h2, h3.le, h3.ge]
  -- reassemble
  have hmain : ∑ n ∈ Finset.Icc 1 N, ((μ n : ℝ) / n) * phi ε (Real.log (Y / n))
      = mCheck1 Y + ∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w := by
    rw [hswap, mCheck1, ← hNdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  -- transfer to `n^{-σ}`
  have hterm : ∀ n ∈ Finset.Icc 1 N, (μ n : ℝ) * (n : ℝ) ^ (-σ) * Real.log (Y / n)
      = Real.exp (-(ε * L)) * (((μ n : ℝ) / n) * phi ε (Real.log (Y / n))) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hlogn : Real.log (Y / n) = L - Real.log n := by
      rw [Real.log_div (ne_of_gt hY0) (ne_of_gt hn0), hLdef]
    have hrpow : (n : ℝ) ^ (-σ) = Real.exp (-σ * Real.log n) := by
      rw [Real.rpow_def_of_pos hn0]; ring_nf
    have hninv : (1 : ℝ) / n = Real.exp (-Real.log n) := by
      rw [Real.exp_neg, Real.exp_log hn0]
      ring
    have hexp : Real.exp (-(ε * L)) * (Real.exp (-Real.log n) * Real.exp (ε * (L - Real.log n)))
        = Real.exp (-σ * Real.log n) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [hεdef]; ring
    rw [hrpow, phi, hlogn]
    rw [show ((μ n : ℝ) / n) = (μ n : ℝ) * (1 / n) by ring, hninv]
    linear_combination (-((μ n : ℝ) * (L - Real.log n))) * hexp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hmain, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have hmC1 := abs_mCheck1_le hY
  have hkey : |mCheck1 Y + ∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w| ≤ (11 / 3) * phi1 ε L := by
    calc |mCheck1 Y + ∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w|
        ≤ |mCheck1 Y| + |∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w| := abs_add_le _ _
      _ ≤ 11 / 3 + (11 / 3) * (phi1 ε L - 1) := by linarith [hmC1, hintbnd]
      _ = (11 / 3) * phi1 ε L := by ring
  have hexpphi : Real.exp (-(ε * L)) * ((11 / 3) * phi1 ε L)
      = (11 / 3) * (1 + ε * L) := by
    unfold phi1
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  calc Real.exp (-(ε * L)) * |mCheck1 Y + ∫ w in (0 : ℝ)..L, phi2 ε w * Qfun Y w|
      ≤ Real.exp (-(ε * L)) * ((11 / 3) * phi1 ε L) :=
        mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
    _ = (11 / 3) * (1 + ε * L) := hexpphi

end SigmaMain


/-! ### RZA Lemma 3.1 for general squarefree `q` -/

/-- `m̌_q(X, σ) = ∑_{n ≤ X, (n,q)=1} μ(n) n^{-σ} log(X/n)`. -/
noncomputable def mCheckQ (q : ℕ) (X σ : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
    (if Nat.Coprime n q then (μ n : ℝ) * (n : ℝ) ^ (-σ) * Real.log (X / n) else 0)

lemma mCheckQ_one (X σ : ℝ) :
    mCheckQ 1 X σ = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (μ n : ℝ) * (n : ℝ) ^ (-σ) * Real.log (X / n) := by
  simp [mCheckQ]

lemma mCheckQ_of_lt_one {X : ℝ} (hX : X < 1) (q : ℕ) (σ : ℝ) : mCheckQ q X σ = 0 := by
  have h : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr hX
  simp [mCheckQ, h]

/-- **The `q`-recursion.**  For a prime `p ∣ q` with `q` squarefree,
`m̌_{q/p}(X, σ) = m̌_q(X, σ) − p^{-σ} m̌_q(X/p, σ)`. -/
lemma mCheckQ_rec {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q) (X σ : ℝ) :
    mCheckQ (q / p) X σ = mCheckQ q X σ - (p : ℝ) ^ (-σ) * mCheckQ q (X / p) σ := by
  have hp0 : 0 < p := hp.pos
  have hp1 : 1 < p := hp.one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  obtain ⟨q', rfl⟩ := hpq
  have hdiv : p * q' / p = q' := Nat.mul_div_cancel_left q' hp0
  rw [hdiv]
  set N := ⌊X⌋₊ with hN
  set f : ℕ → ℝ := fun n => (μ n : ℝ) * (n : ℝ) ^ (-σ) * Real.log (X / n) with hf
  have hnpq' : ¬ p ∣ q' := by
    rintro ⟨t, rfl⟩
    have := Nat.isUnit_iff.mp (hq p ⟨t, by ring⟩)
    omega
  have hcop : Nat.Coprime p q' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnpq'
  -- pointwise split of the `q'`-indicator
  have hsplit : ∀ n : ℕ, (if Nat.Coprime n q' then f n else 0)
      = (if Nat.Coprime n (p * q') then f n else 0)
        + (if p ∣ n then (if Nat.Coprime n q' then f n else 0) else 0) := by
    intro n
    by_cases hpn : p ∣ n
    · have hnc : ¬ Nat.Coprime n (p * q') := by
        intro hc
        have h1 : Nat.Coprime n p := Nat.Coprime.coprime_dvd_right (Dvd.intro q' rfl) hc
        exact absurd (Nat.Coprime.eq_one_of_dvd h1.symm hpn) (by omega)
      simp [hnc, hpn]
    · have hiff : Nat.Coprime n (p * q') ↔ Nat.Coprime n q' := by
        constructor
        · exact fun hc => Nat.Coprime.coprime_dvd_right (Dvd.intro_left p rfl) hc
        · intro hc
          exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm hc
      simp [hpn, hiff]
  have hmain : mCheckQ q' X σ
      = mCheckQ (p * q') X σ
        + ∑ n ∈ Finset.Icc 1 N, (if p ∣ n then (if Nat.Coprime n q' then f n else 0) else 0) := by
    rw [mCheckQ, mCheckQ, ← hN, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => hsplit n)
  rw [hmain]
  -- the `p ∣ n` part is `−p^{-σ} m̌_q(X/p)`
  have hfloor : ⌊X / (p : ℝ)⌋₊ = N / p := by rw [hN, Nat.floor_div_natCast X p]
  have hreindex : ∑ n ∈ Finset.Icc 1 N, (if p ∣ n then (if Nat.Coprime n q' then f n else 0) else 0)
      = ∑ m ∈ Finset.Icc 1 (N / p), (if Nat.Coprime (p * m) q' then f (p * m) else 0) := by
    rw [← Finset.sum_filter]
    refine (Finset.sum_nbij' (i := fun m => p * m) (j := fun n => n / p) ?_ ?_ ?_ ?_ ?_).symm
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, Dvd.intro m rfl⟩
      · nlinarith [hm.1, hp0]
      · exact (Nat.le_div_iff_mul_le hp0).mp hm.2 |>.trans_eq' (by ring)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpn⟩ := hn
      simp only [Finset.mem_Icc]
      exact ⟨Nat.one_le_div_iff hp0 |>.mpr (Nat.le_of_dvd (by omega) hpn),
        Nat.div_le_div_right hnN⟩
    · intro m _
      exact Nat.mul_div_cancel_left m hp0
    · intro n hn
      simp only [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      rfl
  rw [hreindex]
  have hterm : ∀ m ∈ Finset.Icc 1 (N / p), (if Nat.Coprime (p * m) q' then f (p * m) else 0)
      = (-((p : ℝ) ^ (-σ))) *
          (if Nat.Coprime m (p * q') then
            (μ m : ℝ) * (m : ℝ) ^ (-σ) * Real.log (X / (p : ℝ) / m) else 0) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    have hm0 : 0 < m := hm.1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    by_cases hpm : p ∣ m
    · -- `μ(pm) = 0` and `(m, pq') ≠ 1`
      obtain ⟨t, rfl⟩ := hpm
      have hnsq : ¬ Squarefree (p * (p * t)) := by
        intro hs
        have := Nat.isUnit_iff.mp (hs p ⟨t, by ring⟩)
        omega
      have hmu : (μ (p * (p * t)) : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]; norm_num
      have hnc : ¬ Nat.Coprime (p * t) (p * q') := by
        intro hc
        have h1 : Nat.Coprime (p * t) p := Nat.Coprime.coprime_dvd_right (Dvd.intro q' rfl) hc
        exact absurd (Nat.Coprime.eq_one_of_dvd h1.symm (Dvd.intro t rfl)) (by omega)
      rw [if_neg hnc]
      by_cases hc2 : Nat.Coprime (p * (p * t)) q'
      · rw [if_pos hc2]
        simp only [hf]
        rw [hmu]; ring
      · rw [if_neg hc2]; ring
    · have hcpm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
      have hiff : Nat.Coprime (p * m) q' ↔ Nat.Coprime m (p * q') := by
        constructor
        · intro hc
          exact Nat.Coprime.mul_right hcpm.symm (Nat.Coprime.coprime_dvd_left
            (Dvd.intro_left p rfl) hc)
        · intro hc
          exact Nat.Coprime.mul_left hcop (Nat.Coprime.coprime_dvd_right
            (Dvd.intro_left p rfl) hc)
      have hmu : (μ (p * m) : ℝ) = -(μ m : ℝ) := by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcpm,
          ArithmeticFunction.moebius_apply_prime hp]
        push_cast; ring
      have hpow : ((p * m : ℕ) : ℝ) ^ (-σ) = (p : ℝ) ^ (-σ) * (m : ℝ) ^ (-σ) := by
        push_cast
        rw [Real.mul_rpow hpR.le hmR.le]
      have hlog : Real.log (X / ((p * m : ℕ) : ℝ)) = Real.log (X / (p : ℝ) / m) := by
        push_cast
        rw [div_div]
      by_cases hc : Nat.Coprime (p * m) q'
      · have hc2 : Nat.Coprime m (p * q') := hiff.mp hc
        rw [if_pos hc, if_pos hc2]
        simp only [hf]
        rw [hmu, hpow, hlog]
        ring
      · have hc2 : ¬ Nat.Coprime m (p * q') := fun h => hc (hiff.mpr h)
        rw [if_neg hc, if_neg hc2]
        ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hms : mCheckQ (p * q') (X / (p : ℝ)) σ
      = ∑ m ∈ Finset.Icc 1 (N / p), (if Nat.Coprime m (p * q') then
          (μ m : ℝ) * (m : ℝ) ^ (-σ) * Real.log (X / (p : ℝ) / m) else 0) := by
    rw [mCheckQ, hfloor]
  rw [← hms]
  ring

/-- `q/φ(q) ≥ 1` for `q ≥ 1`. -/
private lemma one_le_q_div_totient {q : ℕ} (hq : q ≠ 0) :
    (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := by
  have h1 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  have h2 : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast h1
  rw [le_div_iff₀ h2, one_mul]
  exact_mod_cast Nat.totient_le q

/-- The two-variable induction behind RZA Lemma 3.1 for squarefree `q`. -/
private lemma abs_mCheckQ_aux {σ : ℝ} (hσ : 1 ≤ σ) :
    ∀ (q : ℕ), Squarefree q → ∀ (N : ℕ) (X : ℝ), ⌊X⌋₊ ≤ N → 1 ≤ X →
      |mCheckQ q X σ| ≤ ((q : ℝ) / (q.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log X) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq N
    induction N using Nat.strong_induction_on with
    | _ N ihN =>
      intro X hXN hX1
      have hq0 : q ≠ 0 := hq.ne_zero
      have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
      have hbase : (0 : ℝ) ≤ 1 + (σ - 1) * Real.log X := by nlinarith
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hq0) with hq1 | hq1
      · -- `q = 1`
        rw [← hq1]
        simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul]
        rw [mCheckQ_one]
        exact abs_mCheck_sigma_le hX1 hσ
      · -- `q > 1`: peel off the least prime factor
        set p := q.minFac with hp
        have hpp : p.Prime := Nat.minFac_prime (by omega)
        have hpq : p ∣ q := Nat.minFac_dvd q
        have hp1 : 1 < p := hpp.one_lt
        have hp0 : 0 < p := hpp.pos
        have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
        set q' := q / p with hq'
        have hqq' : q = p * q' := (Nat.mul_div_cancel' hpq).symm
        have hq'lt : q' < q := Nat.div_lt_self (by omega) hp1
        have hq'sf : Squarefree q' := hq.squarefree_of_dvd (Nat.div_dvd_of_dvd hpq)
        have hq'0 : q' ≠ 0 := hq'sf.ne_zero
        have hcop : Nat.Coprime p q' := by
          rw [Nat.Prime.coprime_iff_not_dvd hpp]
          intro hdvd
          obtain ⟨t, ht⟩ := hdvd
          have : p * p ∣ q := by rw [hqq', ht]; exact ⟨t, by ring⟩
          obtain ⟨u, hu⟩ := this
          have := Nat.isUnit_iff.mp (hq p ⟨u, by rw [hu]⟩)
          omega
        -- totient bookkeeping
        have htot0 : 0 < q'.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq'0)
        have htot0R : (0 : ℝ) < (q'.totient : ℝ) := by exact_mod_cast htot0
        have htotq : (q.totient : ℝ) = ((p : ℝ) - 1) * (q'.totient : ℝ) := by
          rw [hqq', Nat.totient_mul hcop, Nat.totient_prime hpp]
          push_cast [Nat.cast_sub hp0]
          ring
        have hqR : (q : ℝ) = (p : ℝ) * (q' : ℝ) := by rw [hqq']; push_cast; ring
        have hratio : (q : ℝ) / (q.totient : ℝ)
            = ((p : ℝ) / ((p : ℝ) - 1)) * ((q' : ℝ) / (q'.totient : ℝ)) := by
          rw [htotq, hqR]
          field_simp
        -- the recursion
        have hrec : mCheckQ q X σ
            = mCheckQ q' X σ + (p : ℝ) ^ (-σ) * mCheckQ q (X / p) σ := by
          have := mCheckQ_rec hq hpp hpq X σ
          rw [← hq'] at this
          linarith [this]
        -- term 1
        have hb1 : |mCheckQ q' X σ|
            ≤ ((q' : ℝ) / (q'.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log X) :=
          ih q' hq'lt hq'sf N X hXN hX1
        -- term 2
        have hb2 : |mCheckQ q (X / p) σ|
            ≤ ((q : ℝ) / (q.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log X) := by
          rcases lt_or_ge (X / (p : ℝ)) 1 with hlt | hge
          · rw [mCheckQ_of_lt_one hlt, abs_zero]
            have h1 : (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := one_le_q_div_totient hq0
            nlinarith
          · have hfl : ⌊X / (p : ℝ)⌋₊ < N := by
              have h1 : ⌊X / (p : ℝ)⌋₊ = ⌊X⌋₊ / p := Nat.floor_div_natCast X p
              have h2 : 0 < ⌊X⌋₊ := Nat.floor_pos.mpr hX1
              have h3 : ⌊X⌋₊ / p < ⌊X⌋₊ := Nat.div_lt_self h2 hp1
              omega
            have hstep := ihN ⌊X / (p : ℝ)⌋₊ hfl (X / (p : ℝ)) (le_refl _) hge
            refine le_trans hstep ?_
            have hlogle : Real.log (X / (p : ℝ)) ≤ Real.log X :=
              Real.log_le_log (by linarith) (by
                rw [div_le_iff₀ (by linarith : (0:ℝ) < (p:ℝ))]
                nlinarith [hX1, hpR])
            have hqpos : (0 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := le_trans zero_le_one
              (one_le_q_div_totient hq0)
            have : (1 : ℝ) + (σ - 1) * Real.log (X / (p : ℝ)) ≤ 1 + (σ - 1) * Real.log X := by
              nlinarith
            nlinarith
        -- combine
        have hppow : (p : ℝ) ^ (-σ) ≤ 1 / (p : ℝ) := by
          have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hpR.le (by linarith)
          rw [Real.rpow_neg_one] at h1
          rwa [one_div]
        have hppos : (0 : ℝ) < (p : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by linarith) _
        have habs2 : |(p : ℝ) ^ (-σ) * mCheckQ q (X / p) σ|
            ≤ (1 / (p : ℝ)) * (((q : ℝ) / (q.totient : ℝ)) * (11 / 3)
              * (1 + (σ - 1) * Real.log X)) := by
          rw [abs_mul, abs_of_pos hppos]
          have hnn : (0 : ℝ) ≤ ((q : ℝ) / (q.totient : ℝ)) * (11 / 3)
              * (1 + (σ - 1) * Real.log X) := by
            have := one_le_q_div_totient hq0
            nlinarith
          calc (p : ℝ) ^ (-σ) * |mCheckQ q (X / p) σ|
              ≤ (p : ℝ) ^ (-σ) * (((q : ℝ) / (q.totient : ℝ)) * (11 / 3)
                  * (1 + (σ - 1) * Real.log X)) := by
                exact mul_le_mul_of_nonneg_left hb2 hppos.le
            _ ≤ (1 / (p : ℝ)) * (((q : ℝ) / (q.totient : ℝ)) * (11 / 3)
                  * (1 + (σ - 1) * Real.log X)) := by
                exact mul_le_mul_of_nonneg_right hppow hnn
        have hkey : |mCheckQ q X σ| ≤ ((q' : ℝ) / (q'.totient : ℝ)) * (11 / 3)
            * (1 + (σ - 1) * Real.log X)
            + (1 / (p : ℝ)) * (((q : ℝ) / (q.totient : ℝ)) * (11 / 3)
              * (1 + (σ - 1) * Real.log X)) := by
          rw [hrec]
          exact le_trans (abs_add_le _ _) (add_le_add hb1 habs2)
        refine le_trans hkey (le_of_eq ?_)
        have hpne : ((p : ℝ) - 1) ≠ 0 := by linarith
        have hppos' : (0 : ℝ) < (p : ℝ) := by linarith
        rw [hratio]
        field_simp
        ring

/-- **RZA Lemma 3.1, squarefree `q`, constant `11/3`.**
`|m̌_q(X, σ)| ≤ (q/φ(q))(11/3)(1 + (σ−1) log X)` for `X ≥ 1`, `σ ≥ 1`. -/
theorem abs_mCheckQ_le {q : ℕ} (hq : Squarefree q) {X σ : ℝ} (hX : 1 ≤ X) (hσ : 1 ≤ σ) :
    |mCheckQ q X σ| ≤ ((q : ℝ) / (q.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log X) :=
  abs_mCheckQ_aux hσ q hq ⌊X⌋₊ X (le_refl _) hX


/-! ### Squarefree divisor expansions -/

/-- For squarefree `n`, `∑_{a ∣ n} ∏_{p ∣ a} f(p) = ∏_{p ∣ n} (1 + f(p))`. -/
lemma sum_divisors_prod_primeFactors {n : ℕ} (hn : Squarefree n) (f : ℕ → ℝ) :
    ∑ a ∈ n.divisors, ∏ p ∈ a.primeFactors, f p = ∏ p ∈ n.primeFactors, (1 + f p) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hprod : ∏ p ∈ n.primeFactors, (1 + f p)
      = ∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t, f p := by
    have h := Finset.prod_add (fun p => f p) (fun _ => (1 : ℝ)) n.primeFactors
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl (fun p _ => by ring)
  rw [hprod]
  refine Finset.sum_nbij' (i := fun a => a.primeFactors) (j := fun t => ∏ p ∈ t, p) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Nat.mem_divisors] at ha
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono ha.1 hn0)
  · intro t ht
    rw [Finset.mem_powerset] at ht
    rw [Nat.mem_divisors]
    refine ⟨?_, hn0⟩
    calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ ht
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  · intro a ha
    rw [Nat.mem_divisors] at ha
    exact Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd ha.1)
  · intro t ht
    rw [Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (ht hp))
  · intro a _
    rfl

/-! ### The `σ`-totient `φ_σ` -/

/-- `φ_σ(q) = ∏_{p ∣ q} (p^σ − 1)`; on squarefree `q` this is RZA's `ϕ_σ`. -/
noncomputable def phiSig (σ : ℝ) (q : ℕ) : ℝ := ∏ p ∈ q.primeFactors, ((p : ℝ) ^ σ - 1)

lemma phiSig_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (q : ℕ) : 0 ≤ phiSig σ q := by
  refine Finset.prod_nonneg (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp2
  have : (1 : ℝ) ≤ (p : ℝ) ^ σ := Real.one_le_rpow hpR hσ
  linarith

/-- `φ_σ(q) ≤ q^σ`. -/
lemma phiSig_le_rpow {σ : ℝ} (hσ : 0 ≤ σ) {q : ℕ} (hq : q ≠ 0) :
    phiSig σ q ≤ (q : ℝ) ^ σ := by
  have hrad : ∏ p ∈ q.primeFactors, (p : ℝ) ≤ (q : ℝ) := by
    have h1 : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
    have h2 : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) h1
    calc ∏ p ∈ q.primeFactors, (p : ℝ) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (q : ℝ) := by exact_mod_cast h2
  calc phiSig σ q ≤ ∏ p ∈ q.primeFactors, ((p : ℝ) ^ σ) := by
        refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => by linarith)
        · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
          have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.one_le_of_lt hp2
          have : (1 : ℝ) ≤ (p : ℝ) ^ σ := Real.one_le_rpow hpR hσ
          linarith
    _ = (∏ p ∈ q.primeFactors, (p : ℝ)) ^ σ := by
        refine Real.finsetProd_rpow _ _ (fun p _ => ?_) σ
        exact Nat.cast_nonneg p
    _ ≤ (q : ℝ) ^ σ := by
        refine Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) hrad hσ

/-- **Identity (9).**  For squarefree `n`, `∑_{δ ∣ n} φ_σ(δ) = n^σ`. -/
lemma sum_divisors_phiSig {σ : ℝ} {n : ℕ} (hn : Squarefree n) :
    ∑ δ ∈ n.divisors, phiSig σ δ = (n : ℝ) ^ σ := by
  have h := sum_divisors_prod_primeFactors hn (fun p => (p : ℝ) ^ σ - 1)
  simp only [phiSig]
  rw [h]
  have h1 : ∏ p ∈ n.primeFactors, (1 + ((p : ℝ) ^ σ - 1))
      = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ σ) := by
    exact Finset.prod_congr rfl (fun p _ => by ring)
  rw [h1, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) σ]
  congr 1
  calc ∏ p ∈ n.primeFactors, (p : ℝ) = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
    _ = (n : ℝ) := by rw [Nat.prod_primeFactors_of_squarefree hn]

/-! ### Sums of multiplicative functions over squarefree integers -/

/-- Products over reals grow under enlarging the index set when every factor is `≥ 1`. -/
private lemma prod_le_prod_subset_one_le {s t : Finset ℕ} (h : s ⊆ t) (f : ℕ → ℝ)
    (hf : ∀ n, 1 ≤ f n) : ∏ n ∈ s, f n ≤ ∏ n ∈ t, f n := by
  rw [← Finset.prod_sdiff h]
  have h1 : (1 : ℝ) ≤ ∏ n ∈ t \ s, f n := by
    have := Finset.prod_le_prod (s := t \ s) (f := fun _ => (1 : ℝ)) (g := f)
      (fun i _ => zero_le_one) (fun i _ => hf i)
    simpa using this
  have h2 : (0 : ℝ) ≤ ∏ n ∈ s, f n :=
    Finset.prod_nonneg (fun i _ => le_trans zero_le_one (hf i))
  nlinarith



/-- **Squarefree sum ≤ Euler product.**  For `w ≥ 0`,
`∑_{a ≤ M} μ²(a) ∏_{p ∣ a} w(p) ≤ ∏_{2 ≤ n ≤ M} (1 + w(n))`. -/
lemma sum_squarefree_prod_le (M : ℕ) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    ∑ a ∈ Finset.Icc 1 M, (μ a : ℝ) ^ 2 * ∏ p ∈ a.primeFactors, w p
      ≤ ∏ n ∈ Finset.Icc 2 M, (1 + w n) := by
  classical
  set P := (Finset.Icc 2 M).filter Nat.Prime with hP
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  -- rewrite the left side as a sum over squarefree numbers
  have hL : ∑ a ∈ Finset.Icc 1 M, (μ a : ℝ) ^ 2 * ∏ p ∈ a.primeFactors, w p
      = ∑ a ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ a.primeFactors, w p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hsf : Squarefree a
    · rw [if_pos hsf]
      have h1 : (μ a : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
      rw [h1, one_mul]
    · rw [if_neg hsf, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      norm_num
  rw [hL]
  -- every squarefree `a ≤ M` is a product of a subset of `P`
  have hsub : (Finset.Icc 1 M).filter Squarefree ⊆ P.powerset.image (fun t => ∏ p ∈ t, p) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, haM⟩, hsf⟩ := ha
    refine Finset.mem_image.mpr ⟨a.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hsf⟩
    refine Finset.mem_powerset.mpr (fun p hp => ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpa : p ∣ a := Nat.dvd_of_mem_primeFactors hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, ?_⟩, hpp⟩
    exact le_trans (Nat.le_of_dvd (by omega) hpa) haM
  have hnn : ∀ a ∈ P.powerset.image (fun t => ∏ p ∈ t, p),
      a ∉ (Finset.Icc 1 M).filter Squarefree → 0 ≤ ∏ p ∈ a.primeFactors, w p :=
    fun a _ _ => Finset.prod_nonneg (fun p _ => hw p)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
  -- the image sum is the powerset sum
  have hinj : ∀ x ∈ P.powerset, ∀ y ∈ P.powerset,
      (∏ p ∈ x, p) = (∏ p ∈ y, p) → x = y := by
    intro x hx y hy hxy
    have h1 : (∏ p ∈ x, p).primeFactors = x :=
      Nat.primeFactors_prod (fun p hp => hPprime p (Finset.mem_powerset.mp hx hp))
    have h2 : (∏ p ∈ y, p).primeFactors = y :=
      Nat.primeFactors_prod (fun p hp => hPprime p (Finset.mem_powerset.mp hy hp))
    rw [← h1, ← h2, hxy]
  rw [Finset.sum_image hinj]
  have hval : ∀ t ∈ P.powerset, ∏ p ∈ (∏ q ∈ t, q).primeFactors, w p = ∏ p ∈ t, w p := by
    intro t ht
    rw [Nat.primeFactors_prod (fun p hp => hPprime p (Finset.mem_powerset.mp ht hp))]
  rw [Finset.sum_congr rfl hval]
  -- the powerset sum is the Euler product over `P`
  have hprod : ∏ p ∈ P, (1 + w p) = ∑ t ∈ P.powerset, ∏ p ∈ t, w p := by
    have h := Finset.prod_add (fun p => w p) (fun _ => (1 : ℝ)) P
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl (fun p _ => by ring)
  rw [← hprod]
  exact prod_le_prod_subset_one_le (Finset.filter_subset _ _) _ (fun n => by linarith [hw n])

/-- The comparison sequence `u(n) = (2n−1)/(n(n−1)²)`, an upper bound for the local
factors of `(δ/φ(δ))²/δ`. -/
noncomputable def uSeq (n : ℕ) : ℝ := (2 * (n : ℝ) - 1) / ((n : ℝ) * ((n : ℝ) - 1) ^ 2)

lemma uSeq_nonneg (n : ℕ) : 0 ≤ uSeq n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> norm_num [uSeq]
  · have h1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    refine div_nonneg (by linarith) ?_
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- The telescoping tail bound `∑_{6 ≤ n ≤ M} u(n) ≤ 1/2 − 2/(M−1)`. -/
private lemma sum_uSeq_tail : ∀ (M : ℕ), 5 ≤ M →
    ∑ n ∈ Finset.Icc 6 M, uSeq n ≤ 1 / 2 - 2 / ((M : ℝ) - 1) := by
  intro M
  induction M with
  | zero => intro h; omega
  | succ K ih =>
    intro hM
    rcases Nat.lt_or_ge K 5 with hK | hK
    · have hK4 : K = 4 := by omega
      subst hK4
      have hemp : (Finset.Icc 6 (4 + 1) : Finset ℕ) = ∅ := by decide
      rw [hemp]
      norm_num
    · have hstep : ∑ n ∈ Finset.Icc 6 (K + 1), uSeq n
          = (∑ n ∈ Finset.Icc 6 K, uSeq n) + uSeq (K + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      rw [hstep]
      have h1 := ih (by omega)
      have hterm : uSeq (K + 1) = (2 * ((K : ℝ) + 1) - 1) / (((K : ℝ) + 1) * (K : ℝ) ^ 2) := by
        simp only [uSeq]
        push_cast
        ring_nf
      have hbnd : uSeq (K + 1) ≤ 2 / ((K : ℝ) - 1) - 2 / (K : ℝ) := by
        rw [hterm]
        rw [div_sub_div _ _ (by linarith : (K : ℝ) - 1 ≠ 0) (by linarith : (K : ℝ) ≠ 0)]
        rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
        nlinarith [sq_nonneg ((K : ℝ) - 1), sq_nonneg (K : ℝ)]
      have hcast : ((K : ℕ) + 1 : ℝ) - 1 = (K : ℝ) := by ring
      push_cast
      rw [hcast]
      linarith

/-- `∏_{2 ≤ n ≤ M} (1 + u(n)) ≤ 8`. -/
lemma prod_one_add_uSeq_le (M : ℕ) : ∏ n ∈ Finset.Icc 2 M, (1 + uSeq n) ≤ 8 := by
  classical
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ 1 + uSeq n := fun n => by linarith [uSeq_nonneg n]
  rcases Nat.lt_or_ge M 6 with hM | hM
  · have hsub : Finset.Icc 2 M ⊆ Finset.Icc 2 5 := by
      intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    refine le_trans (prod_le_prod_subset_one_le hsub _ hone) ?_
    have h5 : (Finset.Icc 2 5 : Finset ℕ) = {2, 3, 4, 5} := by decide
    rw [h5]
    norm_num [uSeq]
  · have hunion : Finset.Icc 2 M = Finset.Icc 2 5 ∪ Finset.Icc 6 M := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.Icc 2 5) (Finset.Icc 6 M) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      simp only [Finset.mem_Icc] at hn hn'
      omega
    rw [hunion, Finset.prod_union hdisj]
    have h1 : ∏ n ∈ Finset.Icc 2 5, (1 + uSeq n) ≤ 4.71 := by
      have h5 : (Finset.Icc 2 5 : Finset ℕ) = {2, 3, 4, 5} := by decide
      rw [h5]
      norm_num [uSeq]
    have h2 : ∏ n ∈ Finset.Icc 6 M, (1 + uSeq n) ≤ Real.exp (1 / 2) := by
      calc ∏ n ∈ Finset.Icc 6 M, (1 + uSeq n)
          ≤ ∏ n ∈ Finset.Icc 6 M, Real.exp (uSeq n) := by
            refine Finset.prod_le_prod (fun n _ => by linarith [hone n]) (fun n _ => ?_)
            have := Real.add_one_le_exp (uSeq n)
            linarith
        _ = Real.exp (∑ n ∈ Finset.Icc 6 M, uSeq n) := by rw [Real.exp_sum]
        _ ≤ Real.exp (1 / 2) := by
            refine Real.exp_le_exp.mpr ?_
            have h := sum_uSeq_tail M (by omega)
            have hMR : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
            have hnn : (0 : ℝ) ≤ 2 / ((M : ℝ) - 1) := by
              refine div_nonneg (by norm_num) (by linarith)
            linarith
    have hpos1 : (0 : ℝ) ≤ ∏ n ∈ Finset.Icc 2 5, (1 + uSeq n) :=
      Finset.prod_nonneg (fun n _ => by linarith [hone n])
    have hpos2 : (0 : ℝ) ≤ ∏ n ∈ Finset.Icc 6 M, (1 + uSeq n) :=
      Finset.prod_nonneg (fun n _ => by linarith [hone n])
    have hexp : Real.exp (1 / 2) ≤ 1.6488 := by
      have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h9 := Real.exp_one_lt_d9
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    nlinarith [h1, h2, hpos1, hpos2]


/-! ### The `U`-sum bound (crude replacement for RZA Lemma 3.2) -/

/-- `∑_{m ≤ M} 1/m ≤ 1 + log M`. -/
lemma sum_inv_le_one_add_log (M : ℕ) : ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m ≤ 1 + Real.log M := by
  have h : ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m = ((harmonic M : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by rw [one_div])
  rw [h]
  exact harmonic_le_one_add_log M

/-- For squarefree `δ`, `δ/φ(δ) = ∏_{p ∣ δ} p/(p−1)`. -/
lemma div_totient_eq_prod {δ : ℕ} (hδ : Squarefree δ) :
    (δ : ℝ) / (δ.totient : ℝ) = ∏ p ∈ δ.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hδ0 : δ ≠ 0 := hδ.ne_zero
  have hrad : ∏ p ∈ δ.primeFactors, p = δ := Nat.prod_primeFactors_of_squarefree hδ
  have hkey := Nat.totient_mul_prod_primeFactors δ
  rw [hrad] at hkey
  have htot : δ.totient = ∏ p ∈ δ.primeFactors, (p - 1) := by
    have hδpos : 0 < δ := Nat.pos_of_ne_zero hδ0
    have := hkey
    rw [mul_comm δ.totient δ] at this
    exact Nat.eq_of_mul_eq_mul_left hδpos this
  have hcast : ((∏ p ∈ δ.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ δ.primeFactors, ((p : ℝ) - 1) := by
    push_cast
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    push_cast [Nat.cast_sub hp1]
    ring
  have hcast2 : ((∏ p ∈ δ.primeFactors, p : ℕ) : ℝ) = ∏ p ∈ δ.primeFactors, (p : ℝ) := by
    push_cast; ring
  rw [Finset.prod_div_distrib, ← hcast2, ← hcast, hrad, htot]

/-- The local factors of `(δ/φ(δ))²`: `g(p) = (2p−1)/(p−1)²`. -/
noncomputable def gSeq (p : ℕ) : ℝ := (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2

/-- For squarefree `δ`, `(δ/φ(δ))² = ∑_{a ∣ δ} ∏_{p ∣ a} g(p)`. -/
lemma sq_div_totient_eq_sum {δ : ℕ} (hδ : Squarefree δ) :
    ((δ : ℝ) / (δ.totient : ℝ)) ^ 2 = ∑ a ∈ δ.divisors, ∏ p ∈ a.primeFactors, gSeq p := by
  rw [sum_divisors_prod_primeFactors hδ gSeq, div_totient_eq_prod hδ, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [gSeq, div_pow]
  field_simp
  ring

/-- **The `W`-sum.**  For `σ ≥ 1`,
`∑_{δ ≤ M} μ²(δ) φ_σ(δ) δ^{-2σ} (δ/φ(δ))² ≤ 8 (1 + log M)`. -/
lemma W_bound {σ : ℝ} (hσ : 1 ≤ σ) (M : ℕ) :
    ∑ δ ∈ Finset.Icc 1 M,
        (μ δ : ℝ) ^ 2 * phiSig σ δ * (δ : ℝ) ^ (-2 * σ) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2
      ≤ 8 * (1 + Real.log M) := by
  classical
  -- step 1: drop `φ_σ(δ) δ^{-2σ} ≤ 1/δ`
  have hstep1 : ∀ δ ∈ Finset.Icc 1 M,
      (μ δ : ℝ) ^ 2 * phiSig σ δ * (δ : ℝ) ^ (-2 * σ) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2
        ≤ (μ δ : ℝ) ^ 2 * (1 / (δ : ℝ)) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2 := by
    intro δ hδ
    simp only [Finset.mem_Icc] at hδ
    have hδ0 : δ ≠ 0 := by omega
    have hδR : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ.1
    have h1 : phiSig σ δ * (δ : ℝ) ^ (-2 * σ) ≤ 1 / (δ : ℝ) := by
      have hle : phiSig σ δ ≤ (δ : ℝ) ^ σ := phiSig_le_rpow (by linarith) hδ0
      have hpos : (0 : ℝ) < (δ : ℝ) ^ (-2 * σ) := Real.rpow_pos_of_pos (by linarith) _
      calc phiSig σ δ * (δ : ℝ) ^ (-2 * σ) ≤ (δ : ℝ) ^ σ * (δ : ℝ) ^ (-2 * σ) := by
            exact mul_le_mul_of_nonneg_right hle hpos.le
        _ = (δ : ℝ) ^ (-σ) := by
            rw [← Real.rpow_add (by linarith)]
            ring_nf
        _ ≤ (δ : ℝ) ^ (-1 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le hδR (by linarith)
        _ = 1 / (δ : ℝ) := by rw [Real.rpow_neg_one, one_div]
    have hnn : (0 : ℝ) ≤ (μ δ : ℝ) ^ 2 * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2 := by positivity
    nlinarith [h1, hnn, sq_nonneg ((δ : ℝ) / (δ.totient : ℝ)), sq_nonneg ((μ δ : ℝ))]
  refine le_trans (Finset.sum_le_sum hstep1) ?_
  -- step 2: expand `(δ/φ(δ))²` over divisors
  have hstep2 : ∀ δ ∈ Finset.Icc 1 M,
      (μ δ : ℝ) ^ 2 * (1 / (δ : ℝ)) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2
        ≤ ∑ a ∈ δ.divisors,
            ((μ a : ℝ) ^ 2 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ))
              * ((μ (δ / a) : ℝ) ^ 2 / ((δ / a : ℕ) : ℝ)) := by
    intro δ hδ
    simp only [Finset.mem_Icc] at hδ
    have hδ0 : δ ≠ 0 := by omega
    by_cases hsf : Squarefree δ
    · have hμ : (μ δ : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
      rw [hμ, one_mul, sq_div_totient_eq_sum hsf, Finset.mul_sum]
      refine Finset.sum_le_sum (fun a ha => ?_)
      rw [Nat.mem_divisors] at ha
      obtain ⟨hadvd, -⟩ := ha
      have ha0 : a ≠ 0 := by rintro rfl; exact hδ0 (zero_dvd_iff.mp hadvd)
      have hasf : Squarefree a := hsf.squarefree_of_dvd hadvd
      have hbsf : Squarefree (δ / a) := hsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hadvd)
      have hμa : (μ a : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hasf
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
      have hμb : (μ (δ / a) : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hbsf
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
      have hab : (a : ℝ) * ((δ / a : ℕ) : ℝ) = (δ : ℝ) := by
        have : a * (δ / a) = δ := Nat.mul_div_cancel' hadvd
        exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
      rw [hμa, hμb]
      have haR : (0 : ℝ) < (a : ℝ) := by
        have : 0 < a := Nat.pos_of_ne_zero ha0
        exact_mod_cast this
      have hbR : (0 : ℝ) < ((δ / a : ℕ) : ℝ) := by
        have : 0 < δ / a := Nat.div_pos (Nat.le_of_dvd (by omega) hadvd) (Nat.pos_of_ne_zero ha0)
        exact_mod_cast this
      have hEq : (1 : ℝ) / (δ : ℝ) * ∏ p ∈ a.primeFactors, gSeq p
          = 1 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ) * (1 / ((δ / a : ℕ) : ℝ)) := by
        rw [← hab]
        field_simp
      rw [hEq]
    · have hμ : (μ δ : ℝ) ^ 2 = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
      rw [hμ]
      refine le_trans (by norm_num) (Finset.sum_nonneg (fun a ha => ?_))
      rw [Nat.mem_divisors] at ha
      have hg : (0 : ℝ) ≤ ∏ p ∈ a.primeFactors, gSeq p := by
        refine Finset.prod_nonneg (fun p hp => ?_)
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        rw [gSeq]
        refine div_nonneg (by linarith) (sq_nonneg _)
      positivity
  refine le_trans (Finset.sum_le_sum hstep2) ?_
  -- step 3: hyperbola
  rw [← hyperbola_sum M (fun a => (μ a : ℝ) ^ 2 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ))
      (fun b => (μ b : ℝ) ^ 2 / (b : ℝ))]
  have hinner : ∀ a ∈ Finset.Icc 1 M,
      ∑ b ∈ Finset.Icc 1 (M / a), ((μ a : ℝ) ^ 2 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ))
          * ((μ b : ℝ) ^ 2 / (b : ℝ))
        ≤ ((μ a : ℝ) ^ 2 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ)) * (1 + Real.log M) := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    have hfa : (0 : ℝ) ≤ (μ a : ℝ) ^ 2 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ) := by
      have hg : (0 : ℝ) ≤ ∏ p ∈ a.primeFactors, gSeq p := by
        refine Finset.prod_nonneg (fun p hp => ?_)
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
        rw [gSeq]
        refine div_nonneg (by linarith) (sq_nonneg _)
      positivity
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hfa
    have h1 : ∑ b ∈ Finset.Icc 1 (M / a), ((μ b : ℝ) ^ 2 / (b : ℝ))
        ≤ ∑ b ∈ Finset.Icc 1 (M / a), (1 : ℝ) / b := by
      refine Finset.sum_le_sum (fun b hb => ?_)
      simp only [Finset.mem_Icc] at hb
      have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb.1
      have hμb : (μ b : ℝ) ^ 2 ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := b)
        have : |(μ b : ℝ)| ≤ 1 := by exact_mod_cast h
        nlinarith [abs_nonneg ((μ b : ℝ)), sq_abs ((μ b : ℝ))]
      gcongr
    have h2 : ∑ b ∈ Finset.Icc 1 (M / a), (1 : ℝ) / b ≤ ∑ b ∈ Finset.Icc 1 M, (1 : ℝ) / b := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => by positivity)
      exact Finset.Icc_subset_Icc_right (Nat.div_le_self M a)
    linarith [sum_inv_le_one_add_log M, h1, h2]
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.sum_mul]
  have hlog : (0 : ℝ) ≤ 1 + Real.log M := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · norm_num
    · have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have := Real.log_nonneg this
      linarith
  have hC : ∑ a ∈ Finset.Icc 1 M, (μ a : ℝ) ^ 2 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ)
      ≤ 8 := by
    have hrw : ∀ a ∈ Finset.Icc 1 M,
        (μ a : ℝ) ^ 2 * (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ)
          ≤ (μ a : ℝ) ^ 2 * ∏ p ∈ a.primeFactors, uSeq p := by
      intro a ha
      simp only [Finset.mem_Icc] at ha
      by_cases hsf : Squarefree a
      · have hμa : (μ a : ℝ) ^ 2 = 1 := by
          have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
        rw [hμa, one_mul, one_mul]
        have hrad : ((∏ p ∈ a.primeFactors, p : ℕ) : ℝ) = (a : ℝ) := by
          rw [Nat.prod_primeFactors_of_squarefree hsf]
        have hsplit : ∏ p ∈ a.primeFactors, uSeq p
            = (∏ p ∈ a.primeFactors, gSeq p) / (a : ℝ) := by
          rw [← hrad]
          push_cast
          rw [← Finset.prod_div_distrib]
          refine Finset.prod_congr rfl (fun p hp => ?_)
          have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
          have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          rw [uSeq, gSeq]
          field_simp
        rw [hsplit]
      · have hμ : (μ a : ℝ) ^ 2 = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
        rw [hμ]
        norm_num
    refine le_trans (Finset.sum_le_sum hrw) ?_
    refine le_trans (sum_squarefree_prod_le M uSeq uSeq_nonneg) ?_
    exact prod_one_add_uSeq_le M
  nlinarith [hC, hlog]


/-! ### Item (iv): the elementary `ζ`-bound `ζ(σ) ≤ 1 + 1/(σ−1)` -/

/-- `ζ(σ) = ∑_{n ≥ 1} n^{-σ}` (the `n = 0` term of the `tsum` is `0^{-σ} = 0`). -/
noncomputable def zetaR (σ : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-σ)

lemma summable_rpow_neg {σ : ℝ} (hσ : 1 < σ) : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
  have h : ∀ n : ℕ, (n : ℝ) ^ (-σ) = ((n : ℝ) ^ σ)⁻¹ :=
    fun n => Real.rpow_neg (Nat.cast_nonneg n) σ
  simp only [h]
  exact (Real.summable_nat_rpow_inv (p := σ)).mpr hσ

lemma zetaR_nonneg (σ : ℝ) : 0 ≤ zetaR σ :=
  tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The telescoping step `(σ−1) n^{-σ} ≤ (n−1)^{1−σ} − n^{1−σ}` for `n ≥ 2`. -/
private lemma rpow_neg_le_telescope {σ : ℝ} (hσ : 1 < σ) {n : ℕ} (hn : 2 ≤ n) :
    (σ - 1) * (n : ℝ) ^ (-σ) ≤ ((n : ℝ) - 1) ^ (1 - σ) - (n : ℝ) ^ (1 - σ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  set a := σ - 1 with ha
  have ha0 : 0 < a := by simp only [ha]; linarith
  set y := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by
    rw [hy, div_lt_one hn0]; linarith
  have hxy : (1 : ℝ) - y = ((n : ℝ) - 1) / (n : ℝ) := by
    rw [hy]; field_simp
  -- `(1−y)^{-a} ≥ exp(a y) ≥ 1 + a y`
  have hlog : Real.log (1 - y) ≤ -y := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - y by linarith)
    linarith
  have hkey : (1 : ℝ) + a * y ≤ (1 - y) ^ (-a) := by
    have h1 : (1 - y) ^ (-a) = Real.exp (-a * Real.log (1 - y)) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      ring_nf
    rw [h1]
    have h2 : a * y ≤ -a * Real.log (1 - y) := by nlinarith
    calc (1 : ℝ) + a * y ≤ Real.exp (a * y) := by
          have := Real.add_one_le_exp (a * y); linarith
      _ ≤ Real.exp (-a * Real.log (1 - y)) := Real.exp_le_exp.mpr h2
  -- convert
  have hpow : (1 - y) ^ (-a) = ((n : ℝ) - 1) ^ (-a) * (n : ℝ) ^ a := by
    rw [hxy, Real.div_rpow (by linarith) (le_of_lt hn0), Real.rpow_neg (by linarith),
      Real.rpow_neg (le_of_lt hn0), div_eq_mul_inv, inv_inv]
  have hexp1 : ((n : ℝ) - 1) ^ (1 - σ) = ((n : ℝ) - 1) ^ (-a) := by
    congr 1; simp only [ha]; ring
  have hexp2 : (n : ℝ) ^ (1 - σ) = (n : ℝ) ^ (-a) := by
    congr 1; simp only [ha]; ring
  have hna : (n : ℝ) ^ (-a) * (n : ℝ) ^ a = 1 := by
    rw [← Real.rpow_add hn0]; simp
  have hnsig : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (-a) * (n : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hn0]
    congr 1
    simp only [ha]; ring
  rw [hexp1, hexp2, hnsig]
  have hposa : (0 : ℝ) < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  have hposn : (0 : ℝ) < (n : ℝ) ^ (-a) := Real.rpow_pos_of_pos hn0 (-a)
  -- from `1 + a/n ≤ (n−1)^{-a} n^a`, multiply by `n^{-a}`
  have hstep : 1 + a * y ≤ ((n : ℝ) - 1) ^ (-a) * (n : ℝ) ^ a := by rw [← hpow]; exact hkey
  have hmul := mul_le_mul_of_nonneg_right hstep (le_of_lt hposn)
  have hcancel : ((n : ℝ) - 1) ^ (-a) * (n : ℝ) ^ a * (n : ℝ) ^ (-a)
      = ((n : ℝ) - 1) ^ (-a) := by
    rw [mul_assoc, mul_comm ((n : ℝ) ^ a), hna, mul_one]
  rw [hcancel] at hmul
  have hyval : a * y = a / (n : ℝ) := by rw [hy]; ring
  rw [hyval] at hmul
  have hrw : (σ - 1) * ((n : ℝ) ^ (-a) * (n : ℝ)⁻¹) = a * ((n : ℝ) ^ (-a) / (n : ℝ)) := by
    rw [← ha]
    ring
  rw [hrw]
  have hfin : a * ((n : ℝ) ^ (-a) / (n : ℝ)) ≤ ((n : ℝ) - 1) ^ (-a) - (n : ℝ) ^ (-a) := by
    have h1 : (1 + a / (n : ℝ)) * (n : ℝ) ^ (-a)
        = (n : ℝ) ^ (-a) + a * ((n : ℝ) ^ (-a) / (n : ℝ)) := by
      field_simp
    rw [h1] at hmul
    linarith
  linarith

/-- Partial sums: `∑_{n ≤ N} n^{-σ} ≤ 1 + 1/(σ−1)`. -/
private lemma sum_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤ 1 + 1 / (σ - 1) := by
  have hσ0 : 0 < σ - 1 := by linarith
  have key : ∀ N : ℕ, 1 ≤ N →
      (σ - 1) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤ (σ - 1) + 1 - (N : ℝ) ^ (1 - σ) := by
    intro N
    induction N with
    | zero => intro h; omega
    | succ K ih =>
      intro _
      rcases Nat.lt_or_ge K 1 with hK | hK
      · have hK0 : K = 0 := by omega
        subst hK0
        norm_num
      · have hstep : ∑ n ∈ Finset.Icc 1 (K + 1), (n : ℝ) ^ (-σ)
            = (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-σ)) + ((K : ℝ) + 1) ^ (-σ) := by
          rw [Finset.sum_Icc_succ_top (by omega)]
          push_cast
          ring
        rw [hstep, mul_add]
        have h1 := ih hK
        have h2 := rpow_neg_le_telescope hσ (n := K + 1) (by omega)
        have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
        rw [hcast] at h2
        have hc2 : ((K : ℝ) + 1) - 1 = (K : ℝ) := by ring
        rw [hc2] at h2
        push_cast
        linarith
  intro N
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hN0 : N = 0 := by omega
    subst hN0
    have hemp : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    rw [hemp, Finset.sum_empty]
    have : (0 : ℝ) < 1 / (σ - 1) := by positivity
    linarith
  · have hk := key N hN
    have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hs : (σ - 1) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤ (σ - 1) + 1 := by linarith
    have h2 : (σ - 1) * (1 + 1 / (σ - 1)) = (σ - 1) + 1 := by
      field_simp
    nlinarith [hs, h2]

/-- **`ζ(σ) ≤ 1 + 1/(σ−1)`.** -/
lemma zetaR_le {σ : ℝ} (hσ : 1 < σ) : zetaR σ ≤ 1 + 1 / (σ - 1) := by
  have hnn : ∀ i : ℕ, 0 ≤ (i : ℝ) ^ (-σ) := fun i => Real.rpow_nonneg (Nat.cast_nonneg i) _
  refine Real.tsum_le_of_sum_range_le hnn (fun N => ?_)
  have hzero : ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by intro h; linarith [neg_eq_zero.mp h])]
  have hsub : Finset.range N ⊆ insert 0 (Finset.Icc 1 N) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i)) ?_
  have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  rw [Finset.sum_insert hnotmem, hzero, zero_add]
  exact sum_rpow_neg_le hσ N

/-! ### Item (iii): the Selberg diagonalisation, RZA (9)–(11) -/

section Diagonalisation

open Detector

/-- `λ` vanishes on non-squarefree indices (the Möbius factor). -/
private lemma bvLam_eq_zero_of_not_squarefree {z1 z2 : ℝ} {d : ℕ} (hd : ¬ Squarefree d) :
    bvLam z1 z2 d = 0 := by
  rw [bvLam, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
  simp

/-- `q/φ(q) ≥ 1` for `q ≠ 0` (duplicate of the `private` one above `abs_mCheckQ_le`). -/
private lemma one_le_div_totient' {q : ℕ} (hq : q ≠ 0) :
    (1 : ℝ) ≤ (q : ℝ) / (q.totient : ℝ) := by
  have h1 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  have h2 : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast h1
  rw [le_div_iff₀ h2, one_mul]
  exact_mod_cast Nat.totient_le q

/-- `a(n) = ∑_{d ≤ ⌊z₂⌋₊} [d ∣ n] λ_d` for `n ≠ 0`: the weights with `d ≥ z₂` vanish. -/
lemma bvA_eq_sum_Icc {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 ≤ z2) {n : ℕ} (hn : n ≠ 0) :
    bvA z1 z2 n = ∑ d ∈ Finset.Icc 1 ⌊z2⌋₊, (if d ∣ n then bvLam z1 z2 d else 0) := by
  classical
  rw [bvA, ← Finset.sum_filter]
  refine (Finset.sum_subset (fun d hd => ?_) (fun d hd hd' => ?_)).symm
  · simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, hn⟩
  · rw [Nat.mem_divisors] at hd
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
      rintro rfl; exact hn (zero_dvd_iff.mp hd.1))
    have hdD : ⌊z2⌋₊ < d := by
      by_contra hcon
      push Not at hcon
      exact hd' (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hcon⟩, hd.1⟩)
    have hz2d : z2 ≤ (d : ℝ) := by
      have h1 : z2 < (⌊z2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z2
      have h2 : ((⌊z2⌋₊ + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdD
      push_cast at h2
      linarith
    exact bvLam_eq_zero hz1 hz12 hz2d

/-- `|a(n)| ≤ ⌊z₂⌋₊` (each of the at most `⌊z₂⌋₊` weights has `|λ| ≤ 1`). -/
private lemma abs_bvA_le {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (n : ℕ) :
    |bvA z1 z2 n| ≤ (⌊z2⌋₊ : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bvA, Nat.divisors_zero, Finset.sum_empty, abs_zero]
    exact Nat.cast_nonneg _
  · rw [bvA_eq_sum_Icc hz1 hz12.le hn.ne']
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.Icc 1 ⌊z2⌋₊, |if d ∣ n then bvLam z1 z2 d else 0| ≤ 1 := by
      intro d _
      by_cases hd : d ∣ n
      · rw [if_pos hd]; exact abs_bvLam_le_one hz1 hz12 d
      · rw [if_neg hd, abs_zero]; norm_num
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
    rw [nsmul_eq_mul, mul_one, Nat.card_Icc]
    simp

private lemma summable_rpow_bvA_sq {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) {σ : ℝ}
    (hσ : 1 < σ) : Summable (fun n : ℕ => (n : ℝ) ^ (-σ) * (bvA z1 z2 n) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_rpow_neg hσ).mul_left ((⌊z2⌋₊ : ℝ) ^ 2))
  · positivity
  · have h1 : (bvA z1 z2 n) ^ 2 ≤ (⌊z2⌋₊ : ℝ) ^ 2 := by
      rw [← sq_abs]
      have hb := abs_bvA_le hz1 hz12 n
      nlinarith [abs_nonneg (bvA z1 z2 n)]
    have h2 : (0:ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc (n : ℝ) ^ (-σ) * (bvA z1 z2 n) ^ 2 ≤ (n : ℝ) ^ (-σ) * (⌊z2⌋₊ : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = (⌊z2⌋₊ : ℝ) ^ 2 * (n : ℝ) ^ (-σ) := by ring

/-- Pointwise square expansion over lcm pairs (valid for every `n`, including `n = 0`
where `0^{-σ} = 0` kills both sides). -/
private lemma rpow_mul_bvA_sq {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 ≤ z2) {σ : ℝ}
    (hσ : 0 < σ) (n : ℕ) :
    (n : ℝ) ^ (-σ) * (bvA z1 z2 n) ^ 2
      = ∑ p ∈ Finset.Icc 1 ⌊z2⌋₊ ×ˢ Finset.Icc 1 ⌊z2⌋₊,
          bvLam z1 z2 p.1 * bvLam z1 z2 p.2 *
            (if Nat.lcm p.1 p.2 ∣ n then (n : ℝ) ^ (-σ) else 0) := by
  rw [Finset.sum_product]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (by linarith : -σ < 0).ne
    rw [h0, zero_mul]
    symm
    refine Finset.sum_eq_zero (fun d _ => Finset.sum_eq_zero (fun e _ => ?_))
    rw [if_pos (Nat.dvd_zero _), mul_zero]
  · rw [bvA_eq_sum_Icc hz1 hz12 hn.ne', sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hd : d ∣ n
    · by_cases he : e ∣ n
      · rw [if_pos hd, if_pos he, if_pos (Nat.lcm_dvd hd he)]; ring
      · rw [if_pos hd, if_neg he, if_neg (fun h => he (dvd_trans (Nat.dvd_lcm_right d e) h))]
        ring
    · rw [if_neg hd, if_neg (fun h => hd (dvd_trans (Nat.dvd_lcm_left d e) h))]
      by_cases he : e ∣ n
      · rw [if_pos he]; ring
      · rw [if_neg he]; ring

private lemma summable_ite_multiples {σ : ℝ} (hσ : 1 < σ) (m : ℕ) :
    Summable (fun n : ℕ => (if m ∣ n then (n : ℝ) ^ (-σ) else 0)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_rpow_neg hσ)
  · by_cases h : m ∣ n
    · rw [if_pos h]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [if_neg h]
  · by_cases h : m ∣ n
    · rw [if_pos h]
    · rw [if_neg h]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- `∑'_{m ∣ n} n^{-σ} = m^{-σ} ζ_R(σ)` (reindex along `n = m k`; no summability
is needed: both sides are junk-consistent). -/
private lemma tsum_rpow_multiples {σ : ℝ} {m : ℕ} (hm : m ≠ 0) :
    ∑' n : ℕ, (if m ∣ n then (n : ℝ) ^ (-σ) else 0) = (m : ℝ) ^ (-σ) * zetaR σ := by
  have hinj : Function.Injective (fun k : ℕ => m * k) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h
  have hsupp : Function.support (fun n : ℕ => (if m ∣ n then (n : ℝ) ^ (-σ) else 0))
      ⊆ Set.range (fun k : ℕ => m * k) := by
    intro n hn
    simp only [Function.mem_support] at hn
    by_cases hdvd : m ∣ n
    · obtain ⟨k, rfl⟩ := hdvd
      exact ⟨k, rfl⟩
    · exact absurd (if_neg hdvd) hn
  rw [← hinj.tsum_eq hsupp]
  have hterm : ∀ k : ℕ, (if m ∣ m * k then ((m * k : ℕ) : ℝ) ^ (-σ) else 0)
      = (m : ℝ) ^ (-σ) * (k : ℝ) ^ (-σ) := by
    intro k
    rw [if_pos (Dvd.intro k rfl), Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg k)]
  rw [tsum_congr hterm, tsum_mul_left]
  rfl

/-- **Diagonalisation, step 1** (RZA (10) over `tsum`s):
`∑'_n n^{-σ} a(n)² = ζ_R(σ) · ∑_{d,e ≤ z₂} λ_d λ_e lcm(d,e)^{-σ}`. -/
lemma tsum_rpow_bvA_sq {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) * (bvA z1 z2 n) ^ 2
      = zetaR σ * ∑ p ∈ Finset.Icc 1 ⌊z2⌋₊ ×ˢ Finset.Icc 1 ⌊z2⌋₊,
          bvLam z1 z2 p.1 * bvLam z1 z2 p.2 * ((Nat.lcm p.1 p.2 : ℕ) : ℝ) ^ (-σ) := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hpt : ∀ n : ℕ, (n : ℝ) ^ (-σ) * (bvA z1 z2 n) ^ 2
      = ∑ p ∈ Finset.Icc 1 ⌊z2⌋₊ ×ˢ Finset.Icc 1 ⌊z2⌋₊,
          bvLam z1 z2 p.1 * bvLam z1 z2 p.2 *
            (if Nat.lcm p.1 p.2 ∣ n then (n : ℝ) ^ (-σ) else 0) := by
    intro n
    rw [rpow_mul_bvA_sq hz1 hz12.le hσ0 n, Finset.sum_product]
  have hsummable : ∀ p ∈ Finset.Icc 1 ⌊z2⌋₊ ×ˢ Finset.Icc 1 ⌊z2⌋₊,
      Summable (fun n : ℕ => bvLam z1 z2 p.1 * bvLam z1 z2 p.2 *
        (if Nat.lcm p.1 p.2 ∣ n then (n : ℝ) ^ (-σ) else 0)) :=
    fun p _ => (summable_ite_multiples hσ _).mul_left _
  rw [tsum_congr hpt, Summable.tsum_finsetSum hsummable, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [Finset.mem_product, Finset.mem_Icc] at hp
  have hlcm : Nat.lcm p.1 p.2 ≠ 0 := by
    have h := Nat.gcd_mul_lcm p.1 p.2
    intro hl
    rw [hl, mul_zero] at h
    have h1 : 1 ≤ p.1 := hp.1.1
    have h2 : 1 ≤ p.2 := hp.2.1
    nlinarith [h.symm]
  rw [tsum_mul_left, tsum_rpow_multiples hlcm]
  ring

/-- `S_δ = ∑_{d ≤ ⌊z₂⌋₊, δ ∣ d} λ_d d^{-σ}` (RZA's diagonalising linear form). -/
noncomputable def Ssum (z1 z2 σ : ℝ) (δ : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊z2⌋₊, (if δ ∣ d then bvLam z1 z2 d * (d : ℝ) ^ (-σ) else 0)

private lemma lcm_rpow_neg_eq {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) (σ : ℝ) :
    ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
      = ((Nat.gcd d e : ℕ) : ℝ) ^ σ * ((d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ)) := by
  have hgl : Nat.gcd d e * Nat.lcm d e = d * e := Nat.gcd_mul_lcm d e
  have hg0 : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero hd)
  have hl0 : 0 < Nat.lcm d e := by
    rcases Nat.eq_zero_or_pos (Nat.lcm d e) with h | h
    · rw [h, mul_zero] at hgl
      have := Nat.pos_of_ne_zero hd
      have := Nat.pos_of_ne_zero he
      nlinarith [hgl.symm]
    · exact h
  have hgR : (0:ℝ) < ((Nat.gcd d e : ℕ) : ℝ) := by exact_mod_cast hg0
  have hlR : (0:ℝ) < ((Nat.lcm d e : ℕ) : ℝ) := by exact_mod_cast hl0
  have hprodR : ((Nat.gcd d e : ℕ) : ℝ) * ((Nat.lcm d e : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hgl
  have h1 : ((Nat.gcd d e : ℕ) : ℝ) ^ (-σ) * ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
      = (d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ) := by
    rw [← Real.mul_rpow hgR.le hlR.le, hprodR,
      Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg e)]
  have h2 : ((Nat.gcd d e : ℕ) : ℝ) ^ σ * ((Nat.gcd d e : ℕ) : ℝ) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hgR]
    simp
  calc ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
      = (((Nat.gcd d e : ℕ) : ℝ) ^ σ * ((Nat.gcd d e : ℕ) : ℝ) ^ (-σ))
          * ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ) := by rw [h2, one_mul]
    _ = ((Nat.gcd d e : ℕ) : ℝ) ^ σ
          * (((Nat.gcd d e : ℕ) : ℝ) ^ (-σ) * ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)) := by ring
    _ = ((Nat.gcd d e : ℕ) : ℝ) ^ σ * ((d : ℝ) ^ (-σ) * (e : ℝ) ^ (-σ)) := by rw [h1]

private lemma filter_dvd_eq_divisors_gcd {D d e : ℕ} (hd : d ≠ 0) (hdD : d ≤ D) :
    ((Finset.Icc 1 D).filter (fun δ => δ ∣ d ∧ δ ∣ e)) = (Nat.gcd d e).divisors := by
  ext δ
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, hD⟩, hdd, hde⟩
    exact ⟨Nat.dvd_gcd hdd hde, fun h => hd (Nat.eq_zero_of_gcd_eq_zero_left h)⟩
  · rintro ⟨hg, hg0⟩
    have hdd : δ ∣ d := hg.trans (Nat.gcd_dvd_left d e)
    have hde : δ ∣ e := hg.trans (Nat.gcd_dvd_right d e)
    have hδ0 : δ ≠ 0 := by rintro rfl; exact hd (zero_dvd_iff.mp hdd)
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hδ0,
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdd) hdD⟩, hdd, hde⟩

/-- **Diagonalisation, step 2** (RZA (9)/(11) insertion):
`∑_{d,e ≤ z₂} λ_d λ_e lcm(d,e)^{-σ} = ∑_{δ ≤ z₂} φ_σ(δ) S_δ²`. -/
lemma sum_lcm_eq_sum_phiSig_Ssum_sq (z1 z2 σ : ℝ) :
    ∑ p ∈ Finset.Icc 1 ⌊z2⌋₊ ×ˢ Finset.Icc 1 ⌊z2⌋₊,
        bvLam z1 z2 p.1 * bvLam z1 z2 p.2 * ((Nat.lcm p.1 p.2 : ℕ) : ℝ) ^ (-σ)
      = ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, phiSig σ δ * (Ssum z1 z2 σ δ) ^ 2 := by
  classical
  rw [Finset.sum_product]
  -- pointwise gcd-insertion
  have hpt : ∀ d ∈ Finset.Icc 1 ⌊z2⌋₊, ∀ e ∈ Finset.Icc 1 ⌊z2⌋₊,
      bvLam z1 z2 d * bvLam z1 z2 e * ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ)
        = ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, phiSig σ δ *
            ((if δ ∣ d then bvLam z1 z2 d * (d : ℝ) ^ (-σ) else 0) *
             (if δ ∣ e then bvLam z1 z2 e * (e : ℝ) ^ (-σ) else 0)) := by
    intro d hd e he
    simp only [Finset.mem_Icc] at hd he
    by_cases hsfd : Squarefree d
    · by_cases hsfe : Squarefree e
      · -- both squarefree: the real case
        have hd0 : d ≠ 0 := hsfd.ne_zero
        have he0 : e ≠ 0 := hsfe.ne_zero
        have hgsf : Squarefree (Nat.gcd d e) := hsfd.squarefree_of_dvd (Nat.gcd_dvd_left d e)
        have hcomb : ∀ δ ∈ Finset.Icc 1 ⌊z2⌋₊, phiSig σ δ *
            ((if δ ∣ d then bvLam z1 z2 d * (d : ℝ) ^ (-σ) else 0) *
             (if δ ∣ e then bvLam z1 z2 e * (e : ℝ) ^ (-σ) else 0))
            = (if δ ∣ d ∧ δ ∣ e then phiSig σ δ else 0) *
                (bvLam z1 z2 d * (d : ℝ) ^ (-σ) * (bvLam z1 z2 e * (e : ℝ) ^ (-σ))) := by
          intro δ _
          by_cases h1 : δ ∣ d
          · by_cases h2 : δ ∣ e
            · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
            · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; ring
          · by_cases h2 : δ ∣ e
            · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; ring
            · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1)]; ring
        rw [Finset.sum_congr rfl hcomb, ← Finset.sum_mul, ← Finset.sum_filter,
          filter_dvd_eq_divisors_gcd hd0 hd.2, sum_divisors_phiSig hgsf,
          lcm_rpow_neg_eq hd0 he0]
        ring
      · -- `e` not squarefree: both sides vanish
        rw [bvLam_eq_zero_of_not_squarefree hsfe]
        simp
    · -- `d` not squarefree: both sides vanish
      rw [bvLam_eq_zero_of_not_squarefree hsfd]
      simp
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hpt d hd e he))]
  -- swap the δ-sum out
  have hswap : ∑ d ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
      phiSig σ δ * ((if δ ∣ d then bvLam z1 z2 d * (d : ℝ) ^ (-σ) else 0) *
        (if δ ∣ e then bvLam z1 z2 e * (e : ℝ) ^ (-σ) else 0))
      = ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ d ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z2⌋₊,
        phiSig σ δ * ((if δ ∣ d then bvLam z1 z2 d * (d : ℝ) ^ (-σ) else 0) *
          (if δ ∣ e then bvLam z1 z2 e * (e : ℝ) ^ (-σ) else 0)) := by
    rw [show (∑ d ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
        phiSig σ δ * ((if δ ∣ d then bvLam z1 z2 d * (d : ℝ) ^ (-σ) else 0) *
          (if δ ∣ e then bvLam z1 z2 e * (e : ℝ) ^ (-σ) else 0)))
        = ∑ d ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, ∑ e ∈ Finset.Icc 1 ⌊z2⌋₊,
          phiSig σ δ * ((if δ ∣ d then bvLam z1 z2 d * (d : ℝ) ^ (-σ) else 0) *
            (if δ ∣ e then bvLam z1 z2 e * (e : ℝ) ^ (-σ) else 0))
      from Finset.sum_congr rfl (fun d _ => Finset.sum_comm)]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [show (Ssum z1 z2 σ δ) ^ 2 = Ssum z1 z2 σ δ * Ssum z1 z2 σ δ from sq _]
  rw [Ssum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mul_sum]

/-- `S_δ = 0` for non-squarefree `δ` (all its multiples carry `μ = 0`). -/
lemma Ssum_eq_zero_of_not_squarefree {z1 z2 σ : ℝ} {δ : ℕ} (hδ : ¬ Squarefree δ) :
    Ssum z1 z2 σ δ = 0 := by
  refine Finset.sum_eq_zero (fun d _ => ?_)
  by_cases hdvd : δ ∣ d
  · rw [if_pos hdvd,
      bvLam_eq_zero_of_not_squarefree (fun hsf => hδ (hsf.squarefree_of_dvd hdvd)), zero_mul]
  · rw [if_neg hdvd]

/-- **`S_δ` in terms of `m̌_δ`** (RZA (11)): for squarefree `δ ≤ z₂`,
`S_δ = μ(δ) δ^{-σ} (m̌_δ(z₂/δ, σ) − m̌_δ(z₁/δ, σ)) / log(z₂/z₁)`. -/
lemma Ssum_eq_mCheckQ {z1 z2 : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 ≤ z2) (σ : ℝ) {δ : ℕ}
    (hδsf : Squarefree δ) :
    Ssum z1 z2 σ δ = (μ δ : ℝ) * (δ : ℝ) ^ (-σ)
      * (mCheckQ δ (z2 / δ) σ - mCheckQ δ (z1 / δ) σ) / Real.log (z2 / z1) := by
  classical
  have hδ1 : 1 ≤ δ := Nat.one_le_iff_ne_zero.mpr hδsf.ne_zero
  have hδpos : 0 < δ := hδ1
  have hδR : (1:ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ1
  have hδ0R : (0:ℝ) < (δ : ℝ) := by linarith
  have hz20 : (0:ℝ) < z2 := by linarith
  -- step 1: reindex the filtered sum by `d = δ ℓ`
  have hfilter : Ssum z1 z2 σ δ
      = ∑ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ), bvLam z1 z2 (δ * ℓ) * ((δ * ℓ : ℕ) : ℝ) ^ (-σ) := by
    rw [Ssum, ← Finset.sum_filter]
    refine (Finset.sum_nbij' (i := fun ℓ => δ * ℓ) (j := fun d => d / δ) ?_ ?_ ?_ ?_ ?_).symm
    · intro ℓ hℓ
      simp only [Finset.mem_Icc] at hℓ
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hδpos.ne' (by omega)), ?_⟩,
        Dvd.intro ℓ rfl⟩
      exact (Nat.le_div_iff_mul_le hδpos).mp hℓ.2 |>.trans_eq' (by ring)
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdD⟩, hdvd⟩ := hd
      simp only [Finset.mem_Icc]
      exact ⟨Nat.one_le_div_iff hδpos |>.mpr (Nat.le_of_dvd (by omega) hdvd),
        Nat.div_le_div_right hdD⟩
    · intro ℓ _
      exact Nat.mul_div_cancel_left ℓ hδpos
    · intro d hd
      simp only [Finset.mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro ℓ _
      rfl
  -- step 2: split `λ_{δℓ}` multiplicatively
  have hterm : ∀ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ),
      bvLam z1 z2 (δ * ℓ) * ((δ * ℓ : ℕ) : ℝ) ^ (-σ)
        = (μ δ : ℝ) * (δ : ℝ) ^ (-σ) / Real.log (z2 / z1) *
            (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) *
              (Real.posLog (z2 / δ / ℓ) - Real.posLog (z1 / δ / ℓ)) else 0) := by
    intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    have hℓ1 : 1 ≤ ℓ := hℓ.1
    have hℓR : (0:ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ1
    have hcast : ((δ * ℓ : ℕ) : ℝ) = (δ : ℝ) * (ℓ : ℝ) := by push_cast; ring
    by_cases hcop : Nat.Coprime ℓ δ
    · have hμ : (μ (δ * ℓ) : ℝ) = (μ δ : ℝ) * (μ ℓ : ℝ) := by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.symm]
        push_cast
        ring
      rw [if_pos hcop, bvLam, hμ, hcast, Real.mul_rpow hδ0R.le hℓR.le, div_div, div_div]
      ring
    · have hnsf : ¬ Squarefree (δ * ℓ) := by
        intro hsf
        exact hcop (Nat.coprime_of_squarefree_mul hsf).symm
      have hμ0 : (μ (δ * ℓ) : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]
        norm_num
      rw [if_neg hcop, bvLam, hμ0]
      ring
  -- step 3: identify the two `posLog` sums with `mCheckQ`
  have hfloor2 : ⌊z2 / (δ : ℝ)⌋₊ = ⌊z2⌋₊ / δ := Nat.floor_div_natCast z2 δ
  have hS2 : ∑ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ),
      (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) * Real.posLog (z2 / δ / ℓ) else 0)
      = mCheckQ δ (z2 / δ) σ := by
    rw [mCheckQ, hfloor2]
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    simp only [Finset.mem_Icc] at hℓ
    by_cases hcop : Nat.Coprime ℓ δ
    · rw [if_pos hcop, if_pos hcop]
      have hℓR : (0:ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.1
      have hle : (ℓ : ℝ) ≤ z2 / δ := by
        have h1 : (ℓ : ℝ) ≤ ((⌊z2⌋₊ / δ : ℕ) : ℝ) := by exact_mod_cast hℓ.2
        have h2 : ((⌊z2⌋₊ / δ : ℕ) : ℝ) = ((⌊z2 / (δ : ℝ)⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hfloor2.symm
        rw [h2] at h1
        exact le_trans h1 (Nat.floor_le (by positivity))
      have h1 : (1:ℝ) ≤ z2 / δ / ℓ := by
        rw [le_div_iff₀ hℓR, one_mul]
        exact hle
      rw [posLog_of_one_le h1]
    · rw [if_neg hcop, if_neg hcop]
  have hS1 : ∑ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ),
      (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) * Real.posLog (z1 / δ / ℓ) else 0)
      = mCheckQ δ (z1 / δ) σ := by
    have hfloor1 : ⌊z1 / (δ : ℝ)⌋₊ = ⌊z1⌋₊ / δ := Nat.floor_div_natCast z1 δ
    have hz10 : (0:ℝ) < z1 := by linarith
    have hsub : Finset.Icc 1 ⌊z1 / (δ : ℝ)⌋₊ ⊆ Finset.Icc 1 (⌊z2⌋₊ / δ) := by
      apply Finset.Icc_subset_Icc_right
      rw [hfloor1]
      exact Nat.div_le_div_right (Nat.floor_le_floor hz12)
    have hvan : ∀ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ), ℓ ∉ Finset.Icc 1 ⌊z1 / (δ : ℝ)⌋₊ →
        (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) * Real.posLog (z1 / δ / ℓ) else 0)
          = 0 := by
      intro ℓ hℓ hℓ'
      simp only [Finset.mem_Icc] at hℓ hℓ'
      by_cases hcop : Nat.Coprime ℓ δ
      · rw [if_pos hcop]
        have hℓR : (0:ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.1
        have hgt : z1 / (δ : ℝ) < (ℓ : ℝ) := by
          have h1 : ⌊z1 / (δ : ℝ)⌋₊ < ℓ := by
            rcases Nat.lt_or_ge ⌊z1 / (δ : ℝ)⌋₊ ℓ with h | h
            · exact h
            · exact absurd ⟨hℓ.1, h⟩ hℓ'
          calc z1 / (δ : ℝ) < (⌊z1 / (δ : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
            _ ≤ (ℓ : ℝ) := by exact_mod_cast h1
        have hlt1 : z1 / δ / ℓ ≤ 1 := by
          rw [div_le_one hℓR]
          linarith
        rw [posLog_of_le_one (by positivity) hlt1, mul_zero]
      · rw [if_neg hcop]
    calc ∑ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ),
        (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) * Real.posLog (z1 / δ / ℓ) else 0)
        = ∑ ℓ ∈ Finset.Icc 1 ⌊z1 / (δ : ℝ)⌋₊,
            (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) * Real.posLog (z1 / δ / ℓ)
              else 0) := (Finset.sum_subset hsub hvan).symm
      _ = mCheckQ δ (z1 / δ) σ := by
          rw [mCheckQ]
          refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
          simp only [Finset.mem_Icc] at hℓ
          by_cases hcop : Nat.Coprime ℓ δ
          · rw [if_pos hcop, if_pos hcop]
            have hℓR : (0:ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.1
            have hle : (ℓ : ℝ) ≤ z1 / δ := by
              have h1 : (ℓ : ℝ) ≤ (⌊z1 / (δ : ℝ)⌋₊ : ℝ) := by exact_mod_cast hℓ.2
              exact le_trans h1 (Nat.floor_le (by positivity))
            have h1 : (1:ℝ) ≤ z1 / δ / ℓ := by
              rw [le_div_iff₀ hℓR, one_mul]
              exact hle
            rw [posLog_of_one_le h1]
          · rw [if_neg hcop, if_neg hcop]
  -- assemble
  rw [hfilter, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsplit : ∑ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ),
      (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) *
        (Real.posLog (z2 / δ / ℓ) - Real.posLog (z1 / δ / ℓ)) else 0)
      = (∑ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ),
          (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) * Real.posLog (z2 / δ / ℓ)
            else 0))
        - ∑ ℓ ∈ Finset.Icc 1 (⌊z2⌋₊ / δ),
          (if Nat.Coprime ℓ δ then (μ ℓ : ℝ) * (ℓ : ℝ) ^ (-σ) * Real.posLog (z1 / δ / ℓ)
            else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    by_cases hcop : Nat.Coprime ℓ δ
    · rw [if_pos hcop, if_pos hcop, if_pos hcop]
      ring
    · rw [if_neg hcop, if_neg hcop, if_neg hcop]
      ring
  rw [hsplit, hS2, hS1]
  ring

/-- **The `S_δ` bound**: for squarefree `δ ≤ z₂`, `σ ≥ 1`,
`|S_δ| ≤ δ^{-σ} (δ/φ(δ)) (22/3)(1 + (σ−1) log z₂) / log(z₂/z₁)`. -/
lemma abs_Ssum_le {z1 z2 : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2) {σ : ℝ} (hσ : 1 ≤ σ)
    {δ : ℕ} (hδsf : Squarefree δ) (hδz : (δ : ℝ) ≤ z2) :
    |Ssum z1 z2 σ δ| ≤ (δ : ℝ) ^ (-σ) * ((δ : ℝ) / (δ.totient : ℝ))
      * ((22 / 3) * (1 + (σ - 1) * Real.log z2)) / Real.log (z2 / z1) := by
  have hδ1 : 1 ≤ δ := Nat.one_le_iff_ne_zero.mpr hδsf.ne_zero
  have hδR : (1:ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ1
  have hδ0R : (0:ℝ) < (δ : ℝ) := by linarith
  have hz20 : (0:ℝ) < z2 := by linarith
  have hLpos : 0 < Real.log (z2 / z1) := Real.log_pos ((one_lt_div (by linarith)).mpr hz12)
  have hX2 : (1:ℝ) ≤ z2 / δ := (one_le_div hδ0R).mpr hδz
  have hε : (0:ℝ) ≤ σ - 1 := by linarith
  have hlogz2 : 0 ≤ Real.log z2 := Real.log_nonneg (by linarith)
  have hq1 : (1:ℝ) ≤ (δ : ℝ) / (δ.totient : ℝ) := one_le_div_totient' hδsf.ne_zero
  have hq0 : (0:ℝ) ≤ (δ : ℝ) / (δ.totient : ℝ) := by linarith
  have hbase : (0:ℝ) ≤ 1 + (σ - 1) * Real.log z2 := by nlinarith
  -- bound both `m̌`'s
  have hb2 : |mCheckQ δ (z2 / δ) σ|
      ≤ ((δ : ℝ) / (δ.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log z2) := by
    refine le_trans (abs_mCheckQ_le hδsf hX2 hσ) ?_
    have hmono : Real.log (z2 / δ) ≤ Real.log z2 :=
      Real.log_le_log (by positivity) (by
        rw [div_le_iff₀ hδ0R]
        nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left hmono hε]
  have hb1 : |mCheckQ δ (z1 / δ) σ|
      ≤ ((δ : ℝ) / (δ.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log z2) := by
    rcases lt_or_ge (z1 / (δ : ℝ)) 1 with hlt | hge
    · rw [mCheckQ_of_lt_one hlt, abs_zero]
      nlinarith
    · refine le_trans (abs_mCheckQ_le hδsf hge hσ) ?_
      have hmono : Real.log (z1 / δ) ≤ Real.log z2 :=
        Real.log_le_log (by linarith) (by
          rw [div_le_iff₀ hδ0R]
          nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left hmono hε]
  rw [Ssum_eq_mCheckQ hz1 hz12.le σ hδsf, abs_div, abs_of_pos hLpos]
  gcongr
  -- |μ δ * δ^{-σ} * (m₂ − m₁)| ≤ δ^{-σ} (δ/φ) (22/3)(1 + ε log z₂)
  have hpow0 : (0:ℝ) < (δ : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hδ0R _
  have hμ : |(μ δ : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hdiff : |mCheckQ δ (z2 / δ) σ - mCheckQ δ (z1 / δ) σ|
      ≤ 2 * (((δ : ℝ) / (δ.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log z2)) := by
    refine le_trans (abs_sub _ _) ?_
    linarith
  calc |(μ δ : ℝ) * (δ : ℝ) ^ (-σ) * (mCheckQ δ (z2 / δ) σ - mCheckQ δ (z1 / δ) σ)|
      = |(μ δ : ℝ)| * (δ : ℝ) ^ (-σ) * |mCheckQ δ (z2 / δ) σ - mCheckQ δ (z1 / δ) σ| := by
        rw [abs_mul, abs_mul, abs_of_pos hpow0]
    _ ≤ 1 * (δ : ℝ) ^ (-σ)
          * (2 * (((δ : ℝ) / (δ.totient : ℝ)) * (11 / 3) * (1 + (σ - 1) * Real.log z2))) := by
        have h1 : (0:ℝ) ≤ (δ : ℝ) ^ (-σ) := hpow0.le
        have hnn : (0:ℝ) ≤ |mCheckQ δ (z2 / δ) σ - mCheckQ δ (z1 / δ) σ| := abs_nonneg _
        have hstep := mul_le_mul hμ (le_refl ((δ : ℝ) ^ (-σ))) h1 (by norm_num : (0:ℝ) ≤ 1)
        exact mul_le_mul hstep hdiff hnn (by positivity)
    _ = (δ : ℝ) ^ (-σ) * ((δ : ℝ) / (δ.totient : ℝ))
          * ((22 / 3) * (1 + (σ - 1) * Real.log z2)) := by ring

/-- **The assembled diagonal bound** (items (i)–(iii) combined): for `σ > 1`,
`∑'_n n^{-σ} a(n)² ≤ ζ_R(σ) · (484/9)(1+(σ−1)log z₂)²/log²(z₂/z₁) · 8(1+log⌊z₂⌋₊)`. -/
lemma tsum_rpow_bvA_sq_le {z1 z2 : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2) {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (n : ℝ) ^ (-σ) * (bvA z1 z2 n) ^ 2
      ≤ zetaR σ * ((484 / 9) * (1 + (σ - 1) * Real.log z2) ^ 2 / Real.log (z2 / z1) ^ 2
          * (8 * (1 + Real.log (⌊z2⌋₊ : ℕ)))) := by
  have hz10 : (0:ℝ) < z1 := by linarith
  have hLpos : 0 < Real.log (z2 / z1) := Real.log_pos ((one_lt_div hz10).mpr hz12)
  rw [tsum_rpow_bvA_sq hz10 hz12 hσ, sum_lcm_eq_sum_phiSig_Ssum_sq z1 z2 σ]
  refine mul_le_mul_of_nonneg_left ?_ (zetaR_nonneg σ)
  -- pointwise: `φ_σ(δ) S_δ² ≤ μ²(δ) φ_σ(δ) δ^{-2σ} (δ/φ(δ))² · (22/3)²(1+εlog z₂)²/L²`
  have hpt : ∀ δ ∈ Finset.Icc 1 ⌊z2⌋₊, phiSig σ δ * (Ssum z1 z2 σ δ) ^ 2
      ≤ ((μ δ : ℝ) ^ 2 * phiSig σ δ * (δ : ℝ) ^ (-2 * σ) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2)
          * (((22 / 3) * (1 + (σ - 1) * Real.log z2)) ^ 2 / Real.log (z2 / z1) ^ 2) := by
    intro δ hδ
    simp only [Finset.mem_Icc] at hδ
    have hδ0R : (0:ℝ) < (δ : ℝ) := by exact_mod_cast hδ.1
    by_cases hsf : Squarefree δ
    · have hδz : (δ : ℝ) ≤ z2 := by
        have h1 : (δ : ℝ) ≤ (⌊z2⌋₊ : ℝ) := by exact_mod_cast hδ.2
        exact le_trans h1 (Nat.floor_le (by linarith))
      have hb := abs_Ssum_le hz1 hz12 hσ.le hsf hδz
      have hφ : 0 ≤ phiSig σ δ := phiSig_nonneg (by linarith) δ
      have hμ1 : (μ δ : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
      have hrhs0 : (0:ℝ) ≤ (δ : ℝ) ^ (-σ) * ((δ : ℝ) / (δ.totient : ℝ))
          * ((22 / 3) * (1 + (σ - 1) * Real.log z2)) / Real.log (z2 / z1) :=
        le_trans (abs_nonneg _) hb
      have hsq : (Ssum z1 z2 σ δ) ^ 2
          ≤ ((δ : ℝ) ^ (-σ) * ((δ : ℝ) / (δ.totient : ℝ))
              * ((22 / 3) * (1 + (σ - 1) * Real.log z2)) / Real.log (z2 / z1)) ^ 2 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (Ssum z1 z2 σ δ)]
      have hexpand : ((δ : ℝ) ^ (-σ) * ((δ : ℝ) / (δ.totient : ℝ))
            * ((22 / 3) * (1 + (σ - 1) * Real.log z2)) / Real.log (z2 / z1)) ^ 2
          = ((δ : ℝ) ^ (-2 * σ) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2)
              * (((22 / 3) * (1 + (σ - 1) * Real.log z2)) ^ 2 / Real.log (z2 / z1) ^ 2) := by
        have hpow : ((δ : ℝ) ^ (-σ)) ^ 2 = (δ : ℝ) ^ (-2 * σ) := by
          rw [sq, ← Real.rpow_add hδ0R]
          congr 1
          ring
        rw [div_pow, mul_pow, mul_pow, hpow]
        ring
      calc phiSig σ δ * (Ssum z1 z2 σ δ) ^ 2
          ≤ phiSig σ δ * (((δ : ℝ) ^ (-2 * σ) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2)
              * (((22 / 3) * (1 + (σ - 1) * Real.log z2)) ^ 2 / Real.log (z2 / z1) ^ 2)) := by
            rw [← hexpand]
            exact mul_le_mul_of_nonneg_left hsq hφ
        _ = ((μ δ : ℝ) ^ 2 * phiSig σ δ * (δ : ℝ) ^ (-2 * σ)
              * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2)
              * (((22 / 3) * (1 + (σ - 1) * Real.log z2)) ^ 2 / Real.log (z2 / z1) ^ 2) := by
            rw [hμ1]
            ring
    · rw [Ssum_eq_zero_of_not_squarefree hsf,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      norm_num
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.sum_mul]
  have hW := W_bound hσ.le ⌊z2⌋₊
  have hc : (0:ℝ) ≤ ((22 / 3) * (1 + (σ - 1) * Real.log z2)) ^ 2 / Real.log (z2 / z1) ^ 2 := by
    positivity
  calc (∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
        (μ δ : ℝ) ^ 2 * phiSig σ δ * (δ : ℝ) ^ (-2 * σ) * ((δ : ℝ) / (δ.totient : ℝ)) ^ 2)
        * (((22 / 3) * (1 + (σ - 1) * Real.log z2)) ^ 2 / Real.log (z2 / z1) ^ 2)
      ≤ (8 * (1 + Real.log (⌊z2⌋₊ : ℕ)))
        * (((22 / 3) * (1 + (σ - 1) * Real.log z2)) ^ 2 / Real.log (z2 / z1) ^ 2) :=
        mul_le_mul_of_nonneg_right hW hc
    _ = (484 / 9) * (1 + (σ - 1) * Real.log z2) ^ 2 / Real.log (z2 / z1) ^ 2
        * (8 * (1 + Real.log (⌊z2⌋₊ : ℕ))) := by ring

/-! ### Item (iv), Rankin step: `∑_{n ≤ Y} a(n)²/n ≤ e · ∑'_n n^{-σ} a(n)²`
at `σ = 1 + 1/log Y` (using `n ≤ Y ⟹ n^{-1} ≤ Y^{σ-1} n^{-σ}` and `Y^{1/log Y} = e`). -/

lemma sum_bvA_sq_div_le_tsum {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) {Y : ℝ}
    (hY : 1 < Y) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (bvA z1 z2 n) ^ 2 / n
      ≤ Real.exp 1 * ∑' n : ℕ, (n : ℝ) ^ (-(1 + 1 / Real.log Y)) * (bvA z1 z2 n) ^ 2 := by
  have hlY : 0 < Real.log Y := Real.log_pos hY
  have hσ : 1 < 1 + 1 / Real.log Y := by
    have : 0 < 1 / Real.log Y := by positivity
    linarith
  have hpt : ∀ n ∈ Finset.Icc 1 ⌊Y⌋₊, (bvA z1 z2 n) ^ 2 / n
      ≤ Real.exp 1 * ((n : ℝ) ^ (-(1 + 1 / Real.log Y)) * (bvA z1 z2 n) ^ 2) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have hnY : (n : ℝ) ≤ Y := by
      have h1 : (n : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn.2
      exact le_trans h1 (Nat.floor_le (by linarith))
    have hkey : 1 / (n : ℝ) ≤ Real.exp 1 * (n : ℝ) ^ (-(1 + 1 / Real.log Y)) := by
      have h1 : (n : ℝ) ^ (1 / Real.log Y) ≤ Y ^ (1 / Real.log Y) :=
        Real.rpow_le_rpow hn0.le hnY (by positivity)
      have h2 : Y ^ (1 / Real.log Y : ℝ) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < Y)]
        congr 1
        field_simp
      have h3 : (n : ℝ) ^ (1 / Real.log Y) * (n : ℝ) ^ (-(1 + 1 / Real.log Y))
          = 1 / (n : ℝ) := by
        rw [← Real.rpow_add hn0]
        have : 1 / Real.log Y + -(1 + 1 / Real.log Y) = -1 := by ring
        rw [this, Real.rpow_neg_one, one_div]
      have hp0 : (0:ℝ) ≤ (n : ℝ) ^ (-(1 + 1 / Real.log Y)) :=
        (Real.rpow_pos_of_pos hn0 _).le
      calc 1 / (n : ℝ)
          = (n : ℝ) ^ (1 / Real.log Y) * (n : ℝ) ^ (-(1 + 1 / Real.log Y)) := h3.symm
        _ ≤ Y ^ (1 / Real.log Y) * (n : ℝ) ^ (-(1 + 1 / Real.log Y)) :=
            mul_le_mul_of_nonneg_right h1 hp0
        _ = Real.exp 1 * (n : ℝ) ^ (-(1 + 1 / Real.log Y)) := by rw [h2]
    have hsq : (0:ℝ) ≤ (bvA z1 z2 n) ^ 2 := sq_nonneg _
    calc (bvA z1 z2 n) ^ 2 / n = (1 / (n : ℝ)) * (bvA z1 z2 n) ^ 2 := by ring
      _ ≤ (Real.exp 1 * (n : ℝ) ^ (-(1 + 1 / Real.log Y))) * (bvA z1 z2 n) ^ 2 :=
          mul_le_mul_of_nonneg_right hkey hsq
      _ = Real.exp 1 * ((n : ℝ) ^ (-(1 + 1 / Real.log Y)) * (bvA z1 z2 n) ^ 2) := by ring
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
  refine Summable.sum_le_tsum _ (fun n _ => ?_) (summable_rpow_bvA_sq hz1 hz12 hσ)
  positivity

end Diagonalisation

/-! ### The unconditional I4*: `hharm` discharged at the crude constant -/

section UncondStar

open Detector

set_option linter.unusedVariables false

/-- The endgame numerals: with `62·ℓ ≥ log 100 ≥ 6 log 2 > 4.1588` and `L ≥ 62ℓ`,
`e·(1+L)·(484/9)(125/62)²/ℓ²·8(1+63ℓ) ≤ 5·10⁵·L/ℓ`.  (The assembled constant is
`≈ 4.6·10⁵`; the frozen ceiling is `5·10⁵`.) -/
private lemma endgame_numeric {l L : ℝ} (hl : 6 * Real.log 2 ≤ 62 * l)
    (hL : 62 * l ≤ L) :
    Real.exp 1 * ((1 + L) * ((484 / 9) * (125 / 62) ^ 2 / l ^ 2 * (8 * (1 + 63 * l))))
      ≤ 500000 * L / l := by
  have hlog2 := Real.log_two_gt_d9
  have he := Real.exp_one_lt_d9
  have hl4 : (4.1588 : ℝ) ≤ 62 * l := by nlinarith
  have hl0 : (0:ℝ) < l := by nlinarith
  have hL4 : (4.1588 : ℝ) ≤ L := le_trans hl4 hL
  have hL0 : (0:ℝ) < L := by linarith
  have h1 : 1 + L ≤ 1.2405 * L := by nlinarith
  have h2 : 1 + 63 * l ≤ (77.911 : ℝ) * l := by nlinarith
  have hform : Real.exp 1 * ((1 + L) * ((484 / 9) * (125 / 62) ^ 2 / l ^ 2
        * (8 * (1 + 63 * l))))
      = (Real.exp 1 * (1 + L) * ((484 / 9) * (125 / 62) ^ 2) * (8 * (1 + 63 * l))) / l ^ 2 := by
    ring
  have hform2 : (500000 : ℝ) * L / l = (500000 * L * l) / l ^ 2 := by
    rw [sq]
    field_simp
  rw [hform, hform2]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  -- polynomial core: `e(1+L)·k·8(1+63l) ≤ 500000·L·l`
  have hA : Real.exp 1 * (1 + L) ≤ 2.7182818286 * (1.2405 * L) :=
    mul_le_mul he.le h1 (by linarith) (by norm_num)
  have hB : (8:ℝ) * (1 + 63 * l) ≤ 8 * (77.911 * l) := by nlinarith
  have hAk : Real.exp 1 * (1 + L) * ((484 / 9) * (125 / 62) ^ 2)
      ≤ 2.7182818286 * (1.2405 * L) * ((484 / 9) * (125 / 62) ^ 2) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have hfull : Real.exp 1 * (1 + L) * ((484 / 9) * (125 / 62) ^ 2) * (8 * (1 + 63 * l))
      ≤ 2.7182818286 * (1.2405 * L) * ((484 / 9) * (125 / 62) ^ 2) * (8 * (77.911 * l)) := by
    refine mul_le_mul hAk hB (by nlinarith) ?_
    have hE : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    positivity
  refine le_trans hfull ?_
  have hcoeff : (2.7182818286 : ℝ) * 1.2405 * ((484 / 9) * (125 / 62) ^ 2) * (8 * 77.911)
      ≤ 500000 := by norm_num
  calc (2.7182818286 : ℝ) * (1.2405 * L) * ((484 / 9) * (125 / 62) ^ 2) * (8 * (77.911 * l))
      = (2.7182818286 * 1.2405 * ((484 / 9) * (125 / 62) ^ 2) * (8 * 77.911)) * (L * l) := by
        ring
    _ ≤ 500000 * (L * l) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = 500000 * L * l := by ring

/-- **The `hharm` discharge (UNCONDITIONAL harmonic bound, crude constant).**
At the campaign cuts `z₁ = D^{31/50}`, `z₂ = D^{63/100}`, for any `Y ≥ z₁`:
`∑_{n ≤ Y} a(n)²/n ≤ 5·10⁵ · log Y / ℓ`.  No hypotheses beyond the cut sizes. -/
theorem bvHarm_uncond {D Y : ℝ} (hD : 1 < D) (hz1 : 100 ≤ z1par D) (hY : z1par D ≤ Y) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (bvA (z1par D) (z2par D) n) ^ 2 / n
      ≤ 500000 * Real.log Y / ellpar D := by
  have hD0 : (0:ℝ) < D := by linarith
  have hl0 : 0 < ellpar D := ellpar_pos hD
  have hz12 : z1par D < z2par D := by
    rw [z1par, z2par]
    exact Real.rpow_lt_rpow_of_exponent_lt hD (by norm_num)
  have hz11 : (1:ℝ) ≤ z1par D := by linarith
  have hY1 : (1:ℝ) < Y := by linarith
  have hlY : 0 < Real.log Y := Real.log_pos hY1
  -- logs of the cuts
  have hlogz1 : Real.log (z1par D) = 62 * ellpar D := by
    rw [z1par, Real.log_rpow hD0, ellpar]
    ring
  have hlogz2 : Real.log (z2par D) = 63 * ellpar D := by
    rw [z2par, Real.log_rpow hD0, ellpar]
    ring
  have hlogwin : Real.log (z2par D / z1par D) = ellpar D := log_z2par_div_z1par hD0
  have hLYlow : 62 * ellpar D ≤ Real.log Y := by
    rw [← hlogz1]
    exact Real.log_le_log (by linarith) hY
  have hl62 : 6 * Real.log 2 ≤ 62 * ellpar D := by
    rw [← hlogz1]
    calc 6 * Real.log 2 = Real.log (2 ^ (6 : ℕ)) := by
          rw [Real.log_pow]
          push_cast
          ring
      _ ≤ Real.log (z1par D) := by
          refine Real.log_le_log (by norm_num) ?_
          norm_num
          linarith
  -- the σ of the Rankin step
  have hσ1 : 1 < 1 + 1 / Real.log Y := by
    have : 0 < 1 / Real.log Y := by positivity
    linarith
  -- ζ at the Rankin point
  have hζ : zetaR (1 + 1 / Real.log Y) ≤ 1 + Real.log Y := by
    refine le_trans (zetaR_le hσ1) ?_
    have h1 : 1 + 1 / Real.log Y - 1 = 1 / Real.log Y := by ring
    rw [h1, one_div_one_div]
  -- the ε log z₂ ≤ 63/62 bound
  have hεb : (1 + 1 / Real.log Y - 1) * Real.log (z2par D) ≤ 63 / 62 := by
    have h1 : 1 + 1 / Real.log Y - 1 = 1 / Real.log Y := by ring
    rw [h1, hlogz2, div_mul_eq_mul_div, div_le_div_iff₀ hlY (by norm_num : (0:ℝ) < 62)]
    nlinarith [hLYlow, hl0]
  have hεnn : 0 ≤ (1 + 1 / Real.log Y - 1) * Real.log (z2par D) := by
    have h1 : 1 + 1 / Real.log Y - 1 = 1 / Real.log Y := by ring
    rw [h1, hlogz2]
    positivity
  have hfac : (1 + (1 + 1 / Real.log Y - 1) * Real.log (z2par D)) ^ 2 ≤ (125 / 62) ^ 2 := by
    have h0 : (0:ℝ) ≤ 1 + (1 + 1 / Real.log Y - 1) * Real.log (z2par D) := by linarith
    have h1 : 1 + (1 + 1 / Real.log Y - 1) * Real.log (z2par D) ≤ 125 / 62 := by
      linarith [hεb]
    nlinarith
  -- the floor log
  have hfl1 : (1:ℕ) ≤ ⌊z2par D⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    linarith
  have hfloorlog : Real.log ((⌊z2par D⌋₊ : ℕ) : ℝ) ≤ 63 * ellpar D := by
    rw [← hlogz2]
    refine Real.log_le_log ?_ (Nat.floor_le (by linarith))
    exact_mod_cast hfl1
  have hfloornn : (0:ℝ) ≤ Real.log ((⌊z2par D⌋₊ : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hfl1
  -- chain the three delivered bounds
  have hstep1 := sum_bvA_sq_div_le_tsum (by linarith : (0:ℝ) < z1par D) hz12 hY1
  have hstep2 := tsum_rpow_bvA_sq_le hz11 hz12 hσ1 (z2 := z2par D)
  rw [hlogwin] at hstep2
  have hstep3 : zetaR (1 + 1 / Real.log Y)
        * ((484 / 9) * (1 + (1 + 1 / Real.log Y - 1) * Real.log (z2par D)) ^ 2 / ellpar D ^ 2
          * (8 * (1 + Real.log ((⌊z2par D⌋₊ : ℕ) : ℝ))))
      ≤ (1 + Real.log Y)
        * ((484 / 9) * (125 / 62) ^ 2 / ellpar D ^ 2 * (8 * (1 + 63 * ellpar D))) := by
    have hA : (484 / 9) * (1 + (1 + 1 / Real.log Y - 1) * Real.log (z2par D)) ^ 2 / ellpar D ^ 2
        ≤ (484 / 9) * (125 / 62) ^ 2 / ellpar D ^ 2 := by
      gcongr
    have hB : (8:ℝ) * (1 + Real.log ((⌊z2par D⌋₊ : ℕ) : ℝ)) ≤ 8 * (1 + 63 * ellpar D) := by
      nlinarith [hfloorlog]
    have hB0 : (0:ℝ) ≤ 8 * (1 + Real.log ((⌊z2par D⌋₊ : ℕ) : ℝ)) := by nlinarith
    have hA0 : (0:ℝ) ≤ (484 / 9) * (125 / 62) ^ 2 / ellpar D ^ 2 := by positivity
    have hAB := mul_le_mul hA hB hB0 hA0
    refine mul_le_mul hζ hAB ?_ (by linarith)
    have hApos : (0:ℝ) ≤ (484 / 9)
        * (1 + (1 + 1 / Real.log Y - 1) * Real.log (z2par D)) ^ 2 / ellpar D ^ 2 := by
      positivity
    exact mul_nonneg hApos hB0
  calc ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (bvA (z1par D) (z2par D) n) ^ 2 / n
      ≤ Real.exp 1 * ∑' n : ℕ, (n : ℝ) ^ (-(1 + 1 / Real.log Y))
          * (bvA (z1par D) (z2par D) n) ^ 2 := hstep1
    _ ≤ Real.exp 1 * ((1 + Real.log Y)
          * ((484 / 9) * (125 / 62) ^ 2 / ellpar D ^ 2 * (8 * (1 + 63 * ellpar D)))) := by
        refine mul_le_mul_of_nonneg_left (le_trans hstep2 hstep3) (Real.exp_pos 1).le
    _ ≤ 500000 * Real.log Y / ellpar D := endgame_numeric hl62 hLYlow

/-- **UNCONDITIONAL I4\*** (the frozen interface at the crude-route constant, ceiling
`5·10⁵`; blueprint §2, re-frozen).  At the campaign's cuts `z₁ = D^{31/50}`,
`z₂ = D^{63/100}`, for `Y ≥ z₁` and `α ∈ [1/2, 1]`:
`∑_{n ≤ Y} n^{1−2α} a(n)² ≤ 5·10⁵ · Y^{2−2α} · log Y / ℓ`.
This is `bvL2_star` with `hharm` DISCHARGED and `927` replaced by the crude-route
`500000`. -/
theorem bvL2_star_uncond {D Y α : ℝ} (hD : 1 < D) (hz1 : 100 ≤ z1par D)
    (hY : z1par D ≤ Y) (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1) :
    ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℝ) ^ (1 - 2 * α) * (bvA (z1par D) (z2par D) n) ^ 2
      ≤ 500000 * Y ^ (2 - 2 * α) * Real.log Y / ellpar D := by
  have hY1 : (1:ℝ) ≤ Y := by linarith
  have hpow : (0:ℝ) ≤ Y ^ (2 - 2 * α) := Real.rpow_nonneg (by linarith) _
  have hstep : ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℝ) ^ (1 - 2 * α)
        * (bvA (z1par D) (z2par D) n) ^ 2
      ≤ Y ^ (2 - 2 * α) * (500000 * Real.log Y / ellpar D) :=
    le_trans (rankin_alpha hY1 hα1 _)
      (mul_le_mul_of_nonneg_left (bvHarm_uncond hD hz1 hY) hpow)
  refine le_trans hstep (le_of_eq ?_)
  ring

end UncondStar
