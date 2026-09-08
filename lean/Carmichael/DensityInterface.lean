/-
Route Z: the two zero-density interfaces consumed by the T2.1 assembly
(routez/Z0a-ledger.md §7, the frozen Z6d and Z6-logged forms).

`LogFreeDensity` is the Z6d form (log-free, coefficient 9/2 on σ ∈ [9/10, 1],
t-exponent c₀' ∈ [1, 2]).  `LoggedDensity` is the Z6-logged form with a UNIFORM
profile `P`: any `P ≤ 7/2` satisfies the ledger's fold pin
`c₀·P·(11/50) ≤ (5/4)·(7/2)·(11/50) = 0.9625 < 1` at the rigid ceiling
`c₀ ≤ 5/4` (routez/Z0a-ledger.md §3.2: "any coefficient function P(σ) ≤ 9/2
with c₀·sup P(σ)(1−σ) < 1 works identically").  The delivered profile is
`P = 151/50` (routez/Z6-logged.md).

Zero counts are `Carmichael.zeroCountBox χ σ t` (with multiplicity, box
`[σ,1] × [−t,t]`, `s = 1` excluded).
-/
import Carmichael.ZeroCount

set_option autoImplicit false

namespace Carmichael

/-- Z0a §7, Z6d form: log-free zero density at coefficient `9/2`. -/
def LogFreeDensity : Prop :=
  ∃ γ₂ c₀' : ℝ, 1 ≤ γ₂ ∧ 1 ≤ c₀' ∧ c₀' ≤ 2 ∧
    ∀ (d : ℕ) [NeZero d] (t σ : ℝ), 2 ≤ t → 9/10 ≤ σ → σ ≤ 1 →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
        ≤ γ₂ * ((d : ℝ) * t ^ c₀') ^ ((9/2 : ℝ) * (1 - σ))

/-- Z0a §7, Z6-logged form with a uniform profile `P ≤ 7/2`: logged zero
density on `σ ∈ [39/50, 1]`, `t`-exponent `c₀ ∈ [1, 5/4]`, log power `K`. -/
def LoggedDensity : Prop :=
  ∃ (CH P c₀ : ℝ) (K : ℕ), 1 ≤ CH ∧ 0 ≤ P ∧ P ≤ 7/2 ∧ 1 ≤ c₀ ∧ c₀ ≤ 5/4 ∧
    ∀ (d : ℕ) [NeZero d] (t σ : ℝ), 2 ≤ t → 39/50 ≤ σ → σ ≤ 1 →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
        ≤ CH * ((d : ℝ) * t ^ c₀) ^ (P * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ K

end Carmichael
