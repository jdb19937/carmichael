/-
Route T, sortie T8a: the overhead toolkit for the final assembly.

Pure real analysis and `ℕ` arithmetic, no machine code. Three services for
`Carmichael/TM/Main.lean`:

* **Input length.** Mathlib's `encodeNat n` has exactly `⌊log₂ n⌋ + 1` bits
  for `n ≥ 1` (and none for `n = 0`), so "input length `≥ N`" means
  `n ≥ 2^(N-1)` and "input length `= N`" means `n < 2^N`. This is how
  eventual facts `∀ᶠ n` become facts `∀ N ≥ N₀` about the input length.

* **The time function.** `exists_timeFun`: per-input step counts that are
  eventually `≤ exp(C ℓ₂ ℓ₃)` are dominated by a function of the input
  length `N` that is eventually `≤ exp(C · log N · log log N)`, with the SAME
  constant `C`. The function is `⌊exp(C log N log log N)⌋₊` for `N ≥ N₀` and
  the finite maximum over all inputs of length `N` below; the floor (not the
  ceiling) is what makes the constant exact: `g n ≤ ⌊X⌋₊` needs only
  `g n ≤ X` (`Nat.le_floor`), and `⌊X⌋₊ ≤ X` is free.

* **The bound family.** `ExpB n c a` says `a ≤ exp(c ℓ₂ ℓ₃)`; it is closed
  under products (constants add), sums (`+1`), powers (constants multiply),
  bit lengths, the machine budget `B`, and dominated by constants. The window
  `InWindow` supplies the atoms (`window_base`): `z, w, y, T, 2^T ≤ exp(M)`,
  `z^T ≤ exp(15 M)`, and the bit lengths of `n` and the threshold
  `16 (log n)^{1.2}` are `≤ exp(M)` (`M := ℓ₂ ℓ₃`). Values of `n` and of
  `m ≤ n · x^{|P|}` are NOT exp-bounded — only their bit lengths are, and
  `bits_mul_le`/`bits_pow_le` carry those.
-/
import Carmichael.ScalesTM
import Carmichael.TM.Cost

set_option autoImplicit false

namespace Carmichael

open Filter Computability

/-! ### 1. Input length -/

/-- `encodePosNum p` has exactly `⌊log₂ p⌋ + 1` bits. -/
theorem encodePosNum_length (p : PosNum) :
    (encodePosNum p).length = Nat.log 2 (p : ℕ) + 1 := by
  induction p with
  | one => simp [encodePosNum]
  | bit0 p ih =>
    have hp : 1 ≤ (p : ℕ) := PosNum.one_le_cast p
    rw [encodePosNum, List.length_cons, PosNum.cast_bit0,
      Nat.log_of_one_lt_of_le one_lt_two (by omega : 2 ≤ (p : ℕ) + p),
      show ((p : ℕ) + p) / 2 = p by omega]
    omega
  | bit1 p ih =>
    have hp : 1 ≤ (p : ℕ) := PosNum.one_le_cast p
    rw [encodePosNum, List.length_cons, PosNum.cast_bit1,
      Nat.log_of_one_lt_of_le one_lt_two (by omega : 2 ≤ (p : ℕ) + p + 1),
      show ((p : ℕ) + p + 1) / 2 = p by omega]
    omega

/-- The input length of `n ≥ 1` under Mathlib's `encodeNat`: `⌊log₂ n⌋ + 1`. -/
theorem encodeNat_length (n : ℕ) (hn : 1 ≤ n) :
    (Computability.encodeNat n).length = Nat.log 2 n + 1 := by
  have h := Num.to_of_nat n
  unfold Computability.encodeNat
  rcases hn' : (n : Num) with _ | p
  · rw [hn'] at h
    simp at h
    omega
  · rw [hn', Num.cast_pos] at h
    rw [encodeNum, encodePosNum_length, h]

/-- `encodeNat 0` is the empty list. -/
theorem encodeNat_length_zero : (Computability.encodeNat 0).length = 0 := rfl

/-- The input length is at most `⌊log₂ n⌋ + 1` for every `n`. -/
theorem encodeNat_length_le' (n : ℕ) :
    (Computability.encodeNat n).length ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [encodeNat_length_zero]; omega
  · rw [encodeNat_length n hn]

/-- Every `n` is below `2 ^ (input length of n)`. -/
theorem lt_two_pow_encodeNat_length (n : ℕ) : n < 2 ^ (Computability.encodeNat n).length := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [encodeNat_length_zero]; norm_num
  · rw [encodeNat_length n hn]
    exact Nat.lt_pow_succ_log_self one_lt_two n

/-- Input length `≥ N ≥ 1` forces `n ≥ 2 ^ (N - 1)`: this transfers eventual
facts about `n` to facts about the input length. -/
theorem le_of_encodeNat_length (n N : ℕ) (h : N ≤ (Computability.encodeNat n).length)
    (hN : 1 ≤ N) : 2 ^ (N - 1) ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [encodeNat_length_zero] at h; omega
  · rw [encodeNat_length n hn] at h
    calc 2 ^ (N - 1) ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)

/-- Input length `≥ n₀ + 1` forces `n ≥ n₀` (the form `exists_timeFun` uses). -/
theorem le_of_encodeNat_length_succ (n n₀ : ℕ)
    (h : n₀ + 1 ≤ (Computability.encodeNat n).length) : n₀ ≤ n := by
  have := le_of_encodeNat_length n (n₀ + 1) h (by omega)
  have h2 : n₀ < 2 ^ n₀ := Nat.lt_two_pow_self
  simp only [Nat.add_sub_cancel] at this
  omega

/-! ### Bit lengths of products and powers -/

/-- Bit length of a product: `bits (a b) ≤ bits a + bits b`
(`bits a = ⌊log₂ a⌋ + 1`). -/
theorem bits_mul_le (a b : ℕ) :
    Nat.log 2 (a * b) + 1 ≤ (Nat.log 2 a + 1) + (Nat.log 2 b + 1) := by
  rcases Nat.eq_zero_or_pos (a * b) with h0 | hpos
  · rw [h0, Nat.log_zero_right]; omega
  · have ha : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self one_lt_two a
    have hb : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self one_lt_two b
    have hab : a * b < 2 ^ ((Nat.log 2 a + 1) + (Nat.log 2 b + 1)) := by
      rw [pow_add]
      exact Nat.mul_lt_mul'' ha hb
    have := Nat.log_lt_of_lt_pow (by omega) hab
    omega

/-- Bit length of a power: `bits (a ^ k) ≤ k · bits a + 1`. -/
theorem bits_pow_le (a k : ℕ) :
    Nat.log 2 (a ^ k) + 1 ≤ k * (Nat.log 2 a + 1) + 1 := by
  rcases Nat.eq_zero_or_pos (a ^ k) with h0 | hpos
  · rw [h0]; simp
  · have ha : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self one_lt_two a
    have hak : a ^ k ≤ (2 ^ (Nat.log 2 a + 1)) ^ k := Nat.pow_le_pow_left ha.le k
    rw [← pow_mul] at hak
    have hlog : Nat.log 2 (a ^ k) ≤ (Nat.log 2 a + 1) * k := by
      have := Nat.log_mono_right (b := 2) hak
      rwa [Nat.log_pow one_lt_two] at this
    nlinarith [hlog]

/-! ### 3. The bound family `ExpB` -/

/-- `a ≤ exp(c · ℓ₂ n · ℓ₃ n)`. The exponent is written `c * ell2 n * ell3 n`
(left-associated) to match `search_successW`'s `100 * ell2 n * ell3 n`. -/
def ExpB (n : ℕ) (c : ℝ) (a : ℝ) : Prop := a ≤ Real.exp (c * ell2 n * ell3 n)

theorem ExpB.def' {n : ℕ} {c a : ℝ} :
    ExpB n c a ↔ a ≤ Real.exp (c * (ell2 n * ell3 n)) := by
  unfold ExpB; rw [mul_assoc]

theorem ExpB.of_le {n : ℕ} {c a b : ℝ} (h : a ≤ b) (hb : ExpB n c b) : ExpB n c a :=
  h.trans hb

/-- Cast form of `of_le`: an integer bound transfers. -/
theorem ExpB.of_nat_le {n : ℕ} {c : ℝ} {a b : ℕ} (h : a ≤ b) (hb : ExpB n c (b : ℝ)) :
    ExpB n c (a : ℝ) :=
  ExpB.of_le (by exact_mod_cast h) hb

theorem ExpB.mono {n : ℕ} {c c' a : ℝ} (hM : 0 ≤ ell2 n * ell3 n) (hc : c ≤ c')
    (h : ExpB n c a) : ExpB n c' a := by
  rw [ExpB.def'] at h ⊢
  exact h.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc hM))

/-- The exponential itself. -/
theorem ExpB.exp {n : ℕ} (c : ℝ) : ExpB n c (Real.exp (c * ell2 n * ell3 n)) := le_rfl

/-- Products: constants add. Only the second factor needs to be nonnegative. -/
theorem ExpB.mul {n : ℕ} {c₁ c₂ a b : ℝ} (hb : 0 ≤ b) (h1 : ExpB n c₁ a) (h2 : ExpB n c₂ b) :
    ExpB n (c₁ + c₂) (a * b) := by
  rw [ExpB.def'] at h1 h2 ⊢
  rw [add_mul, Real.exp_add]
  exact mul_le_mul h1 h2 hb (Real.exp_pos _).le

/-- `ExpB.mul`, the name the final conversion refers to. -/
theorem ExpB.exp_mul {n : ℕ} {c₁ c₂ a b : ℝ} (hb : 0 ≤ b) (h1 : ExpB n c₁ a)
    (h2 : ExpB n c₂ b) : ExpB n (c₁ + c₂) (a * b) :=
  ExpB.mul hb h1 h2

/-- Products of naturals: no positivity side condition. -/
theorem ExpB.mul_nat {n : ℕ} {c₁ c₂ : ℝ} {a b : ℕ} (h1 : ExpB n c₁ (a : ℝ))
    (h2 : ExpB n c₂ (b : ℝ)) : ExpB n (c₁ + c₂) ((a * b : ℕ) : ℝ) := by
  push_cast
  exact ExpB.mul (Nat.cast_nonneg b) h1 h2

/-- Powers: constants multiply. -/
theorem ExpB.pow {n : ℕ} {c a : ℝ} (ha : 0 ≤ a) (h : ExpB n c a) (k : ℕ) :
    ExpB n (k * c) (a ^ k) := by
  rw [ExpB.def'] at h ⊢
  calc a ^ k ≤ Real.exp (c * (ell2 n * ell3 n)) ^ k := pow_le_pow_left₀ ha h k
    _ = Real.exp ((k : ℝ) * (c * (ell2 n * ell3 n))) := (Real.exp_nat_mul _ k).symm
    _ = Real.exp ((k : ℝ) * c * (ell2 n * ell3 n)) := by rw [mul_assoc]

theorem ExpB.pow_nat {n : ℕ} {c : ℝ} {a : ℕ} (h : ExpB n c (a : ℝ)) (k : ℕ) :
    ExpB n (k * c) ((a ^ k : ℕ) : ℝ) := by
  push_cast
  exact ExpB.pow (Nat.cast_nonneg a) h k

/-- `2 ≤ exp M` once `M ≥ 1`. -/
theorem two_le_exp_of_one_le {M : ℝ} (hM : 1 ≤ M) : (2 : ℝ) ≤ Real.exp M := by
  have h := Real.add_one_le_exp M
  linarith only [h, hM]

/-- Sums: `a + b ≤ 2 exp(max c₁ c₂ · M) ≤ exp((max c₁ c₂ + 1) M)`. -/
theorem ExpB.add {n : ℕ} {c₁ c₂ a b : ℝ} (hM : 1 ≤ ell2 n * ell3 n) (h1 : ExpB n c₁ a)
    (h2 : ExpB n c₂ b) : ExpB n (max c₁ c₂ + 1) (a + b) := by
  have hM0 : 0 ≤ ell2 n * ell3 n := by linarith only [hM]
  have h1' := ExpB.mono hM0 (le_max_left c₁ c₂) h1
  have h2' := ExpB.mono hM0 (le_max_right c₁ c₂) h2
  rw [ExpB.def'] at h1' h2' ⊢
  rw [add_mul, one_mul, Real.exp_add]
  have h2e := two_le_exp_of_one_le hM
  have hpos := (Real.exp_pos (max c₁ c₂ * (ell2 n * ell3 n))).le
  nlinarith only [h1', h2', h2e, hpos]

/-- Sums with nonnegative constants: `a + b ≤ exp((c₁ + c₂ + 1) M)`. Additive
constants, no `max` — the convenient form for chaining. -/
theorem ExpB.add' {n : ℕ} {c₁ c₂ a b : ℝ} (hM : 1 ≤ ell2 n * ell3 n) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (h1 : ExpB n c₁ a) (h2 : ExpB n c₂ b) : ExpB n (c₁ + c₂ + 1) (a + b) := by
  have hM0 : 0 ≤ ell2 n * ell3 n := by linarith only [hM]
  have h := ExpB.add hM h1 h2
  exact ExpB.mono hM0 (by
    have := max_le (by linarith only [hc₂] : c₁ ≤ c₁ + c₂) (by linarith only [hc₁] : c₂ ≤ c₁ + c₂)
    linarith only [this]) h

/-- Sums with the same constant. -/
theorem ExpB.add_same {n : ℕ} {c a b : ℝ} (hM : 1 ≤ ell2 n * ell3 n) (h1 : ExpB n c a)
    (h2 : ExpB n c b) : ExpB n (c + 1) (a + b) := by
  have := ExpB.add hM h1 h2
  rwa [max_self] at this

theorem ExpB.add_nat {n : ℕ} {c₁ c₂ : ℝ} {a b : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (h1 : ExpB n c₁ (a : ℝ)) (h2 : ExpB n c₂ (b : ℝ)) :
    ExpB n (c₁ + c₂ + 1) ((a + b : ℕ) : ℝ) := by
  push_cast
  exact ExpB.add' hM hc₁ hc₂ h1 h2

/-- Constants: `a ≤ k` with `k ≥ 0` gives `ExpB n k a` (`k ≤ exp k ≤ exp(k M)`). -/
theorem ExpB.const_le {n : ℕ} {a k : ℝ} (hM : 1 ≤ ell2 n * ell3 n) (hk : 0 ≤ k) (ha : a ≤ k) :
    ExpB n k a := by
  rw [ExpB.def']
  have h1 : k ≤ Real.exp k := by linarith only [Real.add_one_le_exp k]
  have h2 : Real.exp k ≤ Real.exp (k * (ell2 n * ell3 n)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hk, hM])
  linarith only [ha, h1, h2]

/-- A natural constant `k` is `ExpB n k`. -/
theorem ExpB.natCast {n : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (k : ℕ) : ExpB n k (k : ℝ) :=
  ExpB.const_le hM (Nat.cast_nonneg k) le_rfl

/-- `1 ≤ exp(c M)` for `c ≥ 0`. -/
theorem ExpB.one {n : ℕ} {c : ℝ} (hM : 0 ≤ ell2 n * ell3 n) (hc : 0 ≤ c) : ExpB n c 1 := by
  rw [ExpB.def']
  have := Real.add_one_le_exp (c * (ell2 n * ell3 n))
  nlinarith only [this, hM, hc]

theorem ExpB.zero {n : ℕ} (c : ℝ) : ExpB n c 0 := (Real.exp_pos _).le

/-- `a ≤ exp s` with `0 ≤ s` gives `ExpB n s a` (the sharp form for small constants,
e.g. `8 ≤ exp 3`). -/
theorem ExpB.of_le_exp {n : ℕ} {a s : ℝ} (hM : 1 ≤ ell2 n * ell3 n) (hs : 0 ≤ s)
    (ha : a ≤ Real.exp s) : ExpB n s a := by
  rw [ExpB.def']
  exact ha.trans (Real.exp_le_exp.mpr (by nlinarith only [hs, hM]))

/-- Nonnegativity of anything `ExpB`-bounded from below by a natural is automatic;
this records `0 ≤ exp(c M)`. -/
theorem ExpB.nonneg_exp (n : ℕ) (c : ℝ) : 0 ≤ Real.exp (c * ell2 n * ell3 n) :=
  (Real.exp_pos _).le

/-- Successor: `a + 1 ≤ exp((c + 1) M)`. -/
theorem ExpB.succ {n : ℕ} {c a : ℝ} (hM : 1 ≤ ell2 n * ell3 n) (hc : 0 ≤ c) (h : ExpB n c a) :
    ExpB n (c + 1) (a + 1) := by
  have := ExpB.add' hM hc (le_refl (0 : ℝ)) h (ExpB.one (by linarith only [hM]) le_rfl)
  rwa [add_zero] at this

theorem ExpB.succ_nat {n : ℕ} {c : ℝ} {a : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (hc : 0 ≤ c)
    (h : ExpB n c (a : ℝ)) : ExpB n (c + 1) ((a + 1 : ℕ) : ℝ) := by
  push_cast
  exact ExpB.succ hM hc h

/-- `1728 ≤ exp 8`. -/
theorem le_exp_eight : (1728 : ℝ) ≤ Real.exp 8 := by
  have h := Real.exp_one_gt_d9
  have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h8]
  have : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h.le 8
  norm_num at this ⊢
  linarith only [this]

/-- The machine budget `B m = 64 (m + 2)^3` of an `ExpB`-bounded operand size:
`B m ≤ 64 · 27 · exp(3 c M) ≤ exp((3c + 8) M)`. -/
theorem ExpB.B {n : ℕ} {c : ℝ} {m : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (hc : 0 ≤ c)
    (h : ExpB n c (m : ℝ)) : ExpB n (3 * c + 8) ((TM.B m : ℕ) : ℝ) := by
  have hM0 : 0 ≤ ell2 n * ell3 n := by linarith only [hM]
  have h1 : (1 : ℝ) ≤ Real.exp (c * ell2 n * ell3 n) := ExpB.one hM0 hc
  have h2 : ((m : ℕ) : ℝ) + 2 ≤ 3 * Real.exp (c * ell2 n * ell3 n) := by
    unfold ExpB at h; linarith only [h, h1]
  have h3 : (((m : ℕ) : ℝ) + 2) ^ 3 ≤ (3 * Real.exp (c * ell2 n * ell3 n)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h2 3
  have h4 : (3 * Real.exp (c * ell2 n * ell3 n)) ^ 3
      = 27 * Real.exp (3 * c * ell2 n * ell3 n) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  have h5 : Real.exp 8 ≤ Real.exp (8 * ell2 n * ell3 n) :=
    Real.exp_le_exp.mpr (by rw [mul_assoc]; nlinarith only [hM])
  unfold TM.B ExpB
  push_cast
  have h6 : Real.exp ((3 * c + 8) * ell2 n * ell3 n)
      = Real.exp (3 * c * ell2 n * ell3 n) * Real.exp (8 * ell2 n * ell3 n) := by
    rw [← Real.exp_add]; ring_nf
  rw [h6]
  have hE := (Real.exp_pos (3 * c * ell2 n * ell3 n)).le
  have h7 := le_exp_eight
  calc (64 : ℝ) * (((m : ℕ) : ℝ) + 2) ^ 3
      ≤ 64 * (27 * Real.exp (3 * c * ell2 n * ell3 n)) := by
        rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = Real.exp (3 * c * ell2 n * ell3 n) * 1728 := by ring
    _ ≤ Real.exp (3 * c * ell2 n * ell3 n) * Real.exp (8 * ell2 n * ell3 n) :=
        mul_le_mul_of_nonneg_left (h7.trans h5) hE

/-- `2 ^ T ≤ exp(c M)` from `T ≤ c M` (`log 2 ≤ 1`). Stated for the real power
`(2 : ℝ) ^ T`; `push_cast` turns `((2 ^ T : ℕ) : ℝ)` into it. -/
theorem ExpB.two_pow {n : ℕ} {c : ℝ} {T : ℕ} (hT : (T : ℝ) ≤ c * (ell2 n * ell3 n)) :
    ExpB n c ((2 : ℝ) ^ T) := by
  rw [ExpB.def']
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith only [this]
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc (2 : ℝ) ^ T = Real.exp (Real.log 2) ^ T := by rw [Real.exp_log (by norm_num)]
    _ = Real.exp ((T : ℝ) * Real.log 2) := (Real.exp_nat_mul _ T).symm
    _ ≤ Real.exp (c * (ell2 n * ell3 n)) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hl2, hT0, hT]

theorem ExpB.two_pow_nat {n : ℕ} {c : ℝ} {T : ℕ} (hT : (T : ℝ) ≤ c * (ell2 n * ell3 n)) :
    ExpB n c ((2 ^ T : ℕ) : ℝ) := by
  push_cast
  exact ExpB.two_pow hT

/-- A power `z ^ T` from a logarithmic bound: `T · log z ≤ c M`. -/
theorem ExpB.nat_pow_of_log {n : ℕ} {c : ℝ} {z T : ℕ} (hz : 1 ≤ z)
    (h : (T : ℝ) * Real.log z ≤ c * (ell2 n * ell3 n)) : ExpB n c ((z : ℝ) ^ T) := by
  rw [ExpB.def']
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz
  calc (z : ℝ) ^ T = Real.exp (Real.log z) ^ T := by rw [Real.exp_log hz0]
    _ = Real.exp ((T : ℝ) * Real.log z) := (Real.exp_nat_mul _ T).symm
    _ ≤ Real.exp (c * (ell2 n * ell3 n)) := Real.exp_le_exp.mpr h

/-- Linear bit-length bound: `a ≤ exp(c M)` with `c ≥ 0` gives
`⌊log₂ a⌋ + 1 ≤ 2 c M + 1` (`log 2 ≥ 1/2`). -/
theorem bits_le_linear_of_ExpB {n : ℕ} {c : ℝ} {a : ℕ} (hM : 0 ≤ ell2 n * ell3 n) (hc : 0 ≤ c)
    (h : ExpB n c (a : ℝ)) :
    ((Nat.log 2 a : ℕ) : ℝ) + 1 ≤ 2 * c * (ell2 n * ell3 n) + 1 := by
  rw [ExpB.def'] at h
  have hcM : 0 ≤ c * (ell2 n * ell3 n) := mul_nonneg hc hM
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp; linarith only [hcM]
  · obtain ⟨b1, _⟩ := natLog_bridge a ha
    have hloga : Real.log a ≤ c * (ell2 n * ell3 n) := by
      have := Real.log_le_log (by exact_mod_cast ha) h
      rwa [Real.log_exp] at this
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith only [this]
    have hL0 : (0 : ℝ) ≤ (Nat.log 2 a : ℕ) := Nat.cast_nonneg _
    nlinarith only [b1, hloga, hl2, hL0]

/-- Bit length of an `ExpB`-bounded number: `⌊log₂ a⌋ + 1 ≤ exp((2c + 1) M)`. -/
theorem ExpB.log {n : ℕ} {c : ℝ} {a : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (hc : 0 ≤ c)
    (h : ExpB n c (a : ℝ)) : ExpB n (2 * c + 1) (((Nat.log 2 a : ℕ) : ℝ) + 1) := by
  have hM0 : 0 ≤ ell2 n * ell3 n := by linarith only [hM]
  have h1 := bits_le_linear_of_ExpB hM0 hc h
  rw [ExpB.def']
  have h2 := Real.add_one_le_exp (2 * c * (ell2 n * ell3 n))
  have h3 : Real.exp (2 * c * (ell2 n * ell3 n)) ≤ Real.exp ((2 * c + 1) * (ell2 n * ell3 n)) :=
    Real.exp_le_exp.mpr (by nlinarith only [hM])
  have h4 : Real.exp (2 * c * (ell2 n * ell3 n)) * 1
      ≤ Real.exp (2 * c * (ell2 n * ell3 n)) * Real.exp (1 * (ell2 n * ell3 n)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := Real.add_one_le_exp (1 * (ell2 n * ell3 n))
    linarith only [this, hM]
  rw [mul_one, ← Real.exp_add] at h4
  have h5 : Real.exp (2 * c * (ell2 n * ell3 n) + 1 * (ell2 n * ell3 n))
      = Real.exp ((2 * c + 1) * (ell2 n * ell3 n)) := by ring_nf
  rw [h5] at h4
  have h6 : (2 : ℝ) * c * (ell2 n * ell3 n) + 1 ≤ Real.exp ((2 * c + 1) * (ell2 n * ell3 n)) := by
    have hcM : 0 ≤ 2 * c * (ell2 n * ell3 n) := by positivity
    have h7 : (1 : ℝ) ≤ Real.exp (2 * c * (ell2 n * ell3 n)) := by
      linarith only [Real.add_one_le_exp (2 * c * (ell2 n * ell3 n)), hcM]
    nlinarith only [h2, h3, h4, h7, hcM]
  exact h1.trans h6

/-- The `ExpB.log` form with the bit length as a natural, `(Nat.log 2 a + 1 : ℕ)`. -/
theorem ExpB.bits {n : ℕ} {c : ℝ} {a : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (hc : 0 ≤ c)
    (h : ExpB n c (a : ℝ)) : ExpB n (2 * c + 1) ((Nat.log 2 a + 1 : ℕ) : ℝ) := by
  push_cast
  exact ExpB.log hM hc h

/-- Bit lengths of a product from bit lengths of the factors. -/
theorem ExpB.bits_mul {n : ℕ} {c₁ c₂ : ℝ} {a b : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (h1 : ExpB n c₁ ((Nat.log 2 a + 1 : ℕ) : ℝ))
    (h2 : ExpB n c₂ ((Nat.log 2 b + 1 : ℕ) : ℝ)) :
    ExpB n (c₁ + c₂ + 1) ((Nat.log 2 (a * b) + 1 : ℕ) : ℝ) :=
  ExpB.of_nat_le (bits_mul_le a b) (ExpB.add_nat hM hc₁ hc₂ h1 h2)

/-- Bit lengths of a power: `bits (a^k) ≤ k · bits a + 1`. -/
theorem ExpB.bits_pow {n : ℕ} {c₁ c₂ : ℝ} {a k : ℕ} (hM : 1 ≤ ell2 n * ell3 n) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hk : ExpB n c₁ (k : ℝ)) (h : ExpB n c₂ ((Nat.log 2 a + 1 : ℕ) : ℝ)) :
    ExpB n (c₁ + c₂ + 1) ((Nat.log 2 (a ^ k) + 1 : ℕ) : ℝ) := by
  refine ExpB.of_nat_le (bits_pow_le a k) ?_
  have hM0 : 0 ≤ ell2 n * ell3 n := by linarith only [hM]
  have hprod := ExpB.mul_nat hk h
  have hone : ExpB n 0 ((1 : ℕ) : ℝ) := by
    push_cast; exact ExpB.one hM0 le_rfl
  have := ExpB.add_nat hM (by positivity) le_rfl hprod hone
  rwa [add_zero] at this

/-! ### 4. Base facts in the window -/

/-- `ℓ₂(n) → ∞`. -/
theorem tendsto_ell2_atTopT : Tendsto ell2 atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `ℓ₃(n) → ∞`. -/
theorem tendsto_ell3_atTopT : Tendsto ell3 atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_ell2_atTopT

/-- `log n → ∞`. -/
theorem tendsto_log_natCast_atTopT : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The pure real-number heart of `window_base`: the atoms of the window are
`exp(O(M))`, `M = ℓ₂ ℓ₃`. -/
private lemma window_base_real {c ℓ2 ℓ3 z w y T : ℝ}
    (h2 : 1 ≤ ℓ2) (h3 : 12 ≤ ℓ3) (h_eq3 : ℓ3 = Real.log ℓ2)
    (hlogc : Real.log (4 * c) ≤ ℓ3) (hc32 : 32 * c ≤ ℓ3) (hc1000 : 1000 ≤ c)
    (hz_lb : c * ℓ2 * ℓ3 ≤ z) (hz_ub : z ≤ 4 * (c * ℓ2 * ℓ3))
    (hw : w ≤ 4 * z) (hy : y ≤ 4 * z) (hT : T ≤ 5 * ℓ2) :
    12 ≤ ℓ2 * ℓ3 ∧
    z ≤ Real.exp (1 * ℓ2 * ℓ3) ∧ w ≤ Real.exp (1 * ℓ2 * ℓ3) ∧ y ≤ Real.exp (1 * ℓ2 * ℓ3) ∧
    T ≤ Real.exp (1 * ℓ2 * ℓ3) ∧ T ≤ 1 * (ℓ2 * ℓ3) ∧
    Real.log z ≤ 3 * ℓ3 ∧ T * Real.log z ≤ 15 * (ℓ2 * ℓ3) := by
  have h2pos : (0 : ℝ) < ℓ2 := by linarith only [h2]
  have h3pos : (0 : ℝ) < ℓ3 := by linarith only [h3]
  have hM : (12 : ℝ) ≤ ℓ2 * ℓ3 := by nlinarith only [h2, h3]
  have hMpos : (0 : ℝ) < ℓ2 * ℓ3 := by linarith only [hM]
  have hT5 : T ≤ 1 * (ℓ2 * ℓ3) := by nlinarith only [hT, h2, h3]
  -- `exp M ≥ M²/2 ≥ 16 c M ≥ 4 z`.
  have hexp : (ℓ2 * ℓ3) ^ 2 / 2 ≤ Real.exp (1 * ℓ2 * ℓ3) := by
    rw [one_mul]
    have := Real.quadratic_le_exp_of_nonneg hMpos.le
    linarith only [this, hMpos]
  have hM32c : 32 * c ≤ ℓ2 * ℓ3 := by nlinarith only [hc32, h2, h3pos]
  have h4z : 4 * z ≤ (ℓ2 * ℓ3) ^ 2 / 2 := by
    have : 4 * z ≤ 16 * c * (ℓ2 * ℓ3) := by linarith only [hz_ub]
    nlinarith only [this, hM32c, hMpos]
  have htriple : (12000 : ℝ) ≤ c * ℓ2 * ℓ3 := by
    have i1 : (1000 : ℝ) * 1 ≤ c * ℓ2 :=
      mul_le_mul hc1000 h2 zero_le_one (by linarith only [hc1000])
    have i2 : (1000 : ℝ) * 1 * 12 ≤ c * ℓ2 * ℓ3 :=
      mul_le_mul i1 h3 (by norm_num)
        (mul_nonneg (by linarith only [hc1000]) (by linarith only [h2]))
    linarith only [i2]
  have hz12000 : (12000 : ℝ) ≤ z := by linarith only [htriple, hz_lb]
  have hz0 : 0 ≤ z := by linarith only [hz12000]
  have hMsq : ℓ2 * ℓ3 ≤ (ℓ2 * ℓ3) ^ 2 / 2 := by nlinarith only [hM]
  refine ⟨hM, ?_, ?_, ?_, ?_, hT5, ?_, ?_⟩
  · linarith only [h4z, hexp, hz0]
  · linarith only [h4z, hexp, hw]
  · linarith only [h4z, hexp, hy]
  · linarith only [hMsq, hexp, hT5]
  · -- `log z ≤ log(4c) + log ℓ₂ + log ℓ₃ ≤ 3 ℓ₃`.
    have hzpos : 0 < z := by linarith only [hz12000]
    have hzc : z ≤ 4 * c * (ℓ2 * ℓ3) := by linarith only [hz_ub]
    have e1 : Real.log z ≤ Real.log (4 * c * (ℓ2 * ℓ3)) := Real.log_le_log hzpos hzc
    have e2 : Real.log (4 * c * (ℓ2 * ℓ3))
        = Real.log (4 * c) + (Real.log ℓ2 + Real.log ℓ3) := by
      rw [Real.log_mul (by linarith only [hc1000] : (0 : ℝ) < 4 * c).ne' hMpos.ne',
        Real.log_mul h2pos.ne' h3pos.ne']
    have e3 : Real.log ℓ3 ≤ ℓ3 := by
      have h := Real.log_le_sub_one_of_pos h3pos; linarith only [h]
    have e4 : Real.log ℓ2 ≤ ℓ3 := le_of_eq h_eq3.symm
    linarith only [e1, e2.le, e3, e4, hlogc]
  · have hzpos : 0 < z := by linarith only [hz12000]
    have hzc : z ≤ 4 * c * (ℓ2 * ℓ3) := by linarith only [hz_ub]
    have e1 : Real.log z ≤ Real.log (4 * c * (ℓ2 * ℓ3)) := Real.log_le_log hzpos hzc
    have e2 : Real.log (4 * c * (ℓ2 * ℓ3))
        = Real.log (4 * c) + (Real.log ℓ2 + Real.log ℓ3) := by
      rw [Real.log_mul (by linarith only [hc1000] : (0 : ℝ) < 4 * c).ne' hMpos.ne',
        Real.log_mul h2pos.ne' h3pos.ne']
    have e3 : Real.log ℓ3 ≤ ℓ3 := by
      have h := Real.log_le_sub_one_of_pos h3pos; linarith only [h]
    have e4 : Real.log ℓ2 ≤ ℓ3 := le_of_eq h_eq3.symm
    have hlz : Real.log z ≤ 3 * ℓ3 := by linarith only [e1, e2.le, e3, e4, hlogc]
    have hz1 : 1 ≤ z := by linarith only [hz12000]
    have hlz0 : 0 ≤ Real.log z := Real.log_nonneg hz1
    have h := mul_le_mul hT hlz hlz0 (by linarith only [h2] : (0 : ℝ) ≤ 5 * ℓ2)
    linarith only [h]

/-- The atoms of the window are exp-bounded: for `n` large and any scales in
`InWindow C₁ E n z w y T`,
`ℓ₂ ≥ 1`, `ℓ₃ ≥ 12`, `M = ℓ₂ ℓ₃ ≥ 12`, `z, w, y, T, 2^T ≤ exp(M)`,
`z^T ≤ exp(15 M)`, `bits n = ⌊log₂ n⌋ + 1 ≤ exp(M)`, `log n ≤ exp(M)`, and
`16 (log n)^{1.2} ≤ exp(M)`. -/
theorem window_base (C₁ E : ℝ) (hE : 0 < E) (h1000 : (1000 : ℝ) ≤ C₁) :
    ∀ᶠ n : ℕ in atTop, ∀ z w y T : ℕ, InWindow C₁ E n z w y T →
      (1 : ℝ) ≤ ell2 n ∧ (12 : ℝ) ≤ ell3 n ∧ (12 : ℝ) ≤ ell2 n * ell3 n ∧
      ExpB n 1 (z : ℝ) ∧ ExpB n 1 (w : ℝ) ∧ ExpB n 1 (y : ℝ) ∧ ExpB n 1 (T : ℝ) ∧
      ExpB n 1 ((2 : ℝ) ^ T) ∧ ExpB n 15 ((z : ℝ) ^ T) ∧
      ExpB n 1 (((Nat.log 2 n : ℕ) : ℝ) + 1) ∧ ExpB n 1 (Real.log n) ∧
      ExpB n 1 (16 * (Real.log n) ^ (1.2 : ℝ)) := by
  have h2ev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ell2 n :=
    tendsto_ell2_atTopT.eventually_ge_atTop 1
  have h3ev : ∀ᶠ n : ℕ in atTop, (12 : ℝ) ≤ ell3 n :=
    tendsto_ell3_atTopT.eventually_ge_atTop 12
  have hlogcev : ∀ᶠ n : ℕ in atTop, Real.log (4 * C₁) ≤ ell3 n :=
    tendsto_ell3_atTopT.eventually_ge_atTop _
  have hc32ev : ∀ᶠ n : ℕ in atTop, 32 * C₁ ≤ ell3 n :=
    tendsto_ell3_atTopT.eventually_ge_atTop _
  have hlogev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    tendsto_log_natCast_atTopT.eventually_ge_atTop 1
  filter_upwards [h2ev, h3ev, hlogcev, hc32ev, hlogev, eventually_ge_atTop 1]
    with n h2 h3 hlogc hc32 hlogn hn1
  intro z w y T hw
  have h2pos : (0 : ℝ) < ell2 n := by linarith only [h2]
  have h3pos : (0 : ℝ) < ell3 n := by linarith only [h3]
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    have i1 : (1000 : ℝ) * 1 ≤ C₁ * ell2 n :=
      mul_le_mul h1000 h2 zero_le_one (by linarith only [h1000])
    have i2 : (1000 : ℝ) * 1 * 12 ≤ C₁ * ell2 n * ell3 n :=
      mul_le_mul i1 h3 (by norm_num)
        (mul_nonneg (by linarith only [h1000]) (by linarith only [h2]))
    linarith only [i2, hw.z_lo]
  have hy : (y : ℝ) ≤ 4 * (z : ℝ) := by
    have h1 : (z : ℝ) ^ ((1 : ℝ) - E) ≤ (z : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz1 (by linarith only [hE])
    rw [Real.rpow_one] at h1
    linarith only [hw.y_hi, h1]
  have hw4 : (w : ℝ) ≤ 4 * (z : ℝ) := by
    have h1 : (z : ℝ) ^ ((99 : ℝ) / 100) ≤ (z : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
    rw [Real.rpow_one] at h1
    linarith only [hw.w_hi, h1]
  obtain ⟨hM, hzE, hwE, hyE, hTE, hT5, _, hzT⟩ :=
    window_base_real h2 h3 rfl hlogc hc32 h1000 hw.z_lo hw.z_hi hw4 hy hw.T_hi
  have hM1 : (1 : ℝ) ≤ ell2 n * ell3 n := by linarith only [hM]
  have hz1n : 1 ≤ z := by exact_mod_cast hz1
  -- `log n = exp ℓ₂`, `(log n)^{1.2} = exp(1.2 ℓ₂)`.
  have hlogn0 : (0 : ℝ) < Real.log n := by linarith only [hlogn]
  have hlogn_eq : Real.log n = Real.exp (ell2 n) := (Real.exp_log hlogn0).symm
  have hl12 : (1.2 : ℝ) * ell2 n + 3 ≤ ell2 n * ell3 n := by nlinarith only [h2, h3]
  have hbitsn : ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ 2 * Real.log n + 1 := by
    obtain ⟨b1, _⟩ := natLog_bridge n hn1
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith only [this]
    have hL0 : (0 : ℝ) ≤ (Nat.log 2 n : ℕ) := Nat.cast_nonneg _
    nlinarith only [b1, hl2, hL0]
  have h16 : (16 : ℝ) ≤ Real.exp 3 := by
    have h := Real.exp_one_gt_d9
    have h3' : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3']
    have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
    norm_num at this ⊢
    linarith only [this]
  refine ⟨h2, h3, hM, hzE, hwE, hyE, hTE, ExpB.two_pow hT5,
    ExpB.nat_pow_of_log hz1n hzT, ?_, ?_, ?_⟩
  · -- `bits n ≤ 2 log n + 1 ≤ 3 exp ℓ₂ ≤ exp(ℓ₂ + 3) ≤ exp M`.
    unfold ExpB
    have h3e : (3 : ℝ) ≤ Real.exp 3 := by linarith only [h16]
    have hlogn1 : (1 : ℝ) ≤ Real.log n := hlogn
    have e1 : 2 * Real.log n + 1 ≤ 3 * Real.log n := by linarith only [hlogn1]
    have e2 : 3 * Real.log n ≤ Real.exp 3 * Real.exp (ell2 n) := by
      rw [hlogn_eq]
      exact mul_le_mul_of_nonneg_right h3e (Real.exp_pos _).le
    rw [← Real.exp_add] at e2
    have e3 : Real.exp (3 + ell2 n) ≤ Real.exp (1 * ell2 n * ell3 n) :=
      Real.exp_le_exp.mpr (by rw [one_mul]; linarith only [hl12, h2])
    linarith only [hbitsn, e1, e2, e3]
  · unfold ExpB
    rw [hlogn_eq]
    exact Real.exp_le_exp.mpr (by rw [one_mul]; nlinarith only [h2, h3])
  · unfold ExpB
    have e1 : (Real.log n) ^ (1.2 : ℝ) = Real.exp (ell2 n * 1.2) := by
      rw [Real.rpow_def_of_pos hlogn0]; rfl
    rw [e1]
    have e2 : 16 * Real.exp (ell2 n * 1.2) ≤ Real.exp 3 * Real.exp (ell2 n * 1.2) :=
      mul_le_mul_of_nonneg_right h16 (Real.exp_pos _).le
    rw [← Real.exp_add] at e2
    have e3 : Real.exp (3 + ell2 n * 1.2) ≤ Real.exp (1 * ell2 n * ell3 n) :=
      Real.exp_le_exp.mpr (by rw [one_mul]; linarith only [hl12])
    linarith only [e2, e3]

/-- The atoms in `ℕ`-cast form (`((2 ^ T : ℕ) : ℝ)`, `((z ^ T : ℕ) : ℝ)`), for step
bounds stated as naturals and pushed through `push_cast`. -/
theorem window_base_nat (C₁ E : ℝ) (hE : 0 < E) (h1000 : (1000 : ℝ) ≤ C₁) :
    ∀ᶠ n : ℕ in atTop, ∀ z w y T : ℕ, InWindow C₁ E n z w y T →
      ExpB n 1 ((2 ^ T : ℕ) : ℝ) ∧ ExpB n 15 ((z ^ T : ℕ) : ℝ) ∧
      ExpB n 1 ((Nat.log 2 n + 1 : ℕ) : ℝ) := by
  filter_upwards [window_base C₁ E hE h1000] with n h
  intro z w y T hw
  obtain ⟨_, _, _, _, _, _, _, h2T, hzT, hbits, _, _⟩ := h z w y T hw
  refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> assumption

/-! ### 2. The time function -/

/-- Given per-input step counts `g n` that are eventually `≤ exp(C ℓ₂ ℓ₃)`, a
time function of the INPUT LENGTH that bounds every input and is eventually
`≤ exp(C · log N · log log N)`, with the same constant `C`. -/
theorem exists_timeFun (g : ℕ → ℕ) (C : ℝ) (hC : 0 < C)
    (hg : ∀ᶠ n : ℕ in Filter.atTop, (g n : ℝ) ≤ Real.exp (C * ell2 n * ell3 n)) :
    ∃ time : ℕ → ℕ,
      (∀ n, g n ≤ time (Computability.encodeNat n).length) ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, (time N : ℝ) ≤ Real.exp (C * Real.log N * Real.log (Real.log N)) := by
  -- The eventual facts, made explicit as a threshold `n₁`.
  have hlogev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    tendsto_log_natCast_atTopT.eventually_ge_atTop 1
  have h2ev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ell2 n :=
    tendsto_ell2_atTopT.eventually_ge_atTop 1
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (hg.and (hlogev.and h2ev))
  set N₀ : ℕ := n₁ + 1 with hN₀
  let X : ℕ → ℝ := fun N => Real.exp (C * Real.log N * Real.log (Real.log N))
  refine ⟨fun N => if N₀ ≤ N then ⌊X N⌋₊ else (Finset.range (2 ^ N)).sup g, ?_, N₀, ?_⟩
  · intro n
    by_cases hN : N₀ ≤ (Computability.encodeNat n).length
    · simp only [hN, if_true]
      apply Nat.le_floor
      -- `n ≥ n₁`, so the eventual facts hold at `n`.
      have hn : n₁ ≤ n := le_of_encodeNat_length_succ n n₁ hN
      obtain ⟨hgn, hlogn, h2⟩ := hn₁ n hn
      have hn1 : 1 ≤ n := by
        have := le_of_encodeNat_length n N₀ hN (by omega)
        have h2 : 1 ≤ 2 ^ (N₀ - 1) := Nat.one_le_two_pow
        omega
      set N := (Computability.encodeNat n).length with hNdef
      have hNeq : N = Nat.log 2 n + 1 := encodeNat_length n hn1
      -- `log n < N log 2 < N`, hence `ℓ₂ n ≤ log N`, `ℓ₃ n ≤ log log N`.
      obtain ⟨_, b2⟩ := natLog_bridge n hn1
      have hNr : ((Nat.log 2 n : ℕ) : ℝ) + 1 = (N : ℝ) := by rw [hNeq]; push_cast; ring
      rw [hNr] at b2
      have hl2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith only [this]
      have hN0 : (0 : ℝ) < N := by
        have : 1 ≤ N := by omega
        exact_mod_cast this
      have hlogN : Real.log n ≤ (N : ℝ) := by
        have : (N : ℝ) * Real.log 2 ≤ (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hl2.le hN0.le
        linarith only [b2, this]
      have hlogn0 : (0 : ℝ) < Real.log n := by linarith only [hlogn]
      have hℓ2 : ell2 n ≤ Real.log N := Real.log_le_log hlogn0 hlogN
      have h2pos : (0 : ℝ) < ell2 n := by linarith only [h2]
      have hℓ3 : ell3 n ≤ Real.log (Real.log N) := Real.log_le_log h2pos hℓ2
      have hℓ3_0 : (0 : ℝ) ≤ ell3 n := Real.log_nonneg h2
      have hlogN0 : (0 : ℝ) ≤ Real.log N := by linarith only [hℓ2, h2pos]
      have hprod : ell2 n * ell3 n ≤ Real.log N * Real.log (Real.log N) :=
        mul_le_mul hℓ2 hℓ3 hℓ3_0 hlogN0
      calc (g n : ℝ) ≤ Real.exp (C * ell2 n * ell3 n) := hgn
        _ ≤ Real.exp (C * Real.log N * Real.log (Real.log N)) := by
            apply Real.exp_le_exp.mpr
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_left hprod hC.le
    · simp only [hN, if_false]
      apply Finset.le_sup (f := g)
      rw [Finset.mem_range]
      exact lt_two_pow_encodeNat_length n
  · intro N hN
    simp only [hN, if_true]
    exact Nat.floor_le (Real.exp_pos _).le

/-! ### 5. The final conversion -/

/-- `(cost : ℝ) ≤ exp(100 ℓ₂ ℓ₃)` is `ExpB n 100 cost`. -/
theorem ExpB.of_cost {n : ℕ} {cost : ℝ} (h : cost ≤ Real.exp (100 * ell2 n * ell3 n)) :
    ExpB n 100 cost := h

/-- `ExpB n c a` unfolded, for handing to `exists_timeFun`. -/
theorem ExpB.le_exp {n : ℕ} {c a : ℝ} (h : ExpB n c a) : a ≤ Real.exp (c * ell2 n * ell3 n) := h

/-- The time function from an eventual `ExpB` bound on the step counts. -/
theorem exists_timeFun_of_ExpB (g : ℕ → ℕ) (C : ℝ) (hC : 0 < C)
    (hg : ∀ᶠ n : ℕ in Filter.atTop, ExpB n C (g n : ℝ)) :
    ∃ time : ℕ → ℕ,
      (∀ n, g n ≤ time (Computability.encodeNat n).length) ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, (time N : ℝ) ≤ Real.exp (C * Real.log N * Real.log (Real.log N)) :=
  exists_timeFun g C hC hg

/-- The typical machine bound `steps ≤ (cost + 1) * poly`: from
`ExpB n c₁ cost` and `ExpB n c₂ poly` get `ExpB n (c₁ + 1 + c₂) steps`. -/
theorem ExpB.steps_of_le {n : ℕ} {c₁ c₂ : ℝ} {steps cost poly : ℕ}
    (hM : 1 ≤ ell2 n * ell3 n) (hc₁ : 0 ≤ c₁)
    (hsteps : steps ≤ (cost + 1) * poly) (hcost : ExpB n c₁ (cost : ℝ))
    (hpoly : ExpB n c₂ (poly : ℝ)) : ExpB n (c₁ + 1 + c₂) (steps : ℝ) :=
  ExpB.of_nat_le hsteps (ExpB.mul_nat (ExpB.succ_nat hM hc₁ hcost) hpoly)

/-! ### Worked example -/

/-- Worked example of the chaining T8b performs: a machine bound of the form
`steps ≤ (cost + 1) * (B (bits n + P * (5 * bits L)) * 2^T * L)` with
`cost ≤ exp(100 M)`, `L ≤ z^T`, `P ≤ 2^T` is `ExpB`. -/
example (C₁ E : ℝ) (hE : 0 < E) (h1000 : (1000 : ℝ) ≤ C₁) (cost L P steps : ℕ → ℕ)
    (hcost : ∀ᶠ n : ℕ in atTop, (cost n : ℝ) ≤ Real.exp (100 * ell2 n * ell3 n)) :
    ∀ᶠ n : ℕ in atTop, ∀ z w y T : ℕ, InWindow C₁ E n z w y T →
      L n ≤ z ^ T → P n ≤ 2 ^ T →
      steps n ≤ (cost n + 1) *
        (TM.B (Nat.log 2 n + 1 + P n * (5 * (Nat.log 2 (L n) + 1))) * 2 ^ T * L n) →
      ExpB n (100 + 1 + ((3 * (1 + (1 + (5 + (2 * 15 + 1))) + 1) + 8 + 1) + 15))
        (steps n : ℝ) := by
  filter_upwards [window_base C₁ E hE h1000, window_base_nat C₁ E hE h1000, hcost]
    with n hb hbn hc
  intro z w y T hw hL hP hsteps
  obtain ⟨_, _, hM12, _, _, _, _, _, _, hbits, _, _⟩ := hb z w y T hw
  obtain ⟨h2T, hzT, hbitsn⟩ := hbn z w y T hw
  have hM : (1 : ℝ) ≤ ell2 n * ell3 n := by linarith only [hM12]
  have hLE : ExpB n 15 (L n : ℝ) := ExpB.of_nat_le hL hzT
  have hPE : ExpB n 1 (P n : ℝ) := ExpB.of_nat_le hP h2T
  have hbL : ExpB n (2 * 15 + 1) ((Nat.log 2 (L n) + 1 : ℕ) : ℝ) :=
    ExpB.bits hM (by norm_num) hLE
  have h5 : ExpB n 5 ((5 : ℕ) : ℝ) := ExpB.natCast hM 5
  have hinner : ExpB n (1 + (1 + (5 + (2 * 15 + 1))) + 1)
      ((Nat.log 2 n + 1 + P n * (5 * (Nat.log 2 (L n) + 1)) : ℕ) : ℝ) :=
    ExpB.add_nat hM (by norm_num) (by norm_num) hbitsn
      (ExpB.mul_nat hPE (ExpB.mul_nat h5 hbL))
  have hB := ExpB.B hM (by norm_num) hinner
  have hpoly := ExpB.mul_nat (ExpB.mul_nat hB h2T) hLE
  exact ExpB.steps_of_le hM (by norm_num) hsteps (ExpB.of_cost hc) hpoly

end Carmichael
