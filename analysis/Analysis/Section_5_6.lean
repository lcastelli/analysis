import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from `Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' m with m ih
  . rw [pow_zero, mul_one, add_zero]
  . rw [pow_succ, ←mul_assoc, ih, ←pow_succ, add_assoc]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m ih
  . rw [mul_zero, pow_zero, pow_zero]
  . rw [pow_succ, ih, pow_add, ←mul_add_one]

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n ih
  . rw [pow_zero, pow_zero, pow_zero, mul_one]
  . rw [pow_succ, ih, show x ^ n * y ^ n * (x * y) = (x ^ n * x) * (y ^ n * y) by ring,
        ←pow_succ, ←pow_succ]

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  rcases n with - | n; contradiction
  induction' n with n ih
  . rw [pow_succ, pow_zero, one_mul]
  . rw [pow_succ, mul_eq_zero]
    constructor
    . rintro (h | h)
      . exact ih (by omega) |>.mp h
      . exact h
    . intro h
      right; exact h

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  . rw [pow_zero]; norm_num
  . rw [pow_succ, ge_iff_le, mul_nonneg_iff]; left; exact ⟨ih, hx⟩

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n ih
  . rw [pow_zero]; norm_num
  . rw [pow_succ, gt_iff_lt, mul_pos_iff]; left; exact ⟨ih, hx⟩

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  . rw [pow_zero, pow_zero]
  . rw [pow_succ, pow_succ]
    gcongr
    exact pow_nonneg n (le_trans hy hxy)

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  rcases n with - | n; contradiction
  induction' n with n ih
  . rwa [pow_succ, pow_succ, pow_zero, pow_zero, one_mul, one_mul]
  . rw [pow_succ x, pow_succ y]
    specialize ih (by omega)
    gcongr

/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  . rw [pow_zero, pow_zero, abs_one]
  . rw [pow_succ, pow_succ, abs_mul, ih]

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from `DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  have pow_ne_zero {k : ℕ} : x ^ k ≠ 0 := by
    induction' k with k ih
    . rw [pow_zero]; norm_num
    . rwa [pow_succ, ne_eq, mul_eq_zero_iff_right hx]
  by_cases hn : 0 ≤ n <;> by_cases hm : 0 ≤ m
  all_goals
    try replace hn := Int.eq_natAbs_of_nonneg hn
    try replace hm := Int.eq_natAbs_of_nonneg hm
    try replace hn :=  Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    try replace hm :=  Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hm)
    rw [hn, hm]
    try simp_rw [pow_eq_zpow]
    try simp_rw [zpow_neg]
  rotate_right
  . rw [div_mul_div_comm, one_mul, pow_add, ←zpow_neg, Int.natCast_add, Int.neg_add]
  . norm_cast; rw [pow_add, ←pow_eq_pow, Int.natCast_add]
  case' pos => rw [mul_comm, add_comm]; let H := n.natAbs ≤ m.natAbs
  case' neg => let H := m.natAbs ≤ n.natAbs
  all_goals
    rw [←mul_div_assoc, mul_one]
    by_cases h : H
    . have ⟨k, h⟩ := exists_add_of_le h
      rw [h, pow_eq_pow, add_comm, ←pow_add, mul_div_assoc, div_self pow_ne_zero, mul_one,
          Int.natCast_add, add_assoc, add_neg_cancel, add_zero, pow_eq_pow]
    . rw [not_le] at h; have ⟨k, h⟩ := exists_add_of_le (le_of_lt h)
      rw [h, pow_eq_pow, ←pow_add, div_mul_eq_div_div, div_self pow_ne_zero,
          Int.natCast_add, Int.add_neg_eq_sub, sub_add_eq_sub_sub, sub_self, zero_sub, zpow_neg]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  have one_div_pow (k : ℕ) : 1 / x ^ k = (1 / x) ^ k := by
    induction' k with k ih
    . simp_rw [pow_zero, one_div_one];
    . simp_rw [pow_succ, div_mul_eq_div_div, ih, ←div_eq_mul_one_div]
  by_cases hn : 0 ≤ n <;> by_cases hm : 0 ≤ m
  all_goals
    try replace hn := Int.eq_natAbs_of_nonneg hn
    try replace hm := Int.eq_natAbs_of_nonneg hm
    try replace hn :=  Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    try replace hm :=  Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hm)
    rw [hn, hm]
    try simp_rw [pow_eq_zpow]
    try simp_rw [zpow_neg]
    try rw [one_div_pow, Int.neg_mul]
    try rw [Int.mul_neg]
    try simp_rw [pow_eq_pow]
    rw [pow_mul, ←Int.natCast_mul]
    try rw [←one_div_pow]
    try rw [neg_neg, one_div_one_div]
    try rw [pow_eq_zpow]
    try rw [zpow_neg]
    try simp_rw [pow_eq_pow]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by
  by_cases hn : 0 ≤ n
  . replace hn := Int.eq_natAbs_of_nonneg hn
    rw [hn, pow_eq_pow, mul_pow, pow_eq_pow, pow_eq_pow]
  . replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    rw [hn, zpow_neg, mul_pow, zpow_neg, zpow_neg, div_mul_div_comm, mul_one]

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  by_cases hn : 0 ≤ n
  . replace hn := Int.eq_natAbs_of_nonneg hn
    rw [hn, pow_eq_pow]
    exact pow_pos _ hx
  . replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    rw [hn, zpow_neg, gt_iff_lt, one_div_pos]
    exact pow_pos _ hx

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  replace hn := Int.eq_natAbs_of_nonneg (le_of_lt hn)
  rw [hn, pow_eq_pow, pow_eq_pow]
  exact pow_ge_pow x y _ hxy (le_of_lt hy)

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_lt hn)
  rw [hn, zpow_neg, zpow_neg, one_div_le_one_div (pow_pos _ (lt_of_lt_of_le hy hxy)) (pow_pos _ hy)]
  exact pow_ge_pow x y _ hxy (le_of_lt hy)

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  rotate_left
  . assumption
  all_goals
    by_cases hn' : 0 ≤ n
    . replace hn' := Int.eq_natAbs_of_nonneg hn'
      rw [hn', pow_eq_pow, pow_eq_pow] at hxy
      have := pow_gt_pow _ _ n.natAbs h (by grind) (by grind) |> ne_of_lt
      symm_saturate; contradiction
    . replace hn' := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn')
      rw [hn', zpow_neg, zpow_neg, div_eq_div_iff (ne_of_lt (pow_pos _ hx)).symm (ne_of_lt (pow_pos _ hy)).symm,
          one_mul, one_mul] at hxy
      have := pow_gt_pow _ _ n.natAbs h (by grind) (by grind) |> ne_of_lt
      symm_saturate; contradiction

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by
  by_cases hn : 0 ≤ n
  . replace hn := Int.eq_natAbs_of_nonneg hn
    rw [hn, pow_eq_pow, pow_eq_pow, pow_abs]
  . replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    rw [hn, zpow_neg, zpow_neg, abs_div, abs_one, pow_abs]

/-- Definition 5.6.2.  We permit ``junk values'' when `x` is negative or `n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  simp [zero_pow (by linarith), hx]

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      rw [← one_pow n]
      exact pow_gt_pow _ _ _ hy' (by norm_num) (by positivity)
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    replace hy := hy.left
    induction' hn' : n - 1 with n' ih generalizing n
    . simp [show n = 1 by grind, hy']
    . specialize ih (n - 1) (by omega) (by grind)
      rw [hn'] at ih
      rw [Nat.sub_eq_iff_eq_add hn] at hn'
      rw [hn', ← pow_add, pow_one]
      apply lt_trans ih
      rw [lt_mul_iff_one_lt_right (by linarith)]
      linarith
  linarith

lemma Real.binomial_lb {x ε : Real} (hε : 0 ≤ ε) (hxε : ε ≤ x) (n : ℕ) :
    x ^ n - ε * (x + 1) ^ n ≤ (x - ε) ^ n := by
  induction' n with n ih
  . simp [hε]
  . rw [← ge_iff_le]
    calc _
      _ = (x - ε) ^ n * (x - ε) := by grind
      _ = x * (x - ε) ^ n - ε * (x - ε) ^ n := by grind
      _ ≥ x * (x ^ n - ε * (x + 1) ^ n) - ε * (x + 1) ^ n := by gcongr <;> grind
      _ = x ^ (n + 1) - ε * x * (x + 1) ^ n - ε * (x + 1) ^ n := by grind
      _ = x ^ (n + 1) - ε * (x + 1) ^ n * (x + 1) := by grind
      _ = x ^ (n + 1) - ε * (x + 1) ^ (n + 1) := by grind

lemma Real.binomial_ub {x ε : Real} (hx : 0 ≤ x) (hε : 0 ≤ ε) (hε' : ε ≤ 1) (n : ℕ) :
    (x + ε) ^ n ≤ x ^ n + ε * (x + 1) ^ n := by
  induction' n with n ih
  . simp [hε]
  . calc _
      _ = (x + ε) ^ n * (x + ε) := by grind
      _ = x * (x + ε) ^ n + ε * (x + ε) ^ n := by grind
      _ ≤ x * (x ^ n + ε * (x + 1) ^ n) + ε * (x + 1) ^ n := by gcongr
      _ = x ^ (n + 1) + ε * (x + 1) ^ n * x + ε * (x + 1) ^ n := by grind
      _ = x ^ (n + 1) + ε * (x + 1) ^ n * (x + 1) := by grind
      _ = x ^ (n + 1) + ε * (x + 1) ^ (n + 1) := by grind

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  rw [root]
  have hlub := ExtendedReal.sSup_of_bounded (rootset_nonempty hx n hn) (rootset_bddAbove n hn)
  set E := {y | y ≥ 0 ∧ y ^ n ≤ x}
  simp_rw [isLUB_def, upperBound_def] at hlub
  have : 0 ∈ E := by simp [E, zero_pow (by positivity), hx]
  exact hlub.left 0 this

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
  revert x y
  have hfwd {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) : y = x.root n → y ^ n = x := by
    intro hyx
    rw [Real.root] at hyx
    replace hyx := hyx.symm ▸ ExtendedReal.sSup_of_bounded (rootset_nonempty hx n hn) (rootset_bddAbove n hn)
    simp_rw [isLUB_def, upperBound_def, Set.mem_setOf] at hyx
    rcases trichotomous' (y ^ n) x with (h | h | rfl)
    . absurd hyx.right
      simp_rw [not_forall, exists_prop, not_le, and_imp]
      replace hy : 0 < y := by
        apply lt_of_le_of_ne' hy
        by_contra!
        rw [this, zero_pow (by grind)] at h
        grind
      let ε := (y ^ n - x) / (2 * (y + 1) ^ n)
      have hε : 0 < ε := by
        simp_rw [ε, div_pos_iff_of_pos_left (sub_pos_of_lt h)]
        positivity
      have hyε : 0 ≤ y - ε := by
        simp_rw [sub_nonneg, ε]
        grw [div_le_comm₀ (by positivity) hy, hx, sub_zero, ← Nat.sub_one_add_one (Nat.ne_zero_of_lt hn),
            ← pow_add, pow_one, mul_div_cancel_right₀ _ (ne_of_gt hy), ← pow_add, pow_one,
            show (2 : Real) > 1 by norm_num, one_mul]
        nth_grw 2 [show y + 1 > 1 by linarith]
        rw [mul_one]
        exact pow_ge_pow _ _ _ (by linarith) (le_of_lt hy)
      have hxyε : x < (y - ε) ^ n := by
        apply lt_of_lt_of_le _ (binomial_lb (le_of_lt hε) (by linarith) n)
        simp_rw [ε, div_mul]
        rw [mul_div_cancel_right₀ _ (by grind [pow_eq_zero_iff]), sub_div' (by norm_num),
            ← sub_add, mul_two, add_sub_cancel_right, ← sub_pos, div_sub' (by norm_num),
            two_mul, add_sub_assoc, sub_add_cancel_left, ← sub_eq_add_neg,
            div_pos_iff_of_pos_right (by norm_num), sub_pos]
        exact h
      use y - ε
      constructor
      . intro z hz hz'
        grw [← hz'] at hxyε
        by_contra!
        refine not_gt_and_lt _ _ ⟨hxyε, ?_⟩
        exact pow_gt_pow _ _ n this hyε hn
      . linarith
    . absurd hyx.left
      simp_rw [not_forall, exists_prop, not_le]
      let ε := min 1 ((x - y ^ n) / (2 * (y + 1) ^ n))
      have hε : 0 < ε := by
        simp_rw [ε, lt_inf_iff, zero_lt_one, true_and, div_pos_iff_of_pos_left (sub_pos_of_lt h)]
        positivity
      have hε' : ε ≤ 1 := by simp [ε]
      have hyεx : (y + ε) ^ n < x := by
        apply lt_of_le_of_lt (binomial_ub hy (le_of_lt hε) hε' n)
        unfold ε
        grw [min_le_right, div_mul, mul_div_cancel_right₀ _ (by grind [pow_eq_zero_iff]),
            add_div' _ _ _ (by norm_num), ← add_sub_assoc, ← sub_add_eq_add_sub, mul_two,
            add_sub_cancel_right, div_lt_iff₀ (by norm_num), ← lt_sub_iff_add_lt, mul_two,
            add_sub_cancel_right]
        exact h
      use y + ε
      and_intros
      . positivity
      . exact le_of_lt hyεx
      . linarith
    . rfl
  intro x y hx hy
  constructor
  . exact hfwd hx hy
  . intro hyx
    by_contra! h
    have hz := (root_nonneg hx hn)
    rw [← hfwd hx hz rfl] at hyx
    generalize x.root n = z at *
    wlog hyz : y < z generalizing y z
    . exact this hz y hyx.symm h.symm hy (lt_of_le_of_ne (le_of_not_gt hyz) h.symm)
    have := pow_gt_pow z y n hyz hy hn
    exact not_lt_and_eq _ _ ⟨this, hyx⟩

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  constructor
  . intro h
    by_contra! hx'
    replace hx : x = 0 := eq_of_le_of_ge hx' hx
    have h0 : root 0 n = 0 := by rw [eq_comm, eq_root_iff_pow_eq le_rfl le_rfl hn, zero_pow (by positivity)]
    rw [hx, h0] at h
    exact lt_irrefl 0 h
  . intro h
    by_contra! hroot
    have hnonneg := root_nonneg hx hn
    replace hroot := eq_of_le_of_ge hroot hnonneg
    have hx : x = 0 := by rw [eq_comm, ← zero_pow (by positivity), ← eq_root_iff_pow_eq hx le_rfl hn, hroot.symm]
    exact not_gt_and_eq _ _ ⟨h, hx⟩

theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  rw [← eq_root_iff_pow_eq hx (root_nonneg hx hn) hn]

theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  rw [eq_comm, eq_root_iff_pow_eq (pow_nonneg n hx) hx hn]

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  constructor
  . intro hxy
    by_contra! h
    have := pow_ge_pow _ _ n h (root_nonneg hx hn)
    rw [pow_of_root hy hn, pow_of_root hx hn] at this
    linarith
  . intro h
    have := pow_gt_pow _ _ _ h (root_nonneg hy hn) hn
    rwa [pow_of_root hx hn, pow_of_root hy hn] at this

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  have h1lt : ∀ n ≥ 1, x.root n > 1 := by
    intro n hn
    by_contra! hxn
    have := pow_ge_pow _ _ n hxn (root_nonneg (by positivity) hn)
    rw [one_pow, pow_of_root (x := x) (by positivity) hn] at this
    exact not_le_of_gt hx this
  have hy := h1lt k (by linarith)
  have hz := h1lt l (by linarith)
  set y := x.root k
  set z := x.root l
  set j := k - l
  have hyz : y ^ k = z ^ l:= by rw [pow_of_root (by linarith) (by linarith), pow_of_root (by linarith) (by linarith)]
  rw [show k = l + j by omega, ← pow_add] at hyz
  have hyn (n : ℕ) (hn : 1 ≤ n) : 1 < y ^ n := by
    have := pow_gt_pow _ _ n hy (by norm_num) (by positivity)
    rwa [one_pow] at this
  have hyz' := lt_mul_of_one_lt_right (by have := hyn l hl; linarith : 0 < y ^ l) (hyn j (by omega))
  rw [hyz] at hyz'
  by_contra!
  replace := pow_ge_pow _ _ l this (root_nonneg (by positivity) hl)
  exact not_le_of_gt hyz' this

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  have hlt1 : ∀ n ≥ 1, x.root n < 1 := by
    intro n hn
    by_contra! hxn
    have := pow_ge_pow _ _ n hxn (by norm_num)
    rw [one_pow, pow_of_root (x := x) (by positivity) hn] at this
    exact not_le_of_gt hx this
  have hy0 := root_pos (x := x) (n := k) (by linarith) (by linarith) |>.mpr hx0
  have hy := hlt1 k (by linarith)
  have hz := hlt1 l (by linarith)
  set y := x.root k
  set z := x.root l
  set j := k - l
  have hyz : y ^ k = z ^ l:= by rw [pow_of_root (by linarith) (by linarith), pow_of_root (by linarith) (by linarith)]
  rw [show k = l + j by omega, ← pow_add] at hyz
  have hyj : y ^ j < 1 := by
    have := pow_gt_pow _ _ j hy (root_nonneg (le_of_lt hx0) (by linarith)) (by omega)
    rwa [one_pow] at this
  have hyz' := mul_lt_of_lt_one_right (pow_pos l hy0) hyj
  rw [hyz] at hyz'
  by_contra!
  replace := pow_ge_pow _ _ l this (le_of_lt hy0)
  exact not_le_of_gt hyz' this

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  rw [eq_comm, eq_root_iff_pow_eq (by norm_num) (by norm_num) hk, one_pow]

lemma Real.pow_inj {x y : Real} (hx : 0 ≤ x) (hy : 0 ≤ y) {n : ℕ} (hn : 1 ≤ n) (hxn : x ^ n = y ^ n) : x = y := by
  rwa [← eq_root_iff_pow_eq (pow_nonneg n hy) hx hn, root_of_pow hy hn] at hxn

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  have hxy := calc (x.root n * y.root n) ^ n
    _ = (x.root n) ^ n * (y.root n) ^ n := by rw [mul_pow]
    _ = x * y := by rw [pow_of_root hx hn, pow_of_root hy hn]
    _ = ((x * y).root n) ^ n := by rw [pow_of_root (by positivity) hn]
  refine' pow_inj _ _ hn hxy.symm
  . exact root_nonneg (by positivity) hn
  . have h1 := root_nonneg hx hn
    have h2 := root_nonneg hy hn
    positivity

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  have hxy := calc ((x.root n).root m) ^ (n * m)
    _ = (((x.root n).root m) ^ m) ^ n := by rw [mul_comm, pow_mul]
    _ = x := by rw [pow_of_root (root_nonneg hx hn) hm, pow_of_root hx hn]
    _ = (x.root (n * m)) ^ (n * m) := by rw [pow_of_root hx (by grw [hn, hm])]
  refine' pow_inj _ _ (by grw [hn, hm]) hxy
  . exact root_nonneg (root_nonneg hx hn) hm
  . exact root_nonneg hx (by grw [hn, hm])

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  rw [eq_comm, eq_root_iff_pow_eq (le_of_lt hx) (le_of_lt hx) le_rfl, pow_one]

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  exact pow_inj (le_of_lt hy) (le_of_lt hz) hn h

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by simpa [ha, eq_comm, ne_of_gt hb'] using hq
    simp_all
  have : a' > 0 := by
    have : 0 < (a : ℚ) / b := by positivity
    rw [hq, div_pos_iff_of_pos_right (by positivity)] at this
    exact_mod_cast this
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, mul_comm, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]

theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  rw [← Int.cast_one, ratPow_def hx _ hn, zpow_one]

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  rw [show (n : ℚ) = n / (1 : ℕ) by simp, ratPow_def hx _ (by decide), root_one hx]

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [ratPow_def hx _ hb]
  exact zpow_pos a (root_pos (le_of_lt hx) (by omega) |>.mpr hx)

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  conv_lhs =>
    rw [div_add_div _ _ (by norm_cast; grind) (by norm_cast; grind)]
    norm_cast
    rw [Rat.divInt_eq_div, Int.cast_natCast, ratPow_def hx _ (by positivity)]
    rw [← zpow_add _ _ _ (root_pos (le_of_lt hx) (by grw [← Nat.one_le_of_lt hb, ← Nat.one_le_of_lt hd])
        |>.mpr hx |> ne_of_gt)]
    rw [← ratPow_def hx _ (by positivity), ← ratPow_def hx _ (by positivity)]
  push_cast
  rw [mul_div_mul_right _ _ (by norm_cast; grind), mul_div_mul_left _ _ (by norm_cast; grind)]

lemma Real.root_pow_comm {x : Real} (hx : 0 ≤ x) (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (x.root b) ^ a = (x ^ a).root b := by
  rw [eq_root_iff_pow_eq (zpow_nonneg hx a) (zpow_nonneg (root_nonneg hx hb) a) (by omega),
      ← pow_eq_pow, zpow_mul, mul_comm, ← zpow_mul, pow_eq_pow, pow_of_root hx hb]

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  obtain ⟨c, d, hd, rfl⟩ := Rat.eq_quot r
  conv_rhs =>
    rw [div_mul_div_comm]
    norm_cast
    rw [Rat.divInt_eq_div, Int.cast_natCast, ratPow_def hx _ (by positivity)]
    rw [← zpow_mul, ← root_root (le_of_lt hx) hb hd]
    rw [root_pow_comm (root_nonneg (le_of_lt hx) hb) _ hd, ← ratPow_def hx a hb]
    rw [← ratPow_def (ratPow_pos hx _) _ hd]

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  by_cases ha : 0 ≤ a
  . lift a to ℕ using ha
    rw [← neg_div, ← Int.cast_neg, ratPow_def hx (-a) hb, zpow_neg a, ← pow_eq_pow, ← ratPow_def hx _ hb]
  . rw [not_le] at ha
    obtain ⟨c, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_lt ha)
    field_simp
    rw [show -(c : ℚ) = ↑(-(c : ℤ)) by simp, ratPow_def hx (-c) hb, zpow_neg c,
        one_div_one_div, ← pow_eq_pow, ← ratPow_def hx _ hb, Int.cast_natCast]

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [ratPow_def hx _ hb, ratPow_def hy _ hb, root_mono (le_of_lt hx) (le_of_lt hy) hb]
  rw [gt_iff_lt, div_pos_iff_of_pos_right (by norm_cast), Int.cast_pos] at h
  lift a to ℕ using (le_of_lt h)
  norm_cast at h
  simp_rw [pow_eq_pow]
  constructor
  . intro h'
    exact pow_gt_pow _ _ a h' (root_nonneg (le_of_lt hy) hb) h
  . intro h'
    by_contra!
    exact not_le_of_gt h' (pow_ge_pow _ _ a this (root_nonneg (le_of_lt hx) hb))

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  have hx0 : x > 0 := by linarith
  have aux : ∀ {s:ℚ}, s > 0 → x^s > 1 := by
    intro s hs
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot s
    rw [Real.ratPow_def hx0 a hb]
    rw [gt_iff_lt] at hs
    have ha_pos : 0 < a := by
      rw [div_pos_iff_of_pos_right (by norm_cast)] at hs
      exact_mod_cast hs
    lift a to ℕ using (le_of_lt ha_pos)
    rw [Real.pow_eq_pow]
    have hb_ge_1 : b ≥ 1 := by omega
    have hroot : x.root b > 1 := by
      rw [←Real.root_of_one hb_ge_1]
      apply (Real.root_mono (by linarith) (by norm_num) hb_ge_1).mp hx
    rw [←one_pow a]
    apply Real.pow_gt_pow _ _ _ hroot (by norm_num)
    norm_cast at ha_pos
  constructor
  . intro h
    rcases lt_trichotomy q r with hqr | rfl | hqr
    . have : x^q < x^r := by
        rw [←sub_pos] at hqr
        rw [←sub_add_cancel r q, Real.ratPow_add hx0, mul_comm]
        conv_lhs => rw [←mul_one (x^q)]
        apply mul_lt_mul_of_pos_left (aux hqr) (Real.ratPow_pos hx0 q)
      rw [gt_iff_lt] at h
      linarith
    . linarith
    . exact hqr
  . intro hqr
    rw [gt_iff_lt] at hqr
    rw [←sub_pos] at hqr
    rw [←sub_add_cancel q r, Real.ratPow_add hx0]
    conv_rhs => rw [←mul_one (x^r)]
    conv_lhs => rw [mul_comm]
    apply mul_lt_mul_of_pos_left (aux hqr) (Real.ratPow_pos hx0 r)

/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  have aux : ∀ {s:ℚ}, s > 0 → x^s < 1 := by
    intro s hs
    obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot s
    rw [Real.ratPow_def hx0 a hb]
    rw [gt_iff_lt] at hs
    have ha_pos : 0 < a := by
      rw [div_pos_iff_of_pos_right (by norm_cast)] at hs
      exact_mod_cast hs
    lift a to ℕ using (le_of_lt ha_pos)
    rw [Real.pow_eq_pow]
    have hb_ge_1 : b ≥ 1 := by omega
    have hroot : x.root b < 1 := by
      rw [←Real.root_of_one hb_ge_1]
      have := (Real.root_mono (by norm_num) (le_of_lt hx0) hb_ge_1).mp hx
      rw [gt_iff_lt] at this
      exact this
    have hroot_pos : 0 ≤ x.root b := le_of_lt (Real.root_pos (le_of_lt hx0) hb_ge_1 |>.mpr hx0)
    rw [←one_pow a]
    apply Real.pow_gt_pow 1 (x.root b) a hroot hroot_pos (by linarith)
  constructor
  . intro h
    rcases lt_trichotomy q r with hqr | rfl | hqr
    . exact hqr
    . linarith
    . have : x^q < x^r := by
        have h_diff : 0 < q - r := sub_pos.mpr hqr
        have h_lt_one := aux h_diff
        have := mul_lt_mul_of_pos_right h_lt_one (Real.ratPow_pos hx0 r)
        rw [one_mul] at this
        convert this using 1
        rw [←Real.ratPow_add hx0, sub_add_cancel]
      rw [gt_iff_lt] at h
      linarith
  . intro hqr
    rw [gt_iff_lt]
    have h_diff : 0 < r - q := sub_pos.mpr hqr
    have h_lt_one := aux h_diff
    have := mul_lt_mul_of_pos_right h_lt_one (Real.ratPow_pos hx0 q)
    rw [one_mul] at this
    convert this using 1
    rw [←Real.ratPow_add hx0, sub_add_cancel]

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  obtain ⟨a, b, hb, rfl⟩ := Rat.eq_quot q
  rw [ratPow_def hx _ hb, ratPow_def hy _ hb, ← mul_zpow,
      ← root_mul hx.le hy.le hb, ← ratPow_def (by positivity) _ hb]

/-- Exercise 5.6.3 -/
theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  obtain ⟨m, rfl⟩ := hn
  rw [← pow_add]
  set y := x ^ m
  by_cases hy : 0 ≤ y
  . grw [← hy, zero_mul]
  . rw [not_le] at hy
    exact mul_pos_of_neg_of_neg hy hy |>.le

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  wlog hxy : x ≤ y generalizing x y
  . specialize this hy hx (by linarith); simpa [max_comm] using this
  rcases hxy with hxy | rfl
  . have hxy' := ratPow_mono hy hx hq |>.mp hxy
    simp [hxy.le, hxy'.le]
  . simp

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  wlog hxy : x ≤ y generalizing x y
  . specialize this hy hx (by linarith); simpa [min_comm] using this
  rcases hxy with hxy | rfl
  . have hxy' := ratPow_mono hy hx hq |>.mp hxy
    simp [hxy.le, hxy'.le]
  . simp

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.
theorem Real.max_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  max (x^q) (y^q) = (min x y)^q := by
  have (eq := hr) r := -q
  rw [← neg_eq_iff_eq_neg] at hr
  subst q
  rw [Left.neg_neg_iff] at hq
  rw [eq_comm, ratPow_neg hx, ratPow_neg hy, ratPow_neg (by simp_all), ← min_ratPow hx hy hq]
  simp_rw [← inv_eq_one_div]
  exact inv_min (Real.isPos_iff _ |>.mpr (ratPow_pos hx _)) (Real.isPos_iff _ |>.mpr (ratPow_pos hy _))

theorem Real.min_ratPow_neg {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q < 0) :
  min (x^q) (y^q) = (max x y)^q := by
  have (eq := hr) r := -q
  rw [← neg_eq_iff_eq_neg] at hr
  subst q
  rw [Left.neg_neg_iff] at hq
  rw [eq_comm, ratPow_neg hx, ratPow_neg hy, ratPow_neg (by simp_all), ← max_ratPow hx hy hq]
  simp_rw [← inv_eq_one_div]
  exact inv_max (Real.isPos_iff _ |>.mpr (ratPow_pos hx _)) (Real.isPos_iff _ |>.mpr (ratPow_pos hy _))

end Chapter5
