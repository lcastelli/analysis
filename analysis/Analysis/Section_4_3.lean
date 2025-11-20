import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers `ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  . rw [abs_of_neg h, _root_.abs_of_neg h]
  . rw [h, abs_of_zero, abs_zero]
  . rw [abs_of_pos h, _root_.abs_of_pos h]

abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  by_cases h : 0 ≤ x
  . rwa [abs_of_nonneg h, ge_iff_le]
  . rw [not_le] at h
    rw [_root_.abs_of_neg h, ge_iff_le, Left.nonneg_neg_iff]
    exact le_of_lt h

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by
  rcases lt_trichotomy x 0 with h | h | h
  . simp_rw [_root_.abs_of_neg h, neg_eq_zero]
  . simp_rw [h, abs_zero]
  . simp_rw [_root_.abs_of_pos h]

/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  all_goals
    try rw [not_le] at hx
    try rw [not_le] at hy
    try rw [abs_of_nonneg hx]
    try rw [abs_of_nonneg hy]
    try rw [_root_.abs_of_neg hx]
    try rw [_root_.abs_of_neg hy]
  rotate_right
  . have : x + y < 0 := add_neg hx hy
    rw [_root_.abs_of_neg this, neg_add]
  . have : 0 ≤ x + y := add_nonneg hx hy
    rw [abs_of_nonneg this]
  all_goals by_cases hxy : 0 ≤ x + y
  all_goals
    try rw [not_le] at hxy
    try rw [abs_of_nonneg hxy]
    try rw [_root_.abs_of_neg hxy]
  . calc
      x + y ≤ x := add_le_of_nonpos_right (le_of_lt hy)
      _ ≤ x + -y := le_add_of_nonneg_right (by rw [Right.nonneg_neg_iff]; exact le_of_lt hy)
  . simp [hx]
  . calc
      x + y ≤ y := add_le_of_nonpos_left (le_of_lt hx)
      _ ≤ -x + y := le_add_of_nonneg_left (by rw [Right.nonneg_neg_iff]; exact le_of_lt hx)
  . simp [hy]

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  by_cases h : 0 ≤ x
  . simp_rw [abs_of_nonneg h]; grind
  . rw [not_le] at h; simp_rw [_root_.abs_of_neg h]; grind

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  by_cases h : 0 ≤ x
  . simp [h, abs_of_nonneg]
  . rw [not_le] at h; rw [_root_.abs_of_neg h]; grind

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  all_goals
    try rw [not_le] at hx
    try rw [not_le] at hy
    try rw [abs_of_nonneg hx]
    try rw [abs_of_nonneg hy]
    try rw [_root_.abs_of_neg hx]
    try rw [_root_.abs_of_neg hy]
  rotate_right
  . observe : 0 < x * y
    rw [_root_.abs_of_pos this, neg_mul_neg, mul_comm]
  . observe : 0 ≤ x * y
    rw [abs_of_nonneg this]
  . have : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (le_of_lt hy)
    rw [abs_of_nonpos this, mul_neg]
  . have : x * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hx) hy
    rw [abs_of_nonpos this, neg_mul]

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  by_cases h : 0 ≤ x
  . rw [abs_of_nonneg h, abs_of_nonpos (Right.neg_nonpos_iff.mpr h), neg_neg]
  . rw [not_le] at h; rw [_root_.abs_of_neg h, _root_.abs_of_pos (Left.neg_pos_iff.mpr h)]

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by
  rw [dist_eq]; apply abs_nonneg

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [dist_eq, abs_eq_zero_iff, sub_eq_zero]

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  rw [dist_eq, dist_eq, ←neg_sub, abs_neg]

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  simp_rw [dist_eq, show x - z = (x - y) + (y - z) by simp]
  apply abs_add

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by rw [close_iff, _root_.abs_of_neg (by norm_num)]; norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by rw [close_iff, _root_.abs_of_neg (by norm_num)]; norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by rw [close_iff, sub_self, abs_zero]; exact le_of_lt hε

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by rw [close_iff, sub_self, abs_zero]

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  simp_rw [close_iff]
  constructor
  . rintro rfl ε hε
    rw [sub_self, abs_zero];
    exact le_of_lt hε
  . intro h₁
    set z := x - y
    by_contra! h₂
    have := mt (abs_eq_zero_iff z).mp (by grind)
    replace h₂ := lt_of_le_of_ne' (abs_nonneg z) this
    specialize h₁ (|z| / 2) (half_pos h₂)
    absurd h₁; rw [not_le]
    exact div_lt_self h₂ (by decide)

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  rw [close_iff, close_iff, ←abs_neg, neg_sub]

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
  rw [close_iff] at hxy hyz ⊢
  calc
    _ ≤ |x - y| + |y - z| := dist_le x y z
    _ ≤ _ := by gcongr

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
  rw [close_iff] at hxy hzw ⊢
  calc
    _ = |(x - y) + (z - w)| := by abel_nf
    _ ≤ |x - y| + |z - w| := by apply abs_add
    _ ≤ _ := by gcongr

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
  have hzw' : δ.Close (-z) (-w) := by rw [close_iff] at hzw ⊢; rw [←abs_neg] at hzw; convert hzw using 1; ring_nf
  have := add_close hxy hzw'
  grind

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by
  rw [close_iff] at hxy ⊢
  exact le_trans hxy hε

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  rw [close_iff, ←abs_neg, neg_sub, ←abs_le_iff] at hxy hxz ⊢
  rcases hbetween with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  all_goals
    rw [←sub_le_sub_iff_right x] at h₁ h₂
    grind

/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
  rw [close_iff] at hxy ⊢
  rw [←mul_sub_right_distrib, abs_mul]
  gcongr

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
  set a := x - y
  have ha : x = y + a := by grind
  have haε: |a| ≤ ε := by rwa [close_iff] at hxy
  set b := w - z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : x * z - y * w = a * z - b * y := by grind
  rw [close_iff]
  calc
    _ = |a * z - b * y| := by grind
    _ = |a * z + -b * y| := by grind
    _ ≤ |a * z| + |-b * y| :=  by grind [abs_add]
    _ = |a| * |z| + |b| * |y| := by grind [abs_mul, abs_neg]
    _ ≤ _ := by gcongr


/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := rfl

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' m with m ih
  . rw [pow_zero, mul_one, add_zero]
  . rw [pow_succ, ←mul_assoc, ih, ←pow_succ, add_assoc]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m ih
  . rw [mul_zero, pow_zero, pow_zero]
  . rw [pow_succ, ih, pow_add, ←mul_add_one]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n ih
  . rw [pow_zero, pow_zero, pow_zero, mul_one]
  . rw [pow_succ, ih, show x ^ n * y ^ n * (x * y) = (x ^ n * x) * (y ^ n * y) by ring,
        ←pow_succ, ←pow_succ]

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
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

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  . rw [pow_zero]; decide
  . rw [pow_succ, ge_iff_le, mul_nonneg_iff]; left; exact ⟨ih, hx⟩

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n ih
  . rw [pow_zero]; decide
  . rw [pow_succ, gt_iff_lt, mul_pos_iff]; left; exact ⟨ih, hx⟩

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  . rw [pow_zero, pow_zero]
  . rw [pow_succ, pow_succ]
    gcongr
    exact pow_nonneg n (le_trans hy hxy)

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  rcases n with - | n; contradiction
  induction' n with n ih
  . rwa [pow_succ, pow_succ, pow_zero, pow_zero, one_mul, one_mul]
  . rw [pow_succ x, pow_succ y]
    specialize ih (by omega)
    gcongr

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  . rw [pow_zero, pow_zero, abs_one]
  . rw [pow_succ, pow_succ, abs_mul, ih]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  have pow_ne_zero {k : ℕ} : x ^ k ≠ 0 := by
    induction' k with k ih
    . rw [pow_zero]; decide
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
  . rw [pow_add, ←pow_eq_zpow, Int.natCast_add]
  case' pos => rw [mul_comm, add_comm]; let H := n.natAbs ≤ m.natAbs
  case' neg => let H := m.natAbs ≤ n.natAbs
  all_goals
    rw [←mul_div_assoc, mul_one]
    by_cases h : H
    . have ⟨k, h⟩ := exists_add_of_le h
      rw [h, add_comm, ←pow_add, mul_div_assoc, div_self pow_ne_zero, mul_one,
          Int.natCast_add, add_assoc, add_neg_cancel, add_zero, pow_eq_zpow]
    . rw [not_le] at h; have ⟨k, h⟩ := exists_add_of_le (le_of_lt h)
      rw [h, ←pow_add, div_mul_eq_div_div, div_self pow_ne_zero,
          Int.natCast_add, Int.add_neg_eq_sub, sub_add_eq_sub_sub, sub_self, zero_sub, zpow_neg]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by
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
    rw [pow_mul, ←Int.natCast_mul]
    try rw [←one_div_pow]
    try rw [neg_neg, one_div_one_div]
    try rw [pow_eq_zpow]
    try rw [zpow_neg]

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by
  by_cases hn : 0 ≤ n
  . replace hn := Int.eq_natAbs_of_nonneg hn
    rw [hn, pow_eq_zpow, mul_pow, pow_eq_zpow, pow_eq_zpow]
  . replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    rw [hn, zpow_neg, mul_pow, zpow_neg, zpow_neg, div_mul_div_comm, mul_one]

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  by_cases hn : 0 ≤ n
  . replace hn := Int.eq_natAbs_of_nonneg hn
    rw [hn, pow_eq_zpow]
    exact pow_pos _ hx
  . replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    rw [hn, zpow_neg, gt_iff_lt, one_div_pos]
    exact pow_pos _ hx

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  replace hn := Int.eq_natAbs_of_nonneg (le_of_lt hn)
  rw [hn, pow_eq_zpow, pow_eq_zpow]
  exact pow_ge_pow x y _ hxy (le_of_lt hy)

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_lt hn)
  rw [hn, zpow_neg, zpow_neg, one_div_le_one_div (pow_pos _ (lt_of_lt_of_le hy hxy)) (pow_pos _ hy)]
  exact pow_ge_pow x y _ hxy (le_of_lt hy)

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  rotate_left
  . assumption
  all_goals
    by_cases hn' : 0 ≤ n
    . replace hn' := Int.eq_natAbs_of_nonneg hn'
      rw [hn', pow_eq_zpow, pow_eq_zpow] at hxy
      have := pow_gt_pow _ _ n.natAbs h (by grind) (by grind) |> ne_of_lt
      symm_saturate; contradiction
    . replace hn' := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn')
      rw [hn', zpow_neg, zpow_neg, div_eq_div_iff (ne_of_lt (pow_pos _ hx)).symm (ne_of_lt (pow_pos _ hy)).symm,
          one_mul, one_mul] at hxy
      have := pow_gt_pow _ _ n.natAbs h (by grind) (by grind) |> ne_of_lt
      symm_saturate; contradiction

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by
  by_cases hn : 0 ≤ n
  . replace hn := Int.eq_natAbs_of_nonneg hn
    rw [hn, pow_eq_zpow, pow_eq_zpow, pow_abs]
  . replace hn := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)
    rw [hn, zpow_neg, zpow_neg, abs_div, abs_one, pow_abs]

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by
  suffices 2 ^ N ≥ N ∧ 2 ^ N ≥ 1 from this.left
  induction' N with n ih
  . decide
  . rw [_root_.pow_succ, mul_two]
    obtain ⟨ih₁, ih₂⟩ := ih
    constructor
    . gcongr
    . grw [ih₂]; decide
