import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases hx : x = 0
  . left; exact hx
  . right
    obtain ⟨a, ha, ⟨c, hc, ha'⟩, rfl⟩ := boundedAwayZero_of_nonzero hx
    have hN := ha
    simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at hN
    obtain ⟨N, hN⟩ := hN c hc
    have hN' := ha' N
    by_cases h : 0 ≤ a N
    . rw [abs_of_nonneg h] at hN'
      let a' (n : ℕ) : ℚ := if n < N then c else a n
      left; use a'
      have hcauchy : (a' : Sequence).IsCauchy := by
        simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq, a'] at ha ⊢
        peel ha with ε hε ha
        obtain ⟨N', ha⟩ := ha
        use max N N'
        intro n hn m hm
        simp [Nat.not_lt_of_le (le_of_max_le_left hn), Nat.not_lt_of_le (le_of_max_le_left hm),
            ha n (by omega) m (by omega)]
      and_intros
      . use c, hc
        intro n
        unfold a'; split_ifs with hn
        . exact le_rfl
        . specialize hN N le_rfl n (Nat.le_of_not_lt hn)
          specialize ha' n
          rwa [abs_of_nonneg] at ha'
          by_contra!
          rw [abs_of_neg this] at ha'
          grw [abs_of_nonneg (by linarith), hN', _root_.sub_eq_add_neg, ha'] at hN
          grind
      . exact hcauchy
      . simp_rw [LIM_eq_LIM ha hcauchy, Sequence.equiv_iff, a']
        intro ε hε
        use N
        intro n hn
        simp [Nat.not_lt_of_le hn, le_of_lt hε]
    . rw [abs_of_neg (lt_of_not_ge h), ge_iff_le, le_neg] at hN'
      let a' (n : ℕ) : ℚ := if n < N then -c else a n
      right; use a'
      have hcauchy : (a' : Sequence).IsCauchy := by
        simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq, a'] at ha ⊢
        peel ha with ε hε ha
        obtain ⟨N', ha⟩ := ha
        use max N N'
        intro n hn m hm
        simp [Nat.not_lt_of_le (le_of_max_le_left hn), Nat.not_lt_of_le (le_of_max_le_left hm),
            ha n (by omega) m (by omega)]
      and_intros
      . use c, hc
        intro n
        unfold a'; split_ifs with hn
        . exact le_rfl
        . specialize hN N le_rfl n (Nat.le_of_not_lt hn)
          specialize ha' n
          rwa [abs_of_nonpos, ge_iff_le, le_neg] at ha'
          by_contra!
          rw [abs_of_pos this] at ha'
          grw [abs_of_nonpos (by linarith), hN', _root_.sub_eq_add_neg, ha'] at hN
          grind
      . exact hcauchy
      . simp_rw [LIM_eq_LIM ha hcauchy, Sequence.equiv_iff, a']
        intro ε hε
        use N
        intro n hn
        simp [Nat.not_lt_of_le hn, le_of_lt hε]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  rw [not_and]
  rintro rfl
  simp_rw [isPos_def, not_exists, not_and]
  intro x hx hx'
  exact lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayPos hx) hx' |>.symm

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  rw [not_and]
  rintro rfl
  simp_rw [isNeg_def, not_exists, not_and]
  intro x hx hx'
  exact lim_of_boundedAwayZero (BoundedAwayZero.boundedAwayNeg hx) hx' |>.symm

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  rw [not_and]
  simp_rw [isPos_def, isNeg_def, not_exists, not_and]
  rintro ⟨x₁, ⟨c₁, hc₁, hx₁⟩, hx₁', rfl⟩ x₂ ⟨c₂, hc₂, hx₂⟩ hx₂'
  simp only [LIM_eq_LIM hx₁' hx₂', Sequence.equiv_iff, not_forall, not_exists, not_le]
  use c₁, hc₁
  intro n
  use n, le_rfl
  specialize hx₁ n
  specialize hx₂ n
  grw [abs_of_nonneg (by linarith), hx₁, _root_.sub_eq_add_neg, ←le_neg_of_le_neg hx₂]
  grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  simp_rw [isNeg_def, isPos_def]
  constructor
  . rintro ⟨a, ⟨c, hc, ha⟩, ha', rfl⟩
    use -a
    and_intros
    . use c, hc
      simpa [le_neg]
    . exact Sequence.IsCauchy.neg _ ha'
    . exact neg_LIM _ ha'
  . rintro ⟨a, ⟨c, hc, ha⟩, ha', hx⟩
    rw [neg_eq_iff_eq_neg] at hx
    subst x
    use -a
    and_intros
    . use c, hc
      simpa [le_neg]
    . exact Sequence.IsCauchy.neg _ ha'
    . exact neg_LIM _ ha'

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  simp_rw [isPos_def, boundedAwayPos_def] at hx hy ⊢
  obtain ⟨a, ⟨c, hc, ha⟩, ha', rfl⟩ := hx
  obtain ⟨b, ⟨d, hd, hb⟩, hb', rfl⟩ := hy
  use a + b
  and_intros
  . use c + d, by positivity
    intro n
    specialize ha n
    specialize hb n
    grw [Pi.add_apply, ha, hb]
  . exact Sequence.IsCauchy.add ha' hb'
  . exact LIM_add ha' hb'

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  simp_rw [isPos_def, boundedAwayPos_def] at hx hy ⊢
  obtain ⟨a, ⟨c, hc, ha⟩, ha', rfl⟩ := hx
  obtain ⟨b, ⟨d, hd, hb⟩, hb', rfl⟩ := hy
  use a * b
  and_intros
  . use c * d, by positivity
    intro n
    specialize ha n
    specialize hb n
    grw [Pi.mul_apply, ha, hb]
    grind
  . exact Sequence.IsCauchy.mul ha' hb'
  . exact LIM_mul ha' hb'

theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  simp_rw [isPos_def, boundedAwayPos_def]
  constructor
  . intro ⟨a, ⟨c, hc, ha⟩, ha', hq⟩
    rw [ratCast_def, LIM_eq_LIM (Sequence.IsCauchy.const q) ha', Sequence.equiv_iff] at hq
    obtain ⟨N, hq⟩ := hq (c / 2) (by positivity)
    specialize hq N le_rfl
    specialize ha N
    by_contra!
    grw [abs_of_nonpos (by grind), neg_sub, ha] at hq
    linarith
  . intro hq
    use fun _ ↦ q
    and_intros
    . use q, hq
      simp
    . exact Sequence.IsCauchy.const q
    . rw [ratCast_def]

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  simp_rw [neg_iff_pos_of_neg, neg_ratCast, ←Left.neg_pos_iff]
  exact pos_of_coe (-q)

open Classical in
/-- Need to use classical logic here because isPos and isNeg are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by rw [←neg_sub, ←neg_iff_pos_of_neg]; apply lt_iff
theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by simp [Eq.comm, le_iff]

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  simp_rw [←sub_neg (a := q), lt_iff, ratCast_sub, neg_of_coe]

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by simp [gt_iff]
theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by simp [lt_iff]

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  rw [gt_iff, lt_iff, ←sub_eq_zero, ←or_assoc, or_comm]
  exact trichotomous _

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]
  exact not_pos_neg _

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, ←sub_eq_zero, and_comm]
  exact not_zero_pos _

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, ←sub_eq_zero, and_comm]
  exact not_zero_neg _

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by rfl

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [antisymm, gt_iff] at hxy hyz ⊢
  rw [show z - x = (z - y) + (y - x) by simp]
  exact pos_add hyz hxy

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [antisymm, gt_iff] at hxy ⊢
  simpa

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢; convert pos_mul hxy hz using 1; ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  simp_rw [mul_comm, le_iff] at hxy ⊢
  by_cases h : x = y
  . right; rw [h]
  . left; simp only [h, or_false] at hxy
    exact mul_lt_mul_right hxy hz

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  rw [neg_iff_pos_of_neg] at hy ⊢
  rw [neg_mul_eq_mul_neg]
  exact pos_mul hx hy

open Classical in
/--
  (Not from textbook) Real has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by simp [le_iff]
  le_trans := by
    intro x y z hxy hxz
    by_cases x = y
    . subst x; assumption
    . by_cases y = z
      . subst y; assumption
      . simp_all only [le_iff, or_false]
        left; exact lt_trans hxy hxz
  lt_iff_le_not_ge := by
    intro x y
    constructor
    . intro h
      have h₁ := not_and'.mp (not_gt_and_lt x y) h
      have h₂ := not_and.mp (not_lt_and_eq x y) h
      grind [le_iff]
    . intro ⟨h₁, h₂⟩
      rw [le_iff, not_or, Eq.comm] at h₂
      simpa [le_iff, h₂] using h₁
  le_antisymm := by
    intro x y h₁ h₂
    by_contra! h
    simp only [le_iff, h, h.symm, or_false, antisymm] at h₁ h₂
    grind [not_gt_and_lt]
  le_total := by
    intro x y
    rcases trichotomous' x y with (h | h | h) <;> grind [le_iff]
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) Linear Orders come with a definition of absolute value |.|
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  dsimp [_root_.abs, abs]
  rcases x.trichotomous with (h | h | h)
  . have h₁ := not_and.mp (not_zero_pos x) h
    have h₂ := not_and.mp (not_zero_neg x) h
    simp_all
  . simp only [h, ↓reduceIte, sup_eq_left]
    rw [←ge_iff_le, ge_iff, gt_iff, sub_neg_eq_add]
    left; exact pos_add h h
  . have h₁ := not_and'.mp (not_pos_neg x) h
    have h₂ := neg_iff_pos_of_neg x |>.mp h
    simp only [h, h₁, ↓reduceIte, sup_eq_right]
    rw [←ge_iff_le, ge_iff, gt_iff, sub_eq_add_neg]
    left; exact pos_add h₂ h₂

/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [div_eq_mul_inv]
  exact pos_mul hx (inv_of_pos hy)

theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) Real has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro x y h c
    simp_rw [add_comm]
    by_cases h' : x = y
    . subst x; exact le_rfl
    . exact add_lt_add_right c (lt_of_le_of_ne h h') |> le_of_lt
  add_le_add_right := by
    intro x y h c
    by_cases h' : x = y
    . subst x; exact le_rfl
    . exact add_lt_add_right c (lt_of_le_of_ne h h') |> le_of_lt
  mul_lt_mul_of_pos_left := by
    intro x y z hxy hz
    simp_rw [gt_iff, sub_zero] at hz
    simp_rw [mul_comm]
    exact mul_lt_mul_right hxy hz
  mul_lt_mul_of_pos_right := by
    intro x y z hxy hz
    simp_rw [gt_iff, sub_zero] at hz
    exact mul_lt_mul_right hxy hz
  le_of_add_le_add_left := by
    intro x y z h
    simpa [le_iff, gt_iff] using h
  zero_le_one := by
    simp_rw [le_iff, gt_iff, sub_zero, show (1 : Real) = (1 : ℚ) by norm_num, pos_of_coe]
    simp

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  have hacauchy : (fun n : ℕ ↦ 1 + 1/((n:ℚ) + 1) : Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    use ⌊ε⁻¹⌋₊
    intro n hn m hm
    simp_rw [one_div, Section_4_3.dist_eq, add_sub_add_left_eq_sub]
    wlog hnm : n ≤ m generalizing n m
    . rw [←neg_sub, abs_neg]
      exact this m hm n hn (not_le.mp hnm |> le_of_lt)
    rw [abs_of_nonneg (by
      rw [sub_nonneg, inv_le_inv₀ (by positivity) (by positivity)]
      norm_cast; linarith)]
    field_simp
    rw [div_le_comm₀ (by positivity) hε, div_eq_mul_inv]
    grw [Nat.lt_floor_add_one ε⁻¹, hn]
    nth_rw 2 [mul_comm]
    gcongr; linarith; simpa
  have hbcauchy : (fun n : ℕ ↦ 1 - 1/((n:ℚ) + 1) : Sequence).IsCauchy := by
    rw [Sequence.IsCauchy.coe]
    intro ε hε
    use ⌊ε⁻¹⌋₊
    intro n hn m hm
    simp_rw [one_div, Section_4_3.dist_eq, sub_sub_sub_cancel_left]
    wlog hnm : m ≤ n generalizing n m
    . rw [←neg_sub, abs_neg]
      exact this m hm n hn (not_le.mp hnm |> le_of_lt)
    rw [abs_of_nonneg (by
      rw [sub_nonneg, inv_le_inv₀ (by positivity) (by positivity)]
      norm_cast; linarith)]
    field_simp
    rw [div_le_comm₀ (by positivity) hε, div_eq_mul_inv]
    grw [Nat.lt_floor_add_one ε⁻¹, hm]
    nth_rw 2 [mul_comm]
    gcongr; linarith; simpa
  and_intros
  . exact hacauchy
  . exact hbcauchy
  . intro n
    simp [sub_lt_iff_lt_add, add_assoc, lt_add_iff_pos_right]
    positivity
  . rw [not_lt, le_iff]
    right; rw [LIM_eq_LIM hacauchy hbcauchy, Sequence.equiv_iff]
    intro ε hε
    use 2 * ⌊ε⁻¹⌋₊ + 1
    intro n hn
    ring_nf
    rw [abs_of_nonneg (by positivity), ←le_mul_inv_iff₀' (by positivity), ←mul_inv_le_iff₀' hε, inv_inv]
    grw [Nat.lt_floor_add_one ε⁻¹, hn]
    simp [mul_add, add_comm, ←add_assoc, one_add_one_eq_two]

/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  simp_rw [gt_iff, isPos_def, boundedAwayPos_def] at hxy
  obtain ⟨c, ⟨d, hd, hd'⟩, hc, hxy⟩ := hxy
  obtain ⟨a, ha, rfl⟩ := eq_lim x
  set b := a + c
  obtain rfl : y = LIM b := by unfold b; rw [←LIM_add ha hc, ←hxy, add_sub_cancel]
  have hb : (b : Sequence).IsCauchy := Sequence.IsCauchy.add ha hc
  have hN := ha; have hM := hb
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at hN hM
  obtain ⟨N, hN⟩ := hN (d / 4) (by positivity)
  obtain ⟨M, hM⟩ := hM (d / 4) (by positivity)
  let K := max N M
  let q := a K + d / 2
  use q
  constructor
  . simp_rw [gt_iff, ratCast_def, LIM_sub (Sequence.IsCauchy.const q) ha, isPos_def]
    let w (n : ℕ) : ℚ := if K ≤ n then q - a n else d / 4
    use w
    have hw : (w : Sequence).IsCauchy := by
      simp_rw [w, Sequence.IsCauchy.coe] at ha ⊢
      peel ha with ε hε hJ
      obtain ⟨J, hJ⟩ := hJ
      use max J K
      intro n hn m hm
      specialize hJ n (by omega) m (by omega)
      simp_rw [Section_4_3.dist_eq] at hJ ⊢
      rw [←neg_sub, abs_neg] at hJ
      simp_all
    and_intros
    . use d / 4, by positivity
      intro n
      simp only [ge_iff_le, q, w]
      split_ifs with hn
      . specialize hN K (by omega) n (by omega)
        replace hN := abs_le.mp hN |>.left
        grw [←sub_add_eq_add_sub, ←hN]
        ring_nf; simp
      . exact le_rfl
    . exact hw
    . simp_rw [LIM_eq_LIM (Sequence.IsCauchy.sub (Sequence.IsCauchy.const q) ha) hw,
          w, Sequence.equiv_iff, Pi.sub_apply]
      intro ε hε
      use K
      intro n hn
      simp_all [le_of_lt hε]
  . simp_rw [gt_iff, ratCast_def, LIM_sub hb (Sequence.IsCauchy.const q), isPos_def]
    let w (n : ℕ) : ℚ := if K ≤ n then b n - q else d / 4
    use w
    have hw : (w : Sequence).IsCauchy := by
      simp_rw [w, Sequence.IsCauchy.coe] at hb ⊢
      peel hb with ε hε hJ
      obtain ⟨J, hJ⟩ := hJ
      use max J K
      intro n hn m hm
      specialize hJ n (by omega) m (by omega)
      simp_rw [Section_4_3.dist_eq] at hJ ⊢
      simp_all
    and_intros
    . use d / 4, by positivity
      intro n
      simp only [ge_iff_le, q, w]
      split_ifs with hn
      . specialize hM K (by omega) n (by omega)
        replace hM := abs_le.mp hM |>.right
        replace hM : b K - d / 4 ≤ b n := by linarith
        have : b K - a K = c K := by simp [b]
        grw [←hM, sub_add_eq_sub_sub, sub_right_comm (b K), this, hd' K]
        linarith
      . exact le_rfl
    . exact hw
    . simp_rw [LIM_eq_LIM (Sequence.IsCauchy.sub hb (Sequence.IsCauchy.const q)) hw,
          w, Sequence.equiv_iff, Pi.sub_apply]
      intro ε hε
      use K
      intro n hn
      simp_all [le_of_lt hε]

theorem Real.LIM_eq_LIM' (h : Sequence.Equiv a b) : LIM a = LIM b := by
  by_cases ha : (a : Sequence).IsCauchy
  . have hb := Sequence.isCauchy_of_equiv h |>.mp ha
    rwa [LIM_eq_LIM ha hb]
  . have hb := Sequence.isCauchy_of_equiv h |>.not |>.mp ha
    apply Quotient.sound
    simp [ha, hb]

def Sequence.replace (a : ℕ → ℚ) (N : ℕ) (b : ℕ → ℚ) : ℕ → ℚ := fun n ↦ if N ≤ n then a n else b n

lemma Sequence.equiv_replace (a : ℕ → ℚ) (N : ℕ) (b : ℕ → ℚ) : Equiv a (replace a N b) := by
  rw [equiv_iff]
  intro ε hε
  use N
  intro n hn
  simp [replace, hn, le_of_lt hε]

lemma Sequence.IsCauchy.replace {a : ℕ → ℚ} (ha : (a : Sequence).IsCauchy) (N : ℕ) (b : ℕ → ℚ) : Sequence.IsCauchy (replace a N b) := by
  have := equiv_replace a N b
  exact Sequence.isCauchy_of_equiv this |>.mp ha

lemma Real.LIM_eq_replace (a : ℕ → ℚ) (N : ℕ) (b : ℕ → ℚ) : LIM a = LIM (Sequence.replace a N b) := by
  apply LIM_eq_LIM'
  exact Sequence.equiv_replace a N b

lemma Real.approx (x : Real) : ∀ ε > 0, ∃ (p q : ℚ), p ≤ x ∧ x ≤ q ∧ q = p + ε := by
  intro ε hε
  obtain ⟨a, ha, rfl⟩ := eq_lim x
  obtain ⟨N, hN⟩ := by simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha; exact ha (ε / 2) (by positivity)
  use a N - ε / 2, a N + ε / 2
  let a' := Sequence.replace a N (fun _ ↦ a N)
  observe ha' : (a' : Sequence).IsCauchy
  observe haa' : LIM a = LIM a'
  simp_rw [haa', ratCast_def]
  and_intros
  . apply LIM_mono (Sequence.IsCauchy.const _) ha'
    intro n
    rw [Sequence.replace]
    split_ifs with hn
    . have han := hN N le_rfl n hn |> le_of_abs_le
      rwa [sub_le_comm]
    . linarith
  . apply LIM_mono ha' (Sequence.IsCauchy.const _)
    intro n
    rw [Sequence.replace]
    split_ifs with hn
    . have han := hN n hn N le_rfl |> le_of_abs_le
      rwa [←sub_le_iff_le_add']
    . linarith
  . grind

lemma Real.IsPos_iff_zero_lt (x : Real) : x.IsPos ↔ 0 < x := by simp [gt_iff]

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  apply existsUnique_of_exists_of_unique
  . have ⟨p, q, hp, hq, hpq⟩ := approx x 1 (by decide)
    let n := ⌊p⌋
    let m := ⌊q⌋
    have hn := Int.floor_eq_iff.mp (refl n)
    have hm := Int.floor_eq_iff.mp (refl m)
    have hnm : m = n + 1 := by
      qify; simp [m, n, hpq, ←Int.self_sub_fract]
    by_cases hmx : m ≤ x
    . use m, hmx
      apply lt_of_le_of_lt hq
      exact_mod_cast hm.right
    . use n
      constructor
      . apply le_trans _ hp
        exact_mod_cast hn.left
      . rw [not_le, hnm] at hmx
        exact_mod_cast hmx
  . intro n m hn hm
    by_contra! hnm
    wlog hnm : n < m generalizing n m
    . rw [not_lt] at hnm
      observe hnm : m < n
      exact this m n hm hn (ne_of_lt hnm) hnm
    have := lt_of_le_of_lt hm.left hn.right
    norm_cast at this
    grind

/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  have hx' := inv_of_pos hx
  obtain ⟨N, hN⟩ := exists_rat_le_and_nat_ge hx' |>.right
  use N
  constructor
  . exact_mod_cast lt_trans (by simpa [gt_iff] : 0 < x⁻¹) hN |> gt_iff_lt.mpr
  . exact inv_lt_of_inv_lt₀ (by simpa [gt_iff]) hN

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  conv_lhs => rw [abs_sub_lt_iff, sub_lt_iff_lt_add, add_comm, sub_lt_comm, and_comm]

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  conv_lhs => rw [abs_sub_le_iff, sub_le_iff_le_add, add_comm, sub_le_comm, and_comm]

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor
  . contrapose!
    intro h
    apply sub_pos_of_lt at h
    use (x - y) / 2, div_of_pos (by rwa [IsPos_iff_zero_lt])
        (by simp [IsPos_iff_zero_lt]) |> (IsPos_iff_zero_lt _).mp
    rwa [←sub_pos, sub_add_eq_sub_sub, sub_half, div_pos_iff_of_pos_right (by simp)]
  . intro h ε hε
    grw [h, le_add_iff_nonneg_right, hε]

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor
  . intro h
    have hxy : x ≤ y := by rw [←le_add_eps_iff]; peel h; apply le_of_abs_le at this; linarith
    have hyx : y ≤ x := by rw [←le_add_eps_iff]; peel h; apply neg_le_of_abs_le at this; linarith
    linarith
  . rintro rfl ε hε
    simp [le_of_lt hε]

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by
  by_contra! hxy
  have ⟨p, hp⟩ := rat_between hxy
  let b := (fun _ ↦ p) - a
  have hp_c := Sequence.IsCauchy.const p
  have hb_c : (b : Sequence).IsCauchy := Sequence.IsCauchy.sub hp_c hcauchy
  have hb : ∀ n, 0 ≤ b n := by
    simp_rw [b, Pi.sub_apply, sub_nonneg]
    peel h with n hn
    exact_mod_cast le_trans hn (le_of_lt hp.left)
  have hLIMb := LIM_of_nonneg hb hb_c
  simp_rw [b, ←LIM_sub hp_c hcauchy, ←ratCast_def, sub_nonneg] at hLIMb
  grind

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
  let b := -a
  have hb_c := Sequence.IsCauchy.neg a hcauchy
  have hb : ∀ n, b n ≤ -x := by peel h with n hn; simpa [b]
  have := LIM_of_le hb_c hb
  simpa [←neg_LIM a hcauchy] using this

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  rw [max_eq, min_eq]
  rcases trichotomous' x y with (h | h | h)
  . simp [le_of_lt h]
  . simp [not_le_of_gt h]
  . simp [h]

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  simp [neg_max]

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  simp_rw [max_eq]
  rcases trichotomous' x y with (h | h | h)
  . simp [le_of_lt h, not_le_of_gt h]
  . simp [le_of_lt h, not_le_of_gt h]
  . simp [h]

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  simp_rw [max_eq, le_rfl, if_true]

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  simp_rw [max_eq]
  rcases trichotomous' x y with (h | h | h)
  . simp [le_of_lt h]
  . simp [not_le_of_gt h]
  . simp [h]

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  simp_rw [max_eq]
  rcases trichotomous' x y with (h | h | h)
  . simp [le_of_lt h, mul_lt_mul_right h hz |> not_lt_of_gt]
  . simp [not_le_of_gt h, mul_lt_mul_right h hz]
  . simp [h]

/- Additional exercise: What happens if z is negative? -/
theorem Real.max_mul' (x y :Real) {z:Real} (hz: z.IsNeg) : max (x * z) (y * z) = min x y * z := by
  rw [←neg_mul_neg, ←neg_mul_neg y, neg_min, neg_mul_comm _ z]
  have hnz := neg_iff_pos_of_neg z |>.mp hz
  exact max_mul _ _ hnz

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  rw [neg_min, max_comm, ←neg_min]

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  rw [neg_min, max_self, neg_neg]

/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  rw [neg_min, neg_add, neg_add, max_add, neg_add, ←neg_min, neg_neg]

/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  simp_rw [neg_min, neg_mul_eq_neg_mul, max_mul _ _ hz, neg_mul_eq_neg_mul]

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  simp_rw [max_eq, min_eq]
  rcases trichotomous' x y with (h | h | h)
  . simp [le_of_lt h, inv_of_gt hx hy h |> not_lt_of_gt]
  . simp [not_le_of_gt h, inv_of_gt hy hx h |> not_le_of_gt]
  . simp [h]

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  simp_rw [max_eq, min_eq]
  rcases trichotomous' x y with (h | h | h)
  . simp [not_le_of_gt h, inv_of_gt hx hy h |> not_le_of_gt]
  . simp [le_of_lt h, inv_of_gt hy hx h |> not_lt_of_gt]
  . simp [h]

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by simp [Monotone]

end Chapter5
