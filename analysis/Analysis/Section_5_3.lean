import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a Cauchy sequence.-/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
  rw [equiv_iff] at hab hbc ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hab (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hbc (ε / 2) (by positivity)
  use max N₁ N₂
  intro n hn
  specialize hN₁ n (by grind)
  specialize hN₂ n (by grind)
  calc
    _ = |(a n - b n) + (b n - c n)| := by simp
    _ ≤ |a n - b n| + |b n - c n| := by apply abs_add_le
    _ ≤ _ := by grw [hN₁, hN₂]; simp

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := by intro x; rw [Sequence.equiv_iff]; intro ε hε; use 0; intro n hn; rw [sub_self, abs_zero]; grind
     symm := by intro x y hxy; rw [Sequence.equiv_iff] at hxy ⊢; peel hxy; rwa [←neg_sub, abs_neg]
     trans := by intro a b c hab hbc; exact Sequence.equiv_trans hab hbc
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  rw [IsCauchy.coe]
  intro ε hε
  use 0
  simp_rw [zero_le, forall_const, Section_4_3.dist, sub_self, abs_zero]
  exact le_of_lt hε

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of 0 to `LIM a` when `a` is not Cauchy.
  This requires Classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *; rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  intro ε hε
  obtain ⟨M, hM₁, hM₂⟩ := isBounded_of_isCauchy ha
  obtain ⟨M', hM₁', hM₂'⟩ := isBounded_of_isCauchy hb
  by_cases h : M = 0 ∨ M' = 0
  . use 0, by simp
    intro n hn m hm
    lift n to ℕ using (by simpa)
    lift m to ℕ using (by simpa)
    have han := hM₂ n
    have ham := hM₂ m
    have hbn := hM₂' n
    have hbm := hM₂' m
    simp_rw [eval_coe] at han ham hbn hbm
    rw [from_eval _ (by grind), from_eval _ (by grind)]
    simp_rw [eval_coe, Rat.Close, Pi.mul_apply]
    apply h.elim <;> (intro hM; simp_all [le_of_lt])
  . rw [not_or, Eq.comm (b := 0), Eq.comm (b := 0)] at h
    replace hM₁ := lt_of_le_of_ne hM₁ h.left
    replace hM₁' := lt_of_le_of_ne hM₁' h.right
    obtain ⟨N, _, hN⟩ := ha (ε / 2 / M') (by positivity)
    obtain ⟨N', _, hN'⟩ := hb (ε / 2 / M) (by positivity)
    lift N to ℕ using (by simp_all)
    lift N' to ℕ using (by simp_all)
    use max N N', by simp_all
    intro n hn m hm
    simp_rw [n0_coe] at hn hm
    lift n to ℕ using (by grind)
    lift m to ℕ using (by grind)
    specialize hN n (by simp_all) m (by simp_all)
    specialize hN' n (by simp_all) m (by simp_all)
    specialize hM₂ m
    specialize hM₂' n
    rw [from_eval _ (le_of_max_le_right hn), from_eval _ (le_of_max_le_right hm)]
    simp_rw [sup_le_iff] at hn hm
    rw [from_eval _ hn.right.left, from_eval _ hm.right.left] at hN
    rw [from_eval _ hn.right.right, from_eval _ hm.right.right] at hN'
    simp_rw [eval_coe, Pi.mul_apply] at hN hN' hM₂ hM₂' ⊢
    have := Section_4_3.close_mul_mul' hN hN'
    rw [Rat.Close] at this ⊢
    grw [hM₂, hM₂', div_mul_cancel₀ _ (by grind), div_mul_cancel₀ _ (by grind), add_halves] at this
    exact this

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  rw [equiv_iff] at haa' ⊢
  simp_rw [Pi.mul_apply, ←sub_mul, abs_mul]
  intro ε hε
  obtain ⟨M, hM₁, hM₂⟩ := isBounded_of_isCauchy hb
  by_cases h : M = 0
  . use 0
    intro n _
    specialize hM₂ n
    rw [eval_coe, h, abs_nonpos_iff] at hM₂
    rw [hM₂, abs_zero, mul_zero]
    exact le_of_lt hε
  . replace hM₁ := lt_of_le_of_ne hM₁ (by grind)
    specialize haa' (ε / M) (by positivity)
    peel haa' with n n' hnn' hεM
    specialize hM₂ n'
    rw [eval_coe] at hM₂
    grw [hεM, hM₂, div_mul_cancel₀ _ h]

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _
  rw [dif_pos]

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  simp_rw [ratCast_def, LIM_eq_LIM (Sequence.IsCauchy.const q) (Sequence.IsCauchy.const r), Sequence.equiv_iff]
  constructor
  . intro h
    simp_rw [Section_4_3.eq_if_close, Rat.Close]
    peel h
    obtain ⟨N, this⟩ := this
    exact this N (by simp)
  . intro h ε hε
    rw [h, sub_self, abs_zero]
    use 0
    grind

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

/-- ratCast distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  have ha := Sequence.IsCauchy.const a
  have hb := Sequence.IsCauchy.const b
  simp_rw [ratCast_def, LIM_add ha hb]
  congr

/-- ratCast distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  have ha := Sequence.IsCauchy.const a
  have hb := Sequence.IsCauchy.const b
  simp_rw [ratCast_def, LIM_mul ha hb]
  congr

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

/-- ratCast commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  simp_rw [instNeg, show -a = -1 * a by simp, ratCast_mul]

/-- It may be possible to omit the Cauchy sequence hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  simp_rw [instNeg, ratCast_def, LIM_mul (Sequence.IsCauchy.const (-1:ℚ)) ha]
  congr
  ext x
  simp

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  rw [←neg_one_mul]
  exact Sequence.IsCauchy.mul (Sequence.IsCauchy.const (-1:ℚ)) ha

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
  AddGroup.ofLeftAxioms (by
    intro a b c
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    obtain ⟨b, hb, rfl⟩ := eq_lim b
    obtain ⟨c, hc, rfl⟩ := eq_lim c
    have hab := Sequence.IsCauchy.add ha hb
    have hbc := Sequence.IsCauchy.add hb hc
    rw [LIM_add ha hb, LIM_add hab hc, LIM_add hb hc, LIM_add ha hbc, add_assoc]
  ) (by
    intro a
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    rw [←LIM.zero, LIM_add (Sequence.IsCauchy.const 0) ha]
    congr; ext; simp
  ) (by
    intro a
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    have hn1 := Sequence.IsCauchy.const (-1)
    have hn1a := Sequence.IsCauchy.mul hn1 ha
    simp_rw [instNeg, ratCast_def, LIM_mul hn1 ha, LIM_add hn1a ha, ←LIM.zero]
    congr; ext; simp
  )

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
  rw [sub_eq_add_neg]
  exact add ha (neg _ hb)

/-- LIM distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
  have hnb := Sequence.IsCauchy.neg b hb
  rw [sub_eq_add_neg, neg_LIM b hb, LIM_add ha hnb, _root_.sub_eq_add_neg]

/-- ratCast distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  rw [sub_eq_add_neg, neg_ratCast, ratCast_add, _root_.sub_eq_add_neg]

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro a b
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    obtain ⟨b, hb, rfl⟩ := eq_lim b
    rw [LIM_add ha hb, LIM_add hb ha, add_comm]

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by
    intro a b
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    obtain ⟨b, hb, rfl⟩ := eq_lim b
    rw [LIM_mul ha hb, LIM_mul hb ha, mul_comm]
  mul_assoc := by
    intro a b c
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    obtain ⟨b, hb, rfl⟩ := eq_lim b
    obtain ⟨c, hc, rfl⟩ := eq_lim c
    have hab := Sequence.IsCauchy.mul ha hb
    have hbc := Sequence.IsCauchy.mul hb hc
    rw [LIM_mul ha hb, LIM_mul hab hc, LIM_mul hb hc, LIM_mul ha hbc, mul_assoc]
  one_mul := by
    intro a
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    rw [show 1 = LIM fun _ ↦ 1 by rw [←ratCast_def 1]; rfl, LIM_mul (Sequence.IsCauchy.const 1) ha]
    congr; ext; simp
  mul_one := by
    intro a
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    rw [show 1 = LIM fun _ ↦ 1 by rw [←ratCast_def 1]; rfl, LIM_mul ha (Sequence.IsCauchy.const 1)]
    congr; ext; simp

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by
    intro a b c
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    obtain ⟨b, hb, rfl⟩ := eq_lim b
    obtain ⟨c, hc, rfl⟩ := eq_lim c
    have hbc := Sequence.IsCauchy.add hb hc
    have hab := Sequence.IsCauchy.mul ha hb
    have hac := Sequence.IsCauchy.mul ha hc
    rw [LIM_add hb hc, LIM_mul ha hbc, LIM_mul ha hb, LIM_mul ha hc, LIM_add hab hac, left_distrib]
  right_distrib := by
    intro a b c
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    obtain ⟨b, hb, rfl⟩ := eq_lim b
    obtain ⟨c, hc, rfl⟩ := eq_lim c
    have hab := Sequence.IsCauchy.add ha hb
    have hac := Sequence.IsCauchy.mul ha hc
    have hbc := Sequence.IsCauchy.mul hb hc
    rw [LIM_add ha hb, LIM_mul hab hc, LIM_mul ha hc, LIM_mul hb hc, LIM_add hac hbc, right_distrib]
  zero_mul := by
    intro a
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    rw [←Real.LIM.zero, LIM_mul (Sequence.IsCauchy.const 0) ha]
    congr; ext; simp
  mul_zero := by
    intro a
    obtain ⟨a, ha, rfl⟩ := eq_lim a
    rw [←Real.LIM.zero, LIM_mul ha (Sequence.IsCauchy.const 0)]
    congr; ext; simp
  mul_assoc := mul_assoc
  natCast_succ := by
    intro n
    simp_rw [instNatCast, show 1 = LIM fun _ ↦ 1 by rw [←ratCast_def 1]; rfl, ratCast_def,
        LIM_add (Sequence.IsCauchy.const n) (Sequence.IsCauchy.const 1)]
    congr; ext; simp
  intCast_negSucc := by
    intro n
    simp_rw [instIntCast, Nat.cast, NatCast.natCast, neg_ratCast]
    congr

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by simp_rw [ratCast_def, ←LIM.zero]
  map_one' := by simp_rw [ratCast_def, show 1 = LIM fun _ ↦ 1 by rw [←ratCast_def 1]; rfl]
  map_add' := by intro a b; rw [ratCast_add]
  map_mul' := by intro a b; rw [ratCast_mul]

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  simp_rw [not_exists, not_and, not_forall, not_le]
  intro c hc
  use ⌊c⁻¹⌋₊
  rw [abs_of_nonneg (zpow_nonneg (by decide) _), ←neg_sub, sub_neg_eq_add, zpow_neg]
  apply inv_lt_of_inv_lt₀ hc
  apply lt_of_lt_of_le (Nat.lt_floor_add_one c⁻¹)
  set c' := ⌊c⁻¹⌋₊
  norm_cast
  induction' c' with c' ih
  . decide
  . grw [←add_assoc, pow_add, pow_one, ←ih]
    grind

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  simp_rw [not_exists, not_and, not_forall, not_le]
  intro c hc
  use 0
  norm_num
  exact hc

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  simp_rw [not_exists, not_and, not_forall, not_le]
  intro M hM
  use ⌊M⌋₊
  rw [Sequence.eval_coe, abs_of_nonneg (by simp)]
  apply lt_of_lt_of_le (Nat.lt_floor_add_one M)
  set M' := ⌊M⌋₊
  norm_cast
  induction' M' with M' ih
  . decide
  . grw [pow_add, pow_one, ←ih]
    grind

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by
    intro j hj
    have := Section_4_3.dist_le (b n₀) (b j) 0
    grw [hb' n₀ hn₀ j hj, Section_4_3.dist_eq, Section_4_3.dist_eq,
        sub_zero, sub_zero, ←hx, ←sub_le_iff_le_add', sub_half] at this
    assumption
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by
    rw [Sequence.equiv_iff]
    intro ε hε
    use n₀
    intro n hn
    simp [a, Nat.not_lt_of_le hn, le_of_lt hε]
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by
  simp only [←LIM.zero, ne_eq, LIM_eq_LIM ha_cauchy (Sequence.IsCauchy.const 0),
      Sequence.equiv_iff, not_forall, not_exists, not_le]
  obtain ⟨c, hc, ha⟩ := ha
  use c / 2, by linarith
  intro n
  use n, le_rfl
  specialize ha n
  grw [sub_zero, ha, ←sub_pos, sub_half]
  positivity

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by congr; field_simp [ha' m, ha' n]; grind
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [instInv, hx, -Quotient.eq]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  obtain ⟨x, hx₁, hx₂, rfl⟩ := boundedAwayZero_of_nonzero hx
  rw [inv_def hx₂ hx₁, LIM_mul hx₁ (inv_isCauchy_of_boundedAwayZero hx₂ hx₁),
      show 1 = LIM fun _ ↦ 1 by rw [←ratCast_def 1]; rfl]
  congr; ext i
  rw [Pi.mul_apply, Pi.inv_apply, mul_inv_cancel₀]
  obtain ⟨c, hc, hx₂⟩ := hx₂
  grw [←hx₂ i] at hc
  apply ne_of_lt at hc
  rwa [ne_comm, abs_ne_zero] at hc

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  rw [mul_comm, self_mul_inv hx]

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by
    use 0, 1
    simp only [←LIM.zero, show 1 = LIM fun _ ↦ 1 by rw [←ratCast_def 1]; rfl, ne_eq,
        LIM_eq_LIM (Sequence.IsCauchy.const 0) (Sequence.IsCauchy.const 1), Sequence.equiv_iff,
        not_forall, not_exists, not_le]
    use 2⁻¹, by positivity
    intro n
    use n, le_rfl
    norm_num
  mul_inv_cancel := by intro x; exact self_mul_inv
  inv_zero := inv_zero
  ratCast_def := by
    intro q
    simp_rw [Nat.cast, NatCast.natCast, Int.cast, IntCast.intCast, div_eq, inv_ratCast, ratCast_mul, ←div_eq_mul_inv]
    congr
    nth_rw 1 [←Rat.num_div_den q]
  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  apply_fun (· * z⁻¹) at h
  simpa [mul_assoc, hz] using h

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  simp_rw [not_forall]
  use 0, 1, 0, rfl, by norm_num
  simp

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by
  specialize hab 1 (by decide)
  rwa [Sequence.isBounded_of_eventuallyClose hab] at ha

/--
  Same as `Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  rw [←LIM.zero, LIM_eq_LIM Sequence.IsCauchy.harmonic' (Sequence.IsCauchy.const 0), Sequence.equiv_iff]
  intro ε hε
  use ⌊ε⁻¹⌋₊
  intro n hn
  rw [sub_zero, abs_of_nonneg (by positivity), ←inv_eq_one_div, ←inv_le_comm₀ hε (by positivity)]
  grw [Nat.lt_floor_add_one ε⁻¹, hn]

end Chapter5
