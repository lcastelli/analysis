import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of ℕ and ℤ.

- Equivalence with the Mathlib rationals `_root_.Rat` (or `ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers `ℕ` and integers `ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y h; symm at h; assumption
    trans := by
      intro x y z h₁ h₂
      have : x.numerator * z.denominator * y.numerator * y.denominator =
          z.numerator * x.denominator * y.numerator * y.denominator := by grind
      rw [Int.mul_eq_mul_right_iff y.nonzero, mul_eq_mul_right_iff] at this
      cases' this with h h
      . assumption
      . simp_rw [h, zero_mul, mul_eq_zero, zero_eq_mul, y.nonzero, or_false] at h₁ h₂
        simp_rw [h₁, h₂, zero_mul]
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [hb, hd, Setoid.r]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Decidability of equality. Hint: modify the proof of `DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the `Quotient` API.
-/
instance Rat.decidableEq : DecidableEq Rat :=
  (Quotient.recOnSubsingleton₂ · · fun x y ↦
    if h : x.numerator * y.denominator = y.numerator * x.denominator then
      isTrue (by simpa)
    else
      isFalse (by simpa))

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Setoid.r]
    calc
      _ = (a*b')*d*d' + b*b'*(c*d') := by ring
      _ = (a'*b)*d*d' + b*b'*(c'*d) := by rw [h3, h4]
      _ = _ := by ring
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨a₁, a₂, ha⟩ ⟨b₁, b₂, hb⟩ ⟨a₁', a₂', ha'⟩ ⟨b₁', b₂', hb'⟩ hab hab'
    simp_all [Setoid.r]; grind)

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨a₁, a₂, ha⟩ ⟨b₁, b₂, hb⟩ hab
    simp_all [Setoid.r])

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  rw [of_Nat_eq, coe_Nat_eq, coe_Nat_eq, add_eq _ _ (by decide) (by decide)]
  simp

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, add_eq _ _ (by decide) (by decide)]
  simp

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  rw [coe_Int_eq, coe_Int_eq, coe_Int_eq, mul_eq _ _ (by decide) (by decide)]
  simp

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a b hab
  simp_rw [coe_Int_eq] at hab
  rw [eq _ _ (by decide) (by decide)] at hab
  grind

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    intro ⟨a₁, a₂, ha⟩ ⟨b₁, b₂, hb⟩ hab
    rw [PreRat.eq] at hab
    simp_rw [Quotient.eq, Setoid.r]
    split_ifs <;> simp_all [mul_comm]
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms (by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring
) (by
  intro x
  obtain ⟨a, b, hb, rfl⟩ := eq_diff x
  rw [of_Nat_eq, add_eq _ _ (by grind) (by grind)]
  simp
) (by
  intro x
  obtain ⟨a, b, hb, rfl⟩ := eq_diff x
  rw [of_Nat_eq, neg_eq _ hb, add_eq _ _ hb hb, eq _ _ (by simpa) (by decide)]
  grind
)

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro x y
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    rw [add_eq _ _ hx₂ hy₂, add_eq _ _ hy₂ hx₂]
    ring_nf

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by
    intro x y
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    rw [mul_eq _ _ hx₂ hy₂, mul_eq _ _ hy₂ hx₂]
    ring_nf
  mul_assoc := by
    intro x y z
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    obtain ⟨z₁, z₂, hz₂, rfl⟩ := eq_diff z
    rw [mul_eq _ _ hx₂ hy₂, mul_eq _ _ (by simp [hx₂, hy₂]) hz₂]
    rw [mul_eq _ _ hy₂ hz₂, mul_eq _ _ hx₂ (by simp [hy₂, hz₂])]
    ring_nf
  one_mul := by
    intro x
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    rw [of_Nat_eq, mul_eq _ _ (by decide) hx₂]
    ring_nf
  mul_one := by
    intro x
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    rw [of_Nat_eq, mul_eq _ _ hx₂ (by decide)]
    ring_nf

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by
    intro x y z
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    obtain ⟨z₁, z₂, hz₂, rfl⟩ := eq_diff z
    rw [add_eq _ _ hy₂ hz₂, mul_eq _ _ hx₂ (by simp_all), mul_eq _ _ hx₂ hy₂,
        mul_eq _ _ hx₂ hz₂, add_eq _ _ (by simp_all) (by simp_all), eq _ _ (by simp_all)]
    ring_nf; simp_all
  right_distrib := by
    intro x y z
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    obtain ⟨z₁, z₂, hz₂, rfl⟩ := eq_diff z
    rw [add_eq _ _ hx₂ hy₂, mul_eq _ _ (by simp_all) hz₂, mul_eq _ _ hx₂ hz₂,
        mul_eq _ _ hy₂ hz₂, add_eq _ _ (by simp_all) (by simp_all), eq _ _ (by simp_all)]
    ring_nf; simp_all
  zero_mul := by
    intro x
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    rw [of_Nat_eq, mul_eq _ _ (by decide) hx₂, eq _ _ (by grind) (by decide)]
    grind
  mul_zero := by
    intro x
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    rw [of_Nat_eq, mul_eq _ _ hx₂ (by decide), eq _ _ (by grind) (by decide)]
    grind
  mul_assoc := by
    intro x y z
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    obtain ⟨z₁, z₂, hz₂, rfl⟩ := eq_diff z
    rw [mul_eq _ _ hx₂ hy₂, mul_eq _ _ (by simp_all) hz₂, mul_eq _ _ hy₂ hz₂,
        mul_eq _ _ hx₂ (by simp_all), eq _ _ (by simp_all) (by simp_all)]
    grind
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro x y hxy
  simp_rw [Rat.cast, RatCast.ratCast, eq x.num y.num
      (by simp [x.den_nz] : (x.den : ℤ) ≠ 0) (by simp [y.den_nz] : (y.den : ℤ) ≠ 0)] at hxy
  rwa [←Rat.normalize_self x, ←Rat.normalize_self y, Rat.normalize_eq_iff]

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by use 0, 1, by decide
  mul_inv_cancel := by
    intro x hx₁
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    rw [of_Nat_eq, Int.cast_ofNat_Int, ne_eq, eq _ _ hx₂ (by decide), mul_one, zero_mul] at hx₁
    rw [inv_eq _ hx₂, mul_eq _ _ hx₂ hx₁, of_Nat_eq, eq _ _ (by simp_all) (by decide)]
    grind
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by decide

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by simp
  map_mul' := by simp

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
  rcases x₁.lt_trichotomy 0 with h₁ | h₁ | h₁
  . by_cases h₂ : x₂ < 0
    . right; left; use -x₁, -x₂
      simp [coe_Int_eq, div_eq, inv_eq, mul_eq _ _ _ hx₂, h₁, h₂]
    . right; right; use -x₁ // x₂
      constructor
      . use -x₁, x₂
        replace h₂ := lt_of_le_of_ne (not_lt.mp h₂) hx₂.symm
        simp [coe_Int_eq, div_eq, inv_eq, mul_eq _ _ _ hx₂, h₁, h₂]
      . simp
  . rw [of_Nat_eq, eq _ _ hx₂ (by decide)]; grind
  . by_cases h₂ : 0 < x₂
    . right; left; use x₁, x₂
      simp [coe_Int_eq, div_eq, inv_eq, mul_eq _ _ _ hx₂, h₁, h₂]
    . right; right; use x₁ // (-x₂)
      constructor
      . use x₁, -x₂
        replace h₂ := lt_of_le_of_ne (not_lt.mp h₂) hx₂
        simp [coe_Int_eq, div_eq, inv_eq, mul_eq _ _ _ hx₂, h₁, h₂]
        rw [neg_eq _ (by grind), eq _ _ (by grind) hx₂]; simp
      . rw [neg_eq _ (by grind), eq _ _ hx₂ (by grind)]; simp

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  intro ⟨h₁, ⟨a, b, ha, hb, h₂⟩⟩
  obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
  rw [of_Nat_eq, eq _ _ hx₂ (by decide), mul_one, Int.cast_ofNat_Int, zero_mul] at h₁
  rw [h₁, coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by grind),
      mul_eq _ _ (by decide) (by grind), eq _ _ hx₂ (by grind),
      zero_mul, mul_one, Eq.comm, Int.mul_eq_zero] at h₂
  grind

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  rintro ⟨rfl, ⟨x, ⟨⟨a, b, ha, hb, hab⟩, hx⟩⟩⟩
  rw [zero_eq_neg] at hx
  rw [hx, of_Nat_eq, coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by grind),
      mul_eq _ _ (by decide) (by grind), eq _ _ (by decide) (by grind)] at hab
  grind

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  rintro ⟨⟨a₁, a₂, ha₁, ha₂, hx₁⟩, ⟨y, ⟨⟨b₁, b₂, hb₁, hb₂, rfl⟩, hx₂⟩⟩⟩
  simp_rw [hx₂, coe_Int_eq, div_eq] at hx₁
  rw [inv_eq _ (by grind), mul_eq _ _ (by grind) (by grind), neg_eq _ (by grind),
      inv_eq _ (by grind), mul_eq _ _ (by grind) (by grind), eq _ _ (by grind) (by grind)] at hx₁
  simp_rw [mul_one, one_mul, neg_mul] at hx₁
  have h₁ : 0 < a₁ * b₂ := by simp_all
  have h₂ : 0 < b₁ * a₂ := by simp_all
  rw [←hx₁, lt_neg] at h₁
  grind

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  constructor
  . intro h
    have ⟨z, hz, hyx⟩ := lt_iff y x |>.mp h
    grind
  . intro h
    exact lt_iff y x |>.mp (by use x - y; grind)

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  constructor
  . intro h
    have := le_iff y x |>.mp h
    grind
  . intro h
    have := le_iff y x |>.mp (by rw [le_iff]; grind)
    simpa [le_iff]

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  rw [gt_iff, lt_iff, ←sub_eq_zero]
  have := trichotomous (x - y)
  grind

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y):= by
  rw [gt_iff, lt_iff]
  exact not_pos_and_neg _

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y):= by
  rw [gt_iff, ←sub_eq_zero]
  have := not_zero_and_pos (x - y)
  grind

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y):= by
  rw [lt_iff, ←sub_eq_zero]
  have := not_zero_and_neg (x - y)
  grind

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by
  rw [lt_iff, gt_iff]
  constructor
  . intro ⟨z, h, hz⟩; grind
  . intro h; use y - x; grind

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  simp_rw [lt_iff, isNeg] at hxy hyz ⊢
  obtain ⟨r, hr, hr'⟩ := hxy
  obtain ⟨s, hs, hs'⟩ := hyz
  use r + s
  constructor
  . obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := hr
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hs
    use a₁ * b₂ + b₁ * a₂, a₂ * b₂
    and_intros
    . observe : a₁ * b₂ > 0; observe : b₁ * a₂ > 0; grind
    . exact Int.mul_pos ha₂ hb₂
    . simp_rw [coe_Int_eq, div_eq]
      rw [inv_eq _ (by decide), inv_eq _ (by decide), inv_eq _ (by decide),
          mul_eq _ _ (by decide) (by grind), mul_eq _ _ (by decide) (by grind),
          mul_eq _ _ (by decide) (by grind [mul_eq_zero]), add_eq _ _ (by grind) (by grind)]
      grind
  . grind

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  obtain ⟨w, hw, hw'⟩ := hxy
  use w
  grind

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  obtain ⟨w, hw, hw'⟩ := hxy
  obtain ⟨w₁, w₂, hw₂, rfl⟩ := eq_diff w
  obtain ⟨z₁, z₂, hz₂, rfl⟩ := eq_diff z
  obtain ⟨a₁, a₂, ha₁, ha₂, hw⟩ := hw
  obtain ⟨b₁, b₂, hb₁, hb₂, hz⟩ := hz
  use (a₁ * b₁) / (a₂ * b₂)
  constructor
  . use a₁ * b₁, a₂ * b₂; simp_all
  . grind

lemma Rat.not_le {x y : Rat} : ¬(x ≤ y) ↔ y < x := by
  grind [le_iff, trichotomous', not_gt_and_lt]

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            rw [le_iff, lt_iff]
            by_cases h' : a * d = b * c
            . right; simp_rw [Quotient.eq, Setoid.r]; grind
            . left; use ⟦⟨b * c - a * d, b * d, by simp_all⟩⟧
              constructor
              . use b * c - a * d, b * d
                and_intros
                . exact lt_of_le_of_ne (by grind) (by grind)
                . exact lt_of_le_of_ne hbd (Int.mul_ne_zero hb hd).symm
                . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by decide), mul_eq _ _ (by decide) (by simp_all)]
                  grind
              . simp_rw [sub_eq_add_neg, (- ·), (· + ·), Add.add]
                simp_all [Setoid.r]; grind
          | isFalse h =>
            apply isFalse
            rw [not_le]
            use ⟦⟨a * d - b * c, b * d, by simp_all⟩⟧
            constructor
            . use a * d - b * c, b * d
              and_intros
              . exact lt_of_le_of_ne (by grind) (by grind)
              . exact lt_of_le_of_ne hbd (Int.mul_ne_zero hb hd).symm
              . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by decide), mul_eq _ _ (by decide) (by simp_all)]
                grind
            . simp_rw [sub_eq_add_neg, (- ·), (· + ·), Add.add]
              simp_all [Setoid.r]; grind
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            rw [_root_.not_le] at hbd
            rw [le_iff, lt_iff]
            by_cases h' : a * d = b * c
            . right; simp_rw [Quotient.eq, Setoid.r]; grind
            . left; use ⟦⟨a * d - b * c, -(b * d), by simp_all⟩⟧
              constructor
              . use a * d - b * c, -(b * d)
                and_intros
                . exact lt_of_le_of_ne (by grind) (by grind)
                . grind
                . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by decide), mul_eq _ _ (by decide) (by simp_all)]
                  grind
              . simp_rw [sub_eq_add_neg, (- ·), (· + ·), Add.add]
                simp_all [Setoid.r]; grind
          | isFalse h =>
            apply isFalse
            rw [_root_.not_le] at hbd h
            rw [not_le]
            use ⟦⟨b * c - a * d, -(b * d), by simp_all⟩⟧
            constructor
            . use b * c - a * d, -(b * d)
              and_intros
              . exact lt_of_le_of_ne (by grind) (by have := ne_of_lt h; grind)
              . exact lt_of_le_of_ne (by rw [Int.neg_nonneg]; grind) (by grind)
              . rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by decide), mul_eq _ _ (by decide) (by simp_all)]
                grind
            . simp_rw [sub_eq_add_neg, (- ·), (· + ·), Add.add]
              simp_all [Setoid.r]; grind
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := by simp [le_iff]
  le_trans := by grind [le_iff, lt_trans]
  lt_iff_le_not_ge := by grind [not_le, le_iff]
  le_antisymm := by grind [le_iff, not_lt_and_eq, not_gt_and_lt]
  le_total := by grind [trichotomous', le_iff]
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by grind [le_iff, add_comm, add_lt_add_right]
  add_le_add_right := by grind [le_iff, add_lt_add_right]
  mul_lt_mul_of_pos_left := by intro x y z hxy hz; simp_rw [mul_comm]; exact mul_lt_mul_right hxy (by rw [lt_iff, isNeg] at hz; grind)
  mul_lt_mul_of_pos_right := by intro x y z hxy hz; exact mul_lt_mul_right hxy (by rw [lt_iff, isNeg] at hz; grind)
  le_of_add_le_add_left := by
    intro x y z h
    rw [le_iff]
    rcases h with ⟨w, hw⟩ | h
    . left; use w; grind
    . grind
  zero_le_one := by decide

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  have ⟨w, ⟨w₁, w₂, hw'⟩, hw⟩ := hxy
  obtain ⟨z, ⟨z₁, z₂, hz'⟩, rfl⟩ := hz
  use w * z
  constructor
  . use w₁ * z₁, w₂ * z₂; simp_all; grind
  . grind

/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    intro ⟨x₁, x₂, hx₂⟩ ⟨y₁, y₂, hy₂⟩ h; rw [div_eq_div_iff (by simpa) (by simpa)]; norm_cast)
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv n := by obtain ⟨n₁, n₂, hn₂, rfl⟩ := eq_diff n; simp_all [coe_Int_eq, div_eq, inv_eq, mul_eq]
  right_inv n := by simp [Rat.cast, RatCast.ratCast, ←Rat.divInt_eq_div]

/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by
    intro x y
    by_cases h₁ : x = y
    . grind
    . obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
      obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
      rw [eq _ _ hx₂ hy₂] at h₁
      simp [_root_.Rat.le_iff, equivRat, hx₂, hy₂, le_iff, lt_iff, Setoid.r,
          sub_eq_add_neg, neg_eq, add_eq, isNeg, isPos, ←Rat.divInt_eq_div]
      have ⟨c, hc₁, hc₂⟩ := Rat.num_den_mk hx₂ (refl (Rat.divInt x₁ x₂))
      have ⟨d, hd₁, hd₂⟩ := Rat.num_den_mk hy₂ (refl (Rat.divInt y₁ y₂))
      have hc : c ≠ 0 := by grind
      have hd : d ≠ 0 := by grind
      set x' := Rat.divInt x₁ x₂
      set y' := Rat.divInt y₁ y₂
      constructor
      . intro h; left
        use (y'.num * x'.den - x'.num * y'.den) // (x'.den * y'.den)
        constructor
        . use y'.num * x'.den - x'.num * y'.den, lt_of_le_of_ne (by grind) (by grind)
          use x'.den * y'.den, by norm_cast; simp_rw [←Nat.ne_zero_iff_zero_lt, Nat.mul_ne_zero_iff]; grind
          rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by decide), mul_eq _ _ (by decide) (by simp),
              eq _ _ (by simp) (by simp)]
          grind
        . rw [neg_eq _ (by simp_all), hc₁, hc₂, hd₁, hd₂, eq _ _ (by simp_all) (by simp_all)]
          grind
      . intro h
        simp_rw [h₁, or_false] at h
        obtain ⟨r, ⟨a, ha, b, hb, rfl⟩, hab⟩ := h
        rw [coe_Int_eq, coe_Int_eq, div_eq, inv_eq _ (by decide), mul_eq _ _ (by decide) (by grind),
            neg_eq _ (by grind), eq _ _ (by simp_all) (by grind)] at hab
        rw [hc₁, hc₂, hd₁, hd₂] at hab
        replace hab : (x'.num * y'.den - x'.den * y'.num) * b * (c * d) = -(x'.den * y'.den * a) * (c * d) := by grind
        apply mul_right_cancel₀ (by grind) at hab
        have : x'.den * y'.den * a > 0 := mul_pos (by simp [←Nat.ne_zero_iff_zero_lt]) ha
        rw [gt_iff_lt, ←Int.neg_lt_zero_iff, ←hab] at this
        have := neg_of_mul_neg_left this (by grind)
        grind

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by
    intro x y
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    simp [hx₂, hy₂, add_eq]
    norm_cast
    rw [Rat.divInt_add_divInt _ _ hx₂ hy₂]
    grind
  map_mul' := by
    intro x y
    obtain ⟨x₁, x₂, hx₂, rfl⟩ := eq_diff x
    obtain ⟨y₁, y₂, hy₂, rfl⟩ := eq_diff y
    simp [hx₂, hy₂, mul_eq]
    norm_cast
    rw [Rat.divInt_mul_divInt']

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
