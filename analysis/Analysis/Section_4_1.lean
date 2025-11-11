import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of ℕ.

- Equivalence with the Mathlib integers `_root_.Int` (or `ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y h; symm; exact h
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [Setoid.r] at *
    calc
      _ = (a+b') + (c+d') := by abel
      _ = (a'+b) + (c'+d) := by rw [h1,h2]
      _ = _ := by abel)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2; simp at h1 h2
    convert mul_congr _ _ <;> simpa
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  simp [←natCast_ofNat]

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
    simp_rw [PreInt.eq, Quotient.eq, Setoid.r] at h ⊢
    grind)

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms
    (by
      intro a b c
      obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
      obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
      obtain ⟨c₁, c₂, rfl⟩ := eq_diff c
      simp_rw [add_eq, eq]; grind)
    (by
      intro a; obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
      simp [ofNat_eq, add_eq])
    (by
      intro a; obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
      rw [ofNat_eq, neg_eq, add_eq, eq]; grind)

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
    simp_rw [add_eq, eq]; grind

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
    simp_rw [mul_eq]; grind
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by
    intro a; obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    simp_rw [ofNat_eq, mul_eq]; grind
  mul_one := by
    intro a; obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    simp_rw [ofNat_eq, mul_eq]; grind

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro a b c
    obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
    obtain ⟨c₁, c₂, rfl⟩ := eq_diff c
    simp only [add_eq, mul_eq]; grind
  right_distrib := by
    intro a b c
    obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
    obtain ⟨c₁, c₂, rfl⟩ := eq_diff c
    simp only [add_eq, mul_eq]; grind
  zero_mul := by
    intro a; obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    simp_rw [ofNat_eq, mul_eq]; grind
  mul_zero := by
    intro a; obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    simp_rw [ofNat_eq, mul_eq]; grind

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  simp_rw [natCast_eq, sub_eq, neg_eq, add_eq]; grind

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨ a₁, a₂, rfl ⟩ := eq_diff a
  obtain ⟨ b₁, b₂, rfl ⟩ := eq_diff b
  simp_rw [mul_eq, ofNat_eq, eq, add_zero, zero_add] at h ⊢
  rcases Nat.lt_trichotomy a₁ a₂ with ha | ha | ha
  . replace h : a₂ * b₂ - a₁ * b₂ = a₂ * b₁ - a₁ * b₁ := by grind
    replace h : (a₂ - a₁) * b₂ = (a₂ - a₁) * b₁ := by simpa [Nat.sub_mul]
    rw [Nat.mul_left_cancel_iff (by grind)] at h; grind
  . grind
  . replace h : a₁ * b₁ - a₂ * b₁ = a₁ * b₂ - a₂ * b₂ := by grind
    replace h : (a₁ - a₂) * b₁ = (a₁ - a₂) * b₂ := by simpa [Nat.sub_mul]
    rw [Nat.mul_left_cancel_iff (by grind)] at h; grind

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have := calc
    0 = a * c - b * c := by grind
    _ = (a - b) * c := by grind
  replace := mul_eq_zero this.symm
  grind

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  rw [lt_iff]
  constructor
  . intro ⟨⟨n, hn⟩, h⟩
    have := calc
      n = b - a := by grind
      _ ≠ 0 := by grind
    rw [←natCast_ofNat, ne_eq, natCast_inj] at this
    use n
  . intro ⟨n, hn, h⟩
    have : n = b - a := by grind
    rw [ne_eq, ←natCast_inj, this] at hn
    grind

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  obtain ⟨n, hn, rfl⟩ := lt_iff_exists_positive_difference _ _ |>.mp h
  rw [lt_iff_exists_positive_difference]
  grind

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  obtain ⟨n, hn, rfl⟩ := lt_iff_exists_positive_difference _ _ |>.mp hab
  obtain ⟨n', hn', rfl⟩ := lt_iff_exists_positive_difference _ _ |>.mp hc
  rw [lt_iff_exists_positive_difference]
  use n * n', Nat.mul_ne_zero hn hn'
  simp [right_distrib]

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  obtain ⟨n, hn, rfl⟩ := lt_iff_exists_positive_difference _ _ |>.mp h
  rw [lt_iff_exists_positive_difference]
  grind

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  obtain ⟨n, rfl⟩ := le_iff _ _ |>.mp h
  rw [le_iff]
  grind

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  obtain ⟨n, hn, rfl⟩ := lt_iff_exists_positive_difference _ _ |>.mp hab
  obtain ⟨n', hn', rfl⟩ := lt_iff_exists_positive_difference _ _ |>.mp hbc
  rw [lt_iff_exists_positive_difference]
  use n + n', (by grind)
  rw [Nat.cast_add]
  grind

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  rcases trichotomous (a - b) with h | ⟨n, hn, hn'⟩ | ⟨n, hn, hn'⟩
  . grind
  . left
    rw [gt_iff_lt, lt_iff_exists_positive_difference]
    grind
  . right; left
    rw [lt_iff_exists_positive_difference]
    use n; grind

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b):= by
  intro h
  simp_rw [gt_iff_lt, lt_iff_exists_positive_difference] at h
  obtain ⟨⟨n, hn₀, hn⟩, ⟨n', hn'₀, rfl⟩⟩ := h
  have := calc
    0 = a - a + n' + n := by grind
    _ = n' + n := by grind
  rw [←natCast_ofNat, ←Nat.cast_add, natCast_inj] at this
  grind

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  intro ⟨h₁, h₂⟩
  rw [gt_iff_lt, lt_iff] at h₁
  grind

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  intro ⟨h₁, h₂⟩
  rw [lt_iff] at h₁
  grind

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
        use k; simp_rw [natCast_eq, add_eq, eq]
        grind
      | isFalse h =>
        apply isFalse
        simp_rw [le_iff, natCast_eq, add_eq, eq]
        grind
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor
  . intro h; specialize h 0; grind
  . grind

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by intro a; rw [le_iff]; use 0; grind
  le_trans := by
    intro a b c h₁ h₂
    obtain ⟨n, rfl⟩ := h₁
    obtain ⟨n', rfl⟩ := h₂
    use n + n'; rw [Nat.cast_add]; grind
  lt_iff_le_not_ge := by
    intro a b
    constructor
    . intro h
      have h₁ := not_and.mp (not_lt_and_eq _ _) h
      have h₂ := not_and.mp (not_gt_and_lt _ _) h
      rw [lt_iff, not_and'] at h₂
      specialize h₂ fun p ↦ h₁ p.symm
      exact ⟨h.left, h₂⟩
    . rw [le_iff b, not_exists, lt_iff]
      intro ⟨h₁, h₂⟩
      specialize h₂ 0
      use h₁; grind
  le_antisymm := by
    intro a b hab hba
    rw [le_iff] at hab; obtain ⟨t₁, h⟩ := hab
    rw [le_iff] at hba; obtain ⟨t₂, rfl⟩ := hba
    rw [add_assoc, left_eq_add, ←natCast_ofNat, ←Nat.cast_add, natCast_inj, Nat.add_eq_zero] at h
    simp [h.left]
  le_total := by
    intro a b
    rcases trichotomous' a b with ⟨h, -⟩ | ⟨h, -⟩ | h
    . grind
    . grind
    . left; use 0; grind
  toDecidableLE := decidableRel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  grind

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use (0 ≤ ·)
  and_intros
  . use 0; simp
  . rintro a ⟨n, rfl⟩; use (n + 1); simp
  . intro h; specialize h ↑(-1)
    obtain ⟨n, hn⟩ := h
    rw [Eq.comm, ←sub_eq_zero, zero_add, sub_neg_eq_add,
        ←natCast_ofNat, ←natCast_ofNat, ←Nat.cast_add, natCast_inj] at hn
    contradiction

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  by_cases h' : n = 0
  . simp [h']
  . rw [Eq.comm] at h'
    replace h : 0 < n := ⟨h, h'⟩
    have := mul_lt_mul_of_pos_right h h
    rw [zero_mul] at this
    exact le_of_lt this

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  by_cases h: 0 ≤ n
  . exact sq_nonneg_of_pos n h
  . rw [not_le] at h; apply neg_gt_neg at h; rw [neg_zero] at h
    rw [←neg_mul_neg]
    exact sq_nonneg_of_pos _ (le_of_lt h)

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  obtain ⟨n', hn'⟩ := sq_nonneg n
  grind

/--
  Not in textbook: create an equivalence between Int and ℤ.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h; rw [PreInt.eq] at h; grind)
  invFun := (·)
  left_inv n := by
    obtain ⟨a, b⟩ := n
    simp_rw [Int.cast_sub, Int.cast_natCast, natCast_eq, sub_eq, neg_eq, add_eq, add_zero, zero_add]
    rfl
  right_inv n := by
    cases n <;> rfl

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
    simp_rw [add_eq, Quotient.lift_mk]
    grind
  map_mul' := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
    simp_rw [mul_eq, Quotient.lift_mk]
    grind
  map_le_map_iff' := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := eq_diff b
    simp_rw [Quotient.lift_mk, le_iff, natCast_eq, add_eq, eq]
    constructor
    . intro h
      obtain ⟨n, hn⟩ := Int.exists_add_of_le h
      use n; grind
    . grind

end Section_4_1
