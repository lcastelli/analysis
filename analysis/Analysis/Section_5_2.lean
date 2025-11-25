import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  intro n hn _
  rw [Sequence.n0_coe] at hn
  simp_rw [Sequence.eval_coe_at_int, hn, if_true, Rat.Close, neg_one_pow_eq_ite]
  split_ifs with h
  . rw [abs_of_nonpos (by norm_num)]
    norm_num
  . rw [abs_of_nonneg (by norm_num)]
    norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  simp_rw [not_forall]
  use 0, by simp, 1, by simp
  rw [Rat.Close]
  norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  simp_rw [not_forall]
  use 0, by simp, 1, by simp
  rw [Rat.Close, abs_of_nonneg (by norm_num)]
  norm_num

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  simp_rw [eventuallyClose_def, closeSeq_def, Rat.Close]
  constructor
  . intro ⟨N, hN⟩
    use N.toNat
    intro n hn
    specialize hN n (by simp_all) (by simp_all)
    simpa [show N ≤ n by grind] using hN
  . intro ⟨N, hN⟩
    use N
    intro n hn _
    lift n to ℕ using (by omega)
    simp_all

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  simp_rw [Rat.closeSeq_def, not_forall, Rat.Close, not_le]
  use 0, by simp, by simp
  rw [abs_of_nonneg (by norm_num)]
  norm_num

example : (0.1:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  use 1
  intro n hn
  rw [add_sub_sub_cancel, ←two_mul, abs_of_nonneg (by positivity), ←neg_sub, sub_neg_eq_add,
      zpow_neg, ←div_eq_mul_inv, div_le_iff₀ (by positivity), show (0.1 : ℚ) = 10 ^ (-1 : ℤ) by norm_num,
      ←zpow_add₀ (by decide), neg_add_cancel_left, zpow_natCast]
  cases' n with n
  . contradiction
  rw [pow_add, pow_one]
  have := pow_pos (by decide : 0 < 10) n
  norm_cast
  omega

example : (0.01:ℚ).EventuallyClose ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  rw [Rat.eventuallyClose_iff]
  use 2
  intro n hn
  rw [add_sub_sub_cancel, ←two_mul, abs_of_nonneg (by positivity), ←neg_sub, sub_neg_eq_add,
      zpow_neg, ←div_eq_mul_inv, div_le_iff₀ (by positivity), show (0.01 : ℚ) = 10 ^ (-2 : ℤ) by norm_num,
      ←zpow_add₀ (by decide), ←add_assoc]
  replace hn := Nat.sub_add_cancel hn
  set n' := n - 2
  rw [←hn, Nat.cast_add, add_comm, ←add_assoc]
  norm_num
  norm_cast
  have := pow_pos (by decide : 0 < 10) n'
  omega

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  simp_rw [equiv_def, Rat.eventuallyClose_iff]

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [mul_assoc, ←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  revert a b
  suffices ∀ (a b: ℕ → ℚ), Equiv a b → (a : Sequence).IsCauchy → (b:Sequence).IsCauchy by
    intro a b h
    constructor
    . exact this a b h
    . apply this b a
      rw [equiv_iff] at h ⊢
      peel h
      rwa [←neg_sub, abs_neg]
  intro a b hab ha
  rw [equiv_iff] at hab
  simp_rw [isCauchy_def, Rat.eventuallySteady_def, Rat.steady_def, Rat.Close, n0_coe] at ha ⊢
  intro ε hε
  obtain ⟨N₁, hab⟩ := hab (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂, ha⟩ := ha (ε / 3) (by positivity)
  lift N₂ to ℕ using hN₂
  use max N₁ N₂, by omega
  rw [max_eq_right (by omega)]
  intro n hn m hm
  specialize ha n (by omega) m (by omega)
  simp_rw [show n ≥ max 0 ↑N₂ by omega, show m ≥ max 0 ↑N₂ by omega, dite_eq_ite, if_true] at ha
  simp_rw [hn, hm, dite_eq_ite, if_true]
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  simp_rw [eval_coe] at ha ⊢
  calc
    _ = |-(a n - b n) + (a n - a m) + (a m - b m)| := by grind
    _ ≤ |-(a n - b n) + (a n - a m)| + |(a m - b m)| := by apply abs_add_le
    _ ≤ |-(a n - b n)| + |(a n - a m)| + |(a m - b m)| := by gcongr; apply abs_add_le
    _ ≤ |(a n - b n)| + |(a n - a m)| + |(a m - b m)| := by rw [abs_neg]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr; exact hab n (by omega); exact hab m (by omega)
    _ = ε := by grind

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  revert a b
  suffices ∀ (a b: ℕ → ℚ), ε.EventuallyClose a b → (a : Sequence).IsBounded → (b:Sequence).IsBounded by
    intro a b h
    constructor
    . exact this a b h
    . apply this b a
      rw [Rat.eventuallyClose_iff] at h ⊢
      peel h
      rwa [←neg_sub, abs_neg]
  simp_rw [Rat.eventuallyClose_iff]
  intro a b ⟨N, hab⟩ ⟨M, hM₁, hM₂⟩
  let b' (i : Fin N) : ℚ := b i
  have ⟨M', hM₁', hM₂'⟩ := IsBounded.finite b'
  use max (M + ε) M', by positivity
  intro i
  rw [eval_coe_at_int]
  by_cases hi₁ : i < 0
  . simp_rw [not_le_of_gt hi₁, if_false]
    positivity
  rw [not_lt] at hi₁
  lift i to ℕ using hi₁
  simp_rw [Int.natCast_nonneg, if_true, Int.toNat_natCast]
  by_cases hi₂ : i < N
  . specialize hM₂' ⟨i, hi₂⟩
    simp_all [b']
  . rw [not_lt] at hi₂
    specialize hab i hi₂
    specialize hM₂ i
    rw [eval_coe] at hM₂
    rw [←neg_sub, abs_neg] at hab
    calc
      _ = |(b i - a i) + a i| := by simp
      _ ≤ |(b i - a i)| + |a i| := by apply abs_add_le
      _ ≤ ε + M := by gcongr
      _ ≤ _ := by simp [add_comm]

end Chapter5
