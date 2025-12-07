import Mathlib.Tactic
import Analysis.Section_5_4
import Analysis.Section_4_4


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds).  Here we use the `upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  simp_rw [Real.upperBound_def, Real.mem_Icc]
  constructor
  . intro h
    exact h 1 ⟨by simp, by simp⟩
  . intro h x hx
    exact le_trans hx.right h

/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M : Real, M ∈ upperBounds (.Ioi 0) := by
  intro ⟨M, hM⟩
  rw [Real.Ioi_def, Real.upperBound_def] at hM
  by_cases h : 0 < M
  . specialize hM (M + 1) (by rw [Set.mem_setOf]; positivity)
    grind
  . specialize hM 1 (by rw [Set.mem_setOf]; positivity)
    grind

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by simp

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
  peel hb with x hx hxM
  exact le_trans hxM h

/-- Definition 5.5.5 (least upper bound).  Here we use the `isLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1 : Real) := by
  simp_rw [Real.isLUB_def, Real.upperBound_def, Real.mem_Icc]
  constructor
  . simp
  . intro M h
    specialize h 1 (by simp)
    exact h

/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  intro ⟨M, hM⟩
  simp_rw [Real.isLUB_def, Real.upperBound_def] at hM
  have := hM.right (M - 1) (by simp)
  grind

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by grind [Real.isLUB_def]

/-- definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
  induction' h : (K - L - 1).toNat with a ih generalizing K
  . use K, hLK, le_rfl, hK, by rw_mod_cast [show K - 1 = L by grind]; exact hL
  . by_cases hKE : ↑(K - 1) * ((1 / (n + 1) : ℚ) : Real) ∈ upperBounds E
    . specialize ih (K := K - 1) (by grind) hKE (by grind)
      grw [show K - 1 ≤ K by simp] at ih
      exact ih
    . use K, hLK, le_rfl, hK, by exact_mod_cast hKE

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by
  by_contra! hmm'
  wlog hmm'₂ : m < m' generalizing m m'
  . exact this hm'1 hm'2 hm1 hm2 hmm'.symm (lt_of_le_of_ne (le_of_not_gt hmm'₂) hmm'.symm)
  have hmm'₃ : (((m : ℚ) / (n + 1) : ℚ) : Real) ≤ (((m' : ℚ) / (n + 1) - 1 / (n + 1) : ℚ) : Real) := by
    grw [show m ≤ m' - 1 by linarith]
    push_cast
    rw [sub_div]
  simp_rw [upperBound_def, not_forall] at hm1 hm'2
  grind

/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
  simp_rw [IsCauchy.coe, Section_4_3.dist_eq, Pi.abs_apply] at ha ⊢
  peel ha
  grw [abs_abs_sub_abs_le_abs_sub]
  exact this

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
  rw [LIM_eq_LIM ha hb] at h
  rw [LIM_eq_LIM (Sequence.IsCauchy.abs ha) (Sequence.IsCauchy.abs hb)]
  simp_rw [Sequence.equiv_iff, Pi.abs_apply] at h ⊢
  peel h
  grw [abs_abs_sub_abs_le_abs_sub]
  exact this

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
    LIM a = LIM |a| := by
  rw [gt_iff, sub_zero, isPos_def] at h
  obtain ⟨b, ⟨c, hc, hc'⟩, hb, hab⟩ := h
  rw [LIM_eq_LIM ha hb, Sequence.equiv_iff] at hab
  obtain ⟨N, hN⟩ := hab c hc
  rw [LIM_eq_LIM ha (Sequence.IsCauchy.abs ha), Sequence.equiv_iff]
  intro ε hε
  use N
  peel hN with n hn hab'
  apply neg_le_of_abs_le at hab'
  grw [hc' n, le_sub_iff_add_le, neg_add_cancel] at hab'
  simp_rw [Pi.abs_apply, abs_of_nonneg hab', sub_self, abs_zero, le_of_lt hε]

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  rcases (LIM a).trichotomous' 0 with (h | h | h)
  . rw [_root_.abs_of_pos h]
    exact LIM.abs_eq_pos h ha
  . rw [_root_.abs_of_neg h, neg_LIM _ ha, ← abs_neg]
    rw [← neg_pos, neg_LIM _ ha] at h
    exact LIM.abs_eq_pos h (Sequence.IsCauchy.neg _ ha)
  . rw [h, abs_zero, ← LIM.zero, LIM_eq_LIM (Sequence.IsCauchy.const 0) (Sequence.IsCauchy.abs ha), Sequence.equiv_iff]
    rw [← LIM.zero, LIM_eq_LIM ha (Sequence.IsCauchy.const 0), Sequence.equiv_iff] at h
    peel h; simpa

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
    (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by
  obtain ⟨N, hN⟩ := h
  let a' := Sequence.replace a N fun _ ↦ a N
  rw [show LIM a = LIM a' by apply Real.LIM_eq_replace]
  apply LIM_of_le (Sequence.IsCauchy.replace hcauchy _ _)
  intro n
  rw [Sequence.replace]
  split_ifs with hn
  . exact hN n hn
  . exact hN N le_rfl

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by
  have hq_c : (q : Sequence).IsCauchy := by
    simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq]
    intro ε hε
    use ⌊ε⁻¹⌋₊
    specialize hq ⌊ε⁻¹⌋₊
    peel hq with n hn m hm h
    grw [h, one_div, inv_le_comm₀ (by positivity) hε]
    exact le_of_lt (Nat.lt_floor_add_one _)
  constructor
  . exact hq_c
  . intro M
    have hqM_c := Sequence.IsCauchy.const (q M)
    have hsub_c := Sequence.IsCauchy.sub hqM_c hq_c
    rw [ratCast_def, LIM_sub hqM_c hq_c, LIM_abs hsub_c]
    apply LIM_of_le' (Sequence.IsCauchy.abs hsub_c)
    use M
    intro n hn
    specialize hq M M le_rfl n hn
    rw [Pi.abs_apply, Pi.sub_apply, show (1 : Real) / (M + 1) = (1 : ℚ) / (M + 1) by simp]
    exact_mod_cast hq

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hb : (b:Sequence).IsCauchy := .harmonic'
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  . intros; apply LIM_of_ge claim3; grind [upperBound_def]
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
  rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers ⊤ to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers ⊥ to denote the -∞ element.-/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real)
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  use x; obtain h | h | h := trichotomous' (x^2) 2
  . have claim11: ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 - 4*ε > 2 := by
      set ε := min (1/2) ((x^2-2)/8)
      have hx : x^2 - 2 > 0 := by linarith
      have hε : 0 < ε := by positivity
      observe hε1: ε ≤ 1/2
      observe hε2: ε ≤ (x^2-2)/8
      refine' ⟨ ε, hε, _, _ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim11
    have claim12: (x-ε)^2 > 2 := calc
      _ = x^2 - 2 * ε * x + ε * ε := by ring
      _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
      _ = x^2 - 4 * ε := by ring
      _ > 2 := hε3
    have why (y:Real) (hy: y ∈ E) : x - ε ≥ y := by
      simp_rw [E, Set.mem_setOf] at hy
      simp_rw [← pow_le_pow_iff_left₀ hy.left (by linarith : 0 ≤ x - ε) (by decide : 2 ≠ 0)]
      linarith
    have claim13: x-ε ∈ upperBounds E := by rwa [upperBound_def]
    have claim14: x ≤ x-ε := by grind [isLUB_def]
    linarith
  . have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  assumption

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by
  have ⟨x, hx⟩ := exist_sqrt_two
  use x
  intro ⟨q, hq⟩
  rw [hq] at hx
  norm_cast at hx
  exact Rat.not_exist_sqrt_two ⟨q, hx⟩

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by
  simp_rw [isLUB_def, upperBound_def] at h
  simp_rw [isGLB_def, lowerBound_def, mem_neg]
  constructor
  . intro x hx
    rw [ge_iff_le, neg_le]
    exact h.left (-x) hx
  . intro M' hM'
    rw [le_neg]
    apply h.right (-M')
    intro x hx
    specialize hM' (-x) (by simp [hx])
    rwa [ge_iff_le, le_neg] at hM'

theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  simp_rw [bddBelow_def, lowerBound_def] at hbound
  simp_rw [isGLB_def, lowerBound_def]
  have hnE : (-E).Nonempty := by
    have ⟨x, hx⟩ := hE
    use -x
    simpa
  have hnE' : BddAbove (-E) := by
    have ⟨M', hM'⟩ := hbound
    use -M'
    intro x hx
    exact hM' (-x) (by simpa [mem_neg]) |> le_neg.mp
  have ⟨S, hS⟩ := LUB_exist hnE hnE'
  simp_rw [isLUB_def, upperBound_def] at hS
  use -S
  constructor
  . intro x hx
    exact hS.left (-x) (by simpa) |> neg_le.mp
  . intro M' hM'
    rw [le_neg]
    apply hS.right (-M')
    intro x hx
    specialize hM' (-x) (by simpa [mem_neg])
    rwa [ge_iff_le, le_neg] at hM'

open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by
  have ⟨p, hxp, hpy⟩ := rat_between hxy
  have ⟨q, hpq, hqy⟩ := rat_between hpy
  have ⟨sqrt2, hsqrt2⟩ := exist_sqrt_two
  wlog hsqrt2₁ : 0 ≤ sqrt2 generalizing sqrt2
  . specialize this (-sqrt2); rw [neg_pow_two] at this; exact this hsqrt2 (by linarith)
  replace hsqrt2₁ : 1 < sqrt2 := by apply lt_of_pow_lt_pow_left₀ 2 hsqrt2₁; rw [hsqrt2]; norm_num
  have hsqrt2₂ : sqrt2 < 2 := by apply lt_of_pow_lt_pow_left₀ 2 (by positivity); rw [hsqrt2]; norm_num
  use p + (q - p) * (sqrt2 - 1)
  and_intros
  . grw [hxp, lt_add_iff_pos_right]
    apply mul_pos
    . simp [hpq]
    . simp [hsqrt2₁]
  . grw [← hqy, ← lt_sub_iff_add_lt', mul_lt_iff_lt_one_right (by linarith)]
    linarith
  . by_contra!
    obtain ⟨s, hs⟩ := this
    apply Rat.not_exist_sqrt_two
    use (s - p) / (q - p) + 1
    rw [← ratCast_inj]
    push_cast
    rw [← hs, add_sub_cancel_left, mul_div_cancel_left₀ _ (by grind), sub_add_cancel]
    exact hsqrt2

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the `sSup` operation to build a conditionally complete lattice structure on `Real`-/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
