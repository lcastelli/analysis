import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  have ⟨A, h'⟩ := h (fun _ ↦ False)
  use A
  simp only [iff_false] at h'
  assumption

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  have ⟨A, h'⟩ := h (fun y ↦ y = x)
  use A

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  have ⟨A, h'⟩ := h (fun y ↦ y = x₁ ∨ y = x₂)
  use A

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  have ⟨C, h'⟩ := h (fun z ↦ z ∈ A ∨ z ∈ B)
  use C

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  have ⟨C, h'⟩ := h (fun z ↦ ∃ h : z ∈ A, P ⟨ z, h ⟩)
  use C

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  have ⟨C, h'⟩ := h (fun y ↦ ∃ a : A, P a y)
  use C

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  intro hA
  let A' := ({(A: Object)}: Set)
  have A'_not_empty : A' ≠ (∅: Set) := by
    intro h
    subst A'
    simp only [Set.ext_iff, not_mem_empty] at h
    specialize h A
    rwa [mem_singleton, eq_self, true_iff] at h
  have ⟨⟨a', ha'⟩, h⟩ := axiom_of_regularity A'_not_empty
  have a'_eq : a' = A := by
    simp only [A', mem_singleton] at ha'
    assumption
  specialize h A a'_eq
  simp only [disjoint_iff, Set.ext_iff, not_mem_empty, mem_inter] at h
  specialize h A
  apply h.mp
  constructor
  . assumption
  . unfold A'
    simp

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  by_contra! h
  let C : Set := {(A : Object), (B : Object)}
  have C_not_empty : C ≠ (∅: Set) := by
    intro hC
    subst C
    simp only [Set.ext_iff, not_mem_empty] at hC
    specialize hC A
    apply hC.mp
    simp
  have ⟨⟨c, hc⟩, hc'⟩ := axiom_of_regularity C_not_empty
  have c_eq : c = A ∨ c = B := by
    simp only [C, mem_pair] at hc
    assumption
  cases' c_eq <;>
  subst c
  case' inl => specialize hc' A
  case' inr => specialize hc' B
  all_goals
    simp only [forall_const, disjoint_iff, Set.ext_iff, not_mem_empty, mem_inter] at hc'
  case' inl =>
    specialize hc' B
    refine hc'.mp ⟨h.right, ?_⟩
  case' inr =>
    specialize hc' A
    refine hc'.mp ⟨h.left, ?_⟩
  all_goals
    subst C
    simp

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
  constructor
  . intro h
    have ⟨U, hU⟩ := h (fun _ ↦ True)
    simp only [iff_true] at hU
    use U
  . intro ⟨U, hU⟩ P
    use U.specify (P ·)
    simp only [specification_axiom'', exists_prop, and_iff_right_iff_imp]
    intro x _
    exact hU x

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  intro ⟨U, hU⟩
  apply not_mem_self U
  apply hU


end Chapter3
