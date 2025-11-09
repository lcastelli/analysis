import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image `f '' S` and preimage `f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.4.1.  Interestingly, the definition does not require S to be a subset of X. -/
abbrev SetTheory.Set.image {X Y:Set} (f:X → Y) (S: Set) : Set :=
  X.replace (P := fun x y ↦ f x = y ∧ x.val ∈ S) (by simp_all)

/-- Definition 3.4.1 -/
theorem SetTheory.Set.mem_image {X Y:Set} (f:X → Y) (S: Set) (y:Object) :
    y ∈ image f S ↔ ∃ x:X, x.val ∈ S ∧ f x = y := by
  grind [replacement_axiom]

/-- Alternate definition of image using axiom of specification -/
theorem SetTheory.Set.image_eq_specify {X Y:Set} (f:X → Y) (S: Set) :
    image f S = Y.specify (fun y ↦ ∃ x:X, x.val ∈ S ∧ f x = y) := by
  ext y
  simp only [replacement_axiom, Subtype.coe_eq_iff, Subtype.exists, exists_and_right,
    exists_and_left, specification_axiom'']
  constructor
  . rintro ⟨x, ⟨hX, hY, hxy⟩, hS⟩
    exact ⟨hY, x, hS, hX, hxy⟩
  . rintro ⟨hY, x, hS, hX, hxy⟩
    exact ⟨x, ⟨hX, hY, hxy⟩, hS⟩

/--
  Connection with Mathlib's notion of image.  Note the need to utilize the `Subtype.val` coercion
  to make everything type consistent.
-/
theorem SetTheory.Set.image_eq_image {X Y:Set} (f:X → Y) (S: Set):
    (image f S: _root_.Set Object) = Subtype.val '' (f '' {x | x.val ∈ S}) := by
  ext; simp; grind

theorem SetTheory.Set.image_in_codomain {X Y:Set} (f:X → Y) (S: Set) :
    image f S ⊆ Y := by intro _ h; rw [mem_image] at h; grind

/-- Example 3.4.2 -/
abbrev f_3_4_2 : nat → nat := fun n ↦ (2*n:ℕ)

theorem SetTheory.Set.image_f_3_4_2 : image f_3_4_2 {1,2,3} = {2,4,6} := by
  ext; simp only [mem_image, mem_triple, f_3_4_2]
  constructor
  · rintro ⟨_, (_ | _ | _), rfl⟩ <;> simp_all
  rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals simp_all

/-- Example 3.4.3 is written using Mathlib's notion of image. -/
example : (fun n:ℤ ↦ n^2) '' {-1,0,1,2} = {0,1,4} := by aesop

theorem SetTheory.Set.mem_image_of_eval {X Y:Set} (f:X → Y) (S: Set) (x:X) :
    x.val ∈ S → (f x).val ∈ image f S := by
  rw [mem_image]
  intro hS
  use x

theorem SetTheory.Set.mem_image_of_eval_counter :
    ∃ (X Y:Set) (f:X → Y) (S: Set) (x:X), ¬((f x).val ∈ image f S → x.val ∈ S) := by
  let f (_ : Nat) : Nat := 0
  use Nat, Nat, f, ({0}: Set), 1
  rw [mem_image]
  intro h
  specialize h ?s
  . use 0
    simp [f]
  . simp at h

/--
  Definition 3.4.4 (inverse images).
  Again, it is not required that U be a subset of Y.
-/
abbrev SetTheory.Set.preimage {X Y:Set} (f:X → Y) (U: Set) : Set := X.specify (P := fun x ↦ (f x).val ∈ U)

@[simp]
theorem SetTheory.Set.mem_preimage {X Y:Set} (f:X → Y) (U: Set) (x:X) :
    x.val ∈ preimage f U ↔ (f x).val ∈ U := by rw [specification_axiom']

/--
  A version of mem_preimage that does not require x to be of type X.
-/
theorem SetTheory.Set.mem_preimage' {X Y:Set} (f:X → Y) (U: Set) (x:Object) :
    x ∈ preimage f U ↔ ∃ x': X, x'.val = x ∧ (f x').val ∈ U := by
  constructor
  . intro h; by_cases hx: x ∈ X
    . use ⟨ x, hx ⟩; have := mem_preimage f U ⟨ _, hx ⟩; simp_all
    . grind [specification_axiom]
  . rintro ⟨ x', rfl, hfx' ⟩; rwa [mem_preimage]

/-- Connection with Mathlib's notion of preimage. -/
theorem SetTheory.Set.preimage_eq {X Y:Set} (f:X → Y) (U: Set) :
    ((preimage f U): _root_.Set Object) = Subtype.val '' (f⁻¹' {y | y.val ∈ U}) := by
  ext; simp

theorem SetTheory.Set.preimage_in_domain {X Y:Set} (f:X → Y) (U: Set) :
    (preimage f U) ⊆ X := by intro _ _; aesop

/-- Example 3.4.6 -/
theorem SetTheory.Set.preimage_f_3_4_2 : preimage f_3_4_2 {2,4,6} = {1,2,3} := by
  ext; simp only [mem_preimage', mem_triple, f_3_4_2]; constructor
  · rintro ⟨x, rfl, (_ | _ | _)⟩ <;> simp_all <;> omega
  rintro (rfl | rfl | rfl); map_tacs [use 1; use 2; use 3]
  all_goals simp

theorem SetTheory.Set.image_preimage_f_3_4_2 :
    image f_3_4_2 (preimage f_3_4_2 {1,2,3}) ≠ {1,2,3} := by
  intro h
  simp only [SetTheory.Set.ext_iff, mem_image, mem_preimage] at h
  specialize h 1
  simp at h

/-- Example 3.4.7 (using the Mathlib notion of preimage) -/
example : (fun n:ℤ ↦ n^2) ⁻¹' {0,1,4} = {-2,-1,0,1,2} := by
  ext; refine ⟨ ?_, by aesop ⟩; rintro (_ | _ | h)
  on_goal 3 => have : 2 ^ 2 = (4:ℤ) := (by norm_num); rw [←h, sq_eq_sq_iff_eq_or_eq_neg] at this
  all_goals aesop

example : (fun n:ℤ ↦ n^2) ⁻¹' ((fun n:ℤ ↦ n^2) '' {-1,0,1,2}) ≠ {-1,0,1,2} := by
  intro h
  simp only [_root_.Set.image_insert_eq, _root_.Set.image_singleton, _root_.Set.preimage,
      _root_.Set.ext_iff, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
      _root_.Set.mem_setOf_eq] at h
  specialize h (-2)
  grind

instance SetTheory.Set.inst_pow : Pow Set Set where
  pow := pow

@[coe]
def SetTheory.Set.coe_of_fun {X Y:Set} (f: X → Y) : Object := function_to_object X Y f

/-- This coercion has to be a `CoeOut` rather than a
`Coe` because the input type `X → Y` contains
parameters not present in the output type `Output` -/
instance SetTheory.Set.inst_coe_of_fun {X Y:Set} : CoeOut (X → Y) Object where
  coe := coe_of_fun

@[simp]
theorem SetTheory.Set.coe_of_fun_inj {X Y:Set} (f g:X → Y) : (f:Object) = (g:Object) ↔ f = g := by
  simp [coe_of_fun]

/-- Axiom 3.11 (Power set axiom) --/
@[simp]
theorem SetTheory.Set.powerset_axiom {X Y:Set} (F:Object) :
    F ∈ (X ^ Y) ↔ ∃ f: Y → X, f = F := SetTheory.powerset_axiom X Y F

/-- Example 3.4.9 -/
abbrev f_3_4_9_a : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 0, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_b : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 0, by simp ⟩ else ⟨ 1, by simp ⟩

open Classical in
noncomputable abbrev f_3_4_9_c : ({4,7}:Set) → ({0,1}:Set) :=
  fun x ↦ if x.val = 4 then ⟨ 1, by simp ⟩ else ⟨ 0, by simp ⟩

abbrev f_3_4_9_d : ({4,7}:Set) → ({0,1}:Set) := fun x ↦ ⟨ 1, by simp ⟩

theorem SetTheory.Set.example_3_4_9 (F:Object) :
    F ∈ ({0,1}:Set) ^ ({4,7}:Set) ↔ F = f_3_4_9_a
    ∨ F = f_3_4_9_b ∨ F = f_3_4_9_c ∨ F = f_3_4_9_d := by
  rw [powerset_axiom]
  refine ⟨?_, by aesop ⟩
  rintro ⟨f, rfl⟩
  have h1 := (f ⟨4, by simp⟩).property
  have h2 := (f ⟨7, by simp⟩).property
  simp [coe_of_fun_inj] at *
  obtain _ | _ := h1 <;> obtain _ | _ := h2
  map_tacs [left; (right;left); (right;right;left); (right;right;right)]
  all_goals ext ⟨_, hx⟩; simp at hx; grind

/-- Exercise 3.4.6 (i). One needs to provide a suitable definition of the power set here. -/
def SetTheory.Set.powerset (X:Set) : Set :=
  (({0,1} ^ X): Set).replace (P := fun F y ↦ ∃ f : X → ({0,1}: Set), f = F.val ∧ y = preimage f {1}) (by simp)

open Classical in
/-- Exercise 3.4.6 (i) -/
@[simp]
theorem SetTheory.Set.mem_powerset {X:Set} (x:Object) :
    x ∈ powerset X ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  simp only [powerset, replacement_axiom, Subtype.exists, powerset_axiom, exists_prop,
    exists_exists_eq_and, coe_of_fun_inj, exists_eq_left]
  constructor
  . intro ⟨f, hx⟩
    use preimage f {1}
    constructor
    . assumption
    . intro x' hx'
      simp at hx'
      exact hx'.fst
  . rintro ⟨X', hx, hX'⟩
    let f (a : X) : ({0, 1}: Set) := if a.val ∈ X' then ⟨1, by aesop⟩ else ⟨0, by aesop⟩
    use f
    rw [hx, coe_eq_iff]
    ext e
    simp only [mem_preimage', f, mem_singleton]
    constructor
    . intro he
      use ⟨e, hX' e he⟩
      simp only [true_and]
      split <;> simp
    . rintro ⟨x', rfl, hf⟩
      split at hf
      . assumption
      . simp at hf

/-- Lemma 3.4.10 -/
theorem SetTheory.Set.exists_powerset (X:Set) :
   ∃ (Z: Set), ∀ x, x ∈ Z ↔ ∃ Y:Set, x = Y ∧ Y ⊆ X := by
  use powerset X; apply mem_powerset

/- As noted in errata, Exercise 3.4.6 (ii) is replaced by Exercise 3.5.11. -/

/-- Remark 3.4.11 -/
theorem SetTheory.Set.powerset_of_triple (a b c x:Object) :
    x ∈ powerset {a,b,c}
    ↔ x = (∅:Set)
    ∨ x = ({a}:Set)
    ∨ x = ({b}:Set)
    ∨ x = ({c}:Set)
    ∨ x = ({a,b}:Set)
    ∨ x = ({a,c}:Set)
    ∨ x = ({b,c}:Set)
    ∨ x = ({a,b,c}:Set) := by
  simp only [mem_powerset, subset_def, mem_triple]
  refine ⟨ ?_, by aesop ⟩
  rintro ⟨Y, rfl, hY⟩; by_cases a ∈ Y <;> by_cases b ∈ Y <;> by_cases c ∈ Y
  on_goal 8 => left
  on_goal 4 => right; left
  on_goal 6 => right; right; left
  on_goal 7 => right; right; right; left
  on_goal 2 => right; right; right; right; left
  on_goal 3 => right; right; right; right; right; left
  on_goal 5 => right; right; right; right; right; right; left
  on_goal 1 => right; right; right; right; right; right; right
  all_goals congr; ext; simp; grind

/-- Axiom 3.12 (Union) -/
theorem SetTheory.Set.union_axiom (A: Set) (x:Object) :
    x ∈ union A ↔ ∃ (S:Set), x ∈ S ∧ (S:Object) ∈ A := SetTheory.union_axiom A x

/-- Example 3.4.12 -/
theorem SetTheory.Set.example_3_4_12 :
    union { (({2,3}:Set):Object), (({3,4}:Set):Object), (({4,5}:Set):Object) } = {2,3,4,5} := by
  ext x
  simp only [union_axiom, mem_insert, coe_eq_iff, mem_singleton]
  aesop

/-- Connection with Mathlib union -/
theorem SetTheory.Set.union_eq (A: Set) :
    (union A : _root_.Set Object) =
    ⋃₀ { S : _root_.Set Object | ∃ S':Set, S = S' ∧ (S':Object) ∈ A } := by
  ext; simp [union_axiom, Set.mem_sUnion]; aesop

/-- Indexed union -/
abbrev SetTheory.Set.iUnion (I: Set) (A: I → Set) : Set :=
  union (I.replace (P := fun α S ↦ S = A α) (by grind))

theorem SetTheory.Set.mem_iUnion {I:Set} (A: I → Set) (x:Object) :
    x ∈ iUnion I A ↔ ∃ α:I, x ∈ A α := by
  rw [union_axiom]; constructor
  . simp_all [replacement_axiom]; grind
  grind [replacement_axiom]

open Classical in
noncomputable abbrev SetTheory.Set.index_example : ({1,2,3}:Set) → Set :=
  fun i ↦ if i.val = 1 then {2,3} else if i.val = 2 then {3,4} else {4,5}

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext; intros; simp [mem_iUnion, index_example, Insert.insert]
  refine ⟨ by aesop, ?_ ⟩; rintro (_ | _ | _); map_tacs [use 1; use 2; use 3]
  all_goals aesop

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

theorem SetTheory.Set.iUnion_of_empty (A: (∅:Set) → Set) : iUnion (∅:Set) A = ∅ := by
  ext x; simp [mem_iUnion]

/-- Indexed intersection -/
noncomputable abbrev SetTheory.Set.nonempty_choose {I:Set} (hI: I ≠ ∅) : I :=
  ⟨(nonempty_def hI).choose, (nonempty_def hI).choose_spec⟩

abbrev SetTheory.Set.iInter' (I:Set) (β:I) (A: I → Set) : Set :=
  (A β).specify (P := fun x ↦ ∀ α:I, x.val ∈ A α)

noncomputable abbrev SetTheory.Set.iInter (I: Set) (hI: I ≠ ∅) (A: I → Set) : Set :=
  iInter' I (nonempty_choose hI) A

theorem SetTheory.Set.mem_iInter {I:Set} (hI: I ≠ ∅) (A: I → Set) (x:Object) :
    x ∈ iInter I hI A ↔ ∀ α:I, x ∈ A α := by
  grind [specification_axiom'']

/-- Exercise 3.4.1 -/
theorem SetTheory.Set.preimage_eq_image_of_inv {X Y V:Set} (f:X → Y) (f_inv: Y → X)
  (hf: Function.LeftInverse f_inv f ∧ Function.RightInverse f_inv f) (hV: V ⊆ Y) :
    image f_inv V = preimage f V := by
  ext x
  grind [replacement_axiom, specification_axiom'']

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f S)` and `S`. -/
theorem SetTheory.Set.preimage_of_image {X Y:Set} (f:X → Y) (S: Set) (hS: S ⊆ X) : S ⊆ preimage f (image f S) := by
  intro x hx
  simp only [mem_preimage', mem_image]
  have hx' : x ∈ X := hS x hx
  use ⟨x, hx'⟩
  simp only [Subtype.exists, exists_and_left, true_and]
  use x, hx, hx'

/- Exercise 3.4.2.  State and prove an assertion connecting `image f (preimage f U)` and `U`.
Interestingly, it is not needed for U to be a subset of Y. -/
theorem SetTheory.Set.image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : image f (preimage f U) ⊆ U := by
  intro x h
  simp only [replacement_axiom, specification_axiom'', Subtype.coe_eta, exists_prop,
    Subtype.exists] at h
  obtain ⟨x', hx', hxx', -, hU⟩ := h
  rwa [hxx'] at hU

/- Exercise 3.4.2.  State and prove an assertion connecting `preimage f (image f (preimage f U))` and `preimage f U`.
Interestingly, it is not needed for U to be a subset of Y.-/
theorem SetTheory.Set.preimage_of_image_of_preimage {X Y:Set} (f:X → Y) (U: Set) : preimage f (image f (preimage f U)) = preimage f U := by
  ext x
  simp only [specification_axiom'', replacement_axiom, Subtype.coe_eta, exists_prop, Subtype.exists]
  constructor
  . rintro ⟨hx, x', hx', hxx', -, hU⟩
    rw [hxx'] at hU
    use hx, hU
  . intro ⟨hx, hU⟩
    use hx, x, hx

/--
  Exercise 3.4.3.
-/
theorem SetTheory.Set.image_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∩ B) ⊆ (image f A) ∩ (image f B) := by
  intro y
  simp only [replacement_axiom, mem_inter, Subtype.exists, exists_and_right, forall_exists_index,
    and_imp]
  rintro x hx rfl hA hB
  constructor <;> use x <;> tauto

theorem SetTheory.Set.image_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    (image f A) \ (image f B) ⊆ image f (A \ B) := by
  intro y
  simp only [mem_sdiff, replacement_axiom, Subtype.exists, exists_and_right, not_exists, not_and,
    forall_exists_index, and_imp]
  rintro x hx rfl hA h
  use x; refine ⟨⟨hx, rfl⟩, hA, ?_⟩
  apply h
  . rfl
  . assumption

theorem SetTheory.Set.image_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    image f (A ∪ B) = (image f A) ∪ (image f B) := by
  ext y
  simp only [replacement_axiom, mem_union]
  grind

def SetTheory.Set.image_of_inter' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A ∩ B) = (image f A) ∩ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  intro h; specialize h Nat Nat (fun _ ↦ 0) {0} {1}
  simp only [SetTheory.Set.ext_iff, mem_image, mem_inter, mem_singleton] at h
  replace h := (h 0).mpr ?_
  . obtain ⟨x, ⟨h₁, h₂⟩, _⟩ := h
    simp [h₂] at h₁
  . constructor <;> [use 0; use 1] <;> simp

def SetTheory.Set.image_of_diff' : Decidable (∀ X Y:Set, ∀ f:X → Y, ∀ A B: Set, image f (A \ B) = (image f A) \ (image f B)) := by
  -- The first line of this construction should be either `apply isTrue` or `apply isFalse`
  apply isFalse
  intro h; specialize h Nat Nat (fun _ ↦ 0) {0,1} {0}
  simp only [SetTheory.Set.ext_iff, mem_image, mem_sdiff, mem_singleton, mem_pair] at h
  replace h := (h 0).mp ?_
  . absurd h.right; use 0; simp
  . use 1; simp

/-- Exercise 3.4.4 -/
theorem SetTheory.Set.preimage_of_inter {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∩ B) = (preimage f A) ∩ (preimage f B) := by
  ext x
  simp only [specification_axiom'', mem_inter]
  grind

theorem SetTheory.Set.preimage_of_union {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A ∪ B) = (preimage f A) ∪ (preimage f B) := by
  ext x
  simp only [specification_axiom'', mem_union]
  grind

theorem SetTheory.Set.preimage_of_diff {X Y:Set} (f:X → Y) (A B: Set) :
    preimage f (A \ B) = (preimage f A) \ (preimage f B)  := by
  ext x
  simp only [specification_axiom'', mem_sdiff, not_exists]
  grind

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.image_preimage_of_surj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ Y → image f (preimage f S) = S) ↔ Function.Surjective f := by
  constructor
  . intro h y
    specialize h {y.val} ?_
    . intro y' hy'; rw [mem_singleton] at hy'
      subst y'; exact y.property
    . rw [SetTheory.Set.ext_iff] at h; specialize h y
      simp only [mem_singleton, iff_true, mem_image, mem_preimage, Subtype.val_inj] at h
      obtain ⟨x, hxy, -⟩ := h; exact ⟨x, hxy⟩
  . intro h S hSY; ext y
    simp only [mem_image, mem_preimage]
    constructor
    . rintro ⟨x, hxS, rfl⟩; exact hxS
    . intro hyS; have ⟨x, hxy⟩ := h ⟨y, hSY y hyS⟩
      use x; simp [hxy, hyS]

/-- Exercise 3.4.5 -/
theorem SetTheory.Set.preimage_image_of_inj {X Y:Set} (f:X → Y) :
    (∀ S, S ⊆ X → preimage f (image f S) = S) ↔ Function.Injective f := by
  constructor
  . intro h x x' hxx'
    specialize h {x.val} ?_
    . intro x₁ hx₁; rw [mem_singleton] at hx₁;
      subst x₁; exact x.property
    . rw [SetTheory.Set.ext_iff] at h; specialize h x'
      simp only [mem_singleton, mem_preimage, mem_image, Subtype.val_inj] at h
      replace h := h.mp ?_
      . exact h.symm
      . use x
  . intro h S hSX
    ext x; simp only [mem_preimage', mem_image]
    constructor
    . rintro ⟨x, rfl, x', hx'S, hxx'⟩
      rw [Subtype.val_inj] at hxx'; specialize h hxx'
      subst x'; assumption
    . intro hxS; have hxX := hSX x hxS
      use ⟨x, hxX⟩; simp only [true_and]
      use ⟨x, hxX⟩

/-- Helper lemma for Exercise 3.4.7. -/
@[simp]
lemma SetTheory.Set.mem_powerset' {S S' : Set} : (S': Object) ∈ S.powerset ↔ S' ⊆ S := by
  simp [mem_powerset]

/-- Another helper lemma for Exercise 3.4.7. -/
lemma SetTheory.Set.mem_union_powerset_replace_iff {S : Set} {P : S.powerset → Object → Prop} {hP : _} {x : Object} :
    x ∈ union (S.powerset.replace (P := P) hP) ↔
    ∃ (S' : S.powerset) (U : Set), P S' U ∧ x ∈ U := by
  grind [union_axiom, replacement_axiom]

/-- Exercise 3.4.7 -/
theorem SetTheory.Set.partial_functions {X Y:Set} :
    ∃ Z:Set, ∀ F:Object, F ∈ Z ↔ ∃ X' Y':Set, X' ⊆ X ∧ Y' ⊆ Y ∧ ∃ f: X' → Y', F = f := by
  let inner (X' : Set) := Y.powerset.replace (P := fun y z' ↦ ∃ (Y' : Set), Y' = y.val ∧ z' = (Y' ^ X' : Set))
      (by aesop) |> union
  let outer := X.powerset.replace (P := fun x z ↦ ∃ (X': Set), X' = x.val ∧ z = inner X')
      (by aesop) |> union
  use outer
  intro F; simp only [outer, mem_union_powerset_replace_iff, coe_eq_iff]
  constructor
  . intro hF; obtain ⟨S, -, ⟨X', hX'S, rfl⟩, hF⟩ := hF
    simp only [inner, mem_union_powerset_replace_iff, coe_eq_iff] at hF
    obtain ⟨U, -, ⟨Y', hY'U, rfl⟩, hF⟩ := hF
    have hX' := S.property; rw [←hX'S, mem_powerset'] at hX'
    have hY' := U.property; rw [←hY'U, mem_powerset'] at hY'
    rw [powerset_axiom] at hF
    grind
  . rintro ⟨X', Y', hX'X, hY'Y, f, rfl⟩
    use ⟨X', by rwa [mem_powerset']⟩, inner X'
    simp only [coe_eq_iff, exists_eq_left, true_and]
    simp only [inner, mem_union_powerset_replace_iff, coe_eq_iff]
    use ⟨Y', by rwa [mem_powerset']⟩, Y' ^ X'
    simp

/--
  Exercise 3.4.8.  The point of this exercise is to prove it without using the
  pairwise union operation `∪`.
-/
theorem SetTheory.Set.union_pair_exists (X Y:Set) : ∃ Z:Set, ∀ x, x ∈ Z ↔ (x ∈ X ∨ x ∈ Y) := by
  use union {(X: Object), (Y: Object)}
  intro x; simp only [union_axiom, mem_pair, coe_eq_iff]
  grind

/-- Exercise 3.4.9 -/
theorem SetTheory.Set.iInter'_insensitive {I:Set} (β β':I) (A: I → Set) :
    iInter' I β A = iInter' I β' A := by
  ext x; simp only [specification_axiom'', exists_prop, and_congr_left_iff]
  grind

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_iUnion {I J:Set} (A: (I ∪ J:Set) → Set) :
    iUnion I (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∪ iUnion J (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iUnion (I ∪ J) A := by
  ext x; simp only [mem_union, mem_iUnion, Subtype.exists]
  grind

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.union_of_nonempty {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) : I ∪ J ≠ ∅ := by
  intro h; simp only [SetTheory.Set.ext_iff, mem_union, not_mem_empty, iff_false, not_or] at h
  have := nonempty_def hI
  grind

/-- Exercise 3.4.10 -/
theorem SetTheory.Set.inter_iInter {I J:Set} (hI: I ≠ ∅) (hJ: J ≠ ∅) (A: (I ∪ J:Set) → Set) :
    iInter I hI (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    ∩ iInter J hJ (fun α ↦ A ⟨ α.val, by simp [α.property]⟩)
    = iInter (I ∪ J) (union_of_nonempty hI hJ) A := by
  --ext x; unfold iInter; simp only [mem_inter]
  ext x; simp only [mem_inter, specification_axiom'', exists_prop]
  constructor
  . rintro ⟨⟨-, hI⟩, ⟨-, hJ⟩⟩
    have (i : (I ∪ J).toSubtype) : x ∈ A i := by
      obtain ⟨i, h⟩ := i; rw [mem_union] at h
      cases' h with h h
      . exact hI ⟨i, h⟩
      . exact hJ ⟨i, h⟩
    tauto
  . grind

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iUnion {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iUnion I A = iInter I hI (fun α ↦ X \ A α) := by
  ext x
  simp only [mem_iUnion, mem_iInter, mem_sdiff, not_exists, forall_and, forall_const, Nonempty.intro (nonempty_choose hI)]

/-- Exercise 3.4.11 -/
theorem SetTheory.Set.compl_iInter {X I: Set} (hI: I ≠ ∅) (A: I → Set) :
    X \ iInter I hI A = iUnion I (fun α ↦ X \ A α) := by
  ext x
  simp only [mem_iUnion, mem_sdiff, mem_iInter, not_forall]; tauto

end Chapter3
