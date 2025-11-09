import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Section_3_2
import Analysis.Section_3_4

/-!
# Analysis I, Section 3.5: Cartesian products

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordered pairs and n-tuples.
- Cartesian products and n-fold products.
- Finite choice.
- Connections with Mathlib counterparts such as `Set.pi` and `Set.prod`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

--/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

open SetTheory.Set

/-- Definition 3.5.1 (Ordered pair).  One could also have used `Object × Object` to
define `OrderedPair` here. -/
@[ext]
structure OrderedPair where
  fst: Object
  snd: Object

#check OrderedPair.ext

/-- Definition 3.5.1 (Ordered pair) -/
@[simp]
theorem OrderedPair.eq (x y x' y' : Object) :
    (⟨ x, y ⟩ : OrderedPair) = (⟨ x', y' ⟩ : OrderedPair) ↔ x = x' ∧ y = y' := by aesop

/-- Helper lemma for Exercise 3.5.1 -/
lemma SetTheory.Set.pair_eq_singleton_iff {a b c: Object} : {a, b} = ({c}: Set) ↔
    a = c ∧ b = c := by
  simp only [SetTheory.Set.ext_iff, mem_pair, mem_singleton]
  constructor
  . intro h
    constructor
    . specialize h a; grind
    . specialize h b; grind
  . grind

/-- Exercise 3.5.1, first part -/
def OrderedPair.toObject : OrderedPair ↪ Object where
  toFun p := ({ (({p.fst}:Set):Object), (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro ⟨a, b⟩ ⟨a', b'⟩ h
    suffices a = a' ∧ b = b' by grind
    simp only [coe_eq_iff] at h
    apply pair_eq_pair at h
    simp only [coe_eq_iff] at h
    cases' h with h h
    . obtain ⟨ha, hab⟩ := h
      have : a = a' := by simp_all [SetTheory.Set.ext_iff]
      subst a'; apply pair_eq_pair at hab
      grind
    . obtain ⟨ha, ha'⟩ := h
      grind [pair_eq_singleton_iff]

instance OrderedPair.inst_coeObject : Coe OrderedPair Object where
  coe := toObject

/--
  A technical operation, turning a object `x` and a set `Y` to a set `{x} × Y`, needed to define
  the full Cartesian product
-/
abbrev SetTheory.Set.slice (x:Object) (Y:Set) : Set :=
  Y.replace (P := fun y z ↦ z = (⟨x, y⟩:OrderedPair)) (by grind)

@[simp]
theorem SetTheory.Set.mem_slice (x z:Object) (Y:Set) :
    z ∈ (SetTheory.Set.slice x Y) ↔ ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := replacement_axiom _ _

/-- Definition 3.5.4 (Cartesian product) -/
abbrev SetTheory.Set.cartesian (X Y:Set) : Set :=
  union (X.replace (P := fun x z ↦ z = slice x Y) (by grind))

/-- This instance enables the ×ˢ notation for Cartesian product. -/
instance SetTheory.Set.inst_SProd : SProd Set Set Set where
  sprod := cartesian

example (X Y:Set) : X ×ˢ Y = SetTheory.Set.cartesian X Y := rfl

@[simp]
theorem SetTheory.Set.mem_cartesian (z:Object) (X Y:Set) :
    z ∈ X ×ˢ Y ↔ ∃ x:X, ∃ y:Y, z = (⟨x, y⟩:OrderedPair) := by
  simp only [SProd.sprod, union_axiom]; constructor
  . intro ⟨ S, hz, hS ⟩; rw [replacement_axiom] at hS; obtain ⟨ x, hx ⟩ := hS
    use x; simp_all
  rintro ⟨ x, y, rfl ⟩; use slice x Y; refine ⟨ by simp, ?_ ⟩
  rw [replacement_axiom]; use x

theorem SetTheory.Set.mem_cartesian' {X Y : Set} (z : X ×ˢ Y) : ∃ x : X, ∃ y : Y, z = ⟨(⟨x, y⟩:OrderedPair), by simp⟩ := by
  have ⟨x, y, hz⟩:= (mem_cartesian z.val X Y).mp z.property
  use x, y; grind

noncomputable def SetTheory.Set.cartesianToOrderedPair {X Y : Set} (z : X ×ˢ Y) : OrderedPair :=
  have hz := mem_cartesian' z
  OrderedPair.mk hz.choose hz.choose_spec.choose

theorem SetTheory.Set.cartesianToOrderedPair_inj {X Y : Set} (z z' : X ×ˢ Y) :
    cartesianToOrderedPair z = cartesianToOrderedPair z' ↔ z = z' := by
  constructor
  . intro h; simp only [cartesianToOrderedPair] at h
    have h₁ := (mem_cartesian' z).choose_spec.choose_spec
    have h₂ := (mem_cartesian' z').choose_spec.choose_spec
    simp only [h, ←h₂] at h₁; assumption
  . grind

noncomputable abbrev SetTheory.Set.fst {X Y:Set} (z:X ×ˢ Y) : X :=
  ((mem_cartesian _ _ _).mp z.property).choose

noncomputable abbrev SetTheory.Set.snd {X Y:Set} (z:X ×ˢ Y) : Y :=
  (exists_comm.mp ((mem_cartesian _ _ _).mp z.property)).choose

theorem SetTheory.Set.pair_eq_fst_snd {X Y:Set} (z:X ×ˢ Y) :
    z.val = (⟨ fst z, snd z ⟩:OrderedPair) := by
  have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y, hy: z.val = (⟨ fst z, y ⟩:OrderedPair)⟩ := this.choose_spec
  obtain ⟨ x, hx: z.val = (⟨ x, snd z ⟩:OrderedPair)⟩ := (exists_comm.mp this).choose_spec
  simp_all [EmbeddingLike.apply_eq_iff_eq]

/-- This equips an `OrderedPair` with proofs that `x ∈ X` and `y ∈ Y`. -/
def SetTheory.Set.mk_cartesian {X Y:Set} (x:X) (y:Y) : X ×ˢ Y :=
  ⟨(⟨ x, y ⟩:OrderedPair), by simp⟩

@[simp]
theorem SetTheory.Set.fst_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    fst (mk_cartesian x y) = x := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ y', hy: z.val = (⟨ fst z, y' ⟩:OrderedPair) ⟩ := this.choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hy.1]

@[simp]
theorem SetTheory.Set.snd_of_mk_cartesian {X Y:Set} (x:X) (y:Y) :
    snd (mk_cartesian x y) = y := by
  let z := mk_cartesian x y; have := (mem_cartesian _ _ _).mp z.property
  obtain ⟨ x', hx: z.val = (⟨ x', snd z ⟩:OrderedPair) ⟩ := (exists_comm.mp this).choose_spec
  simp [z, mk_cartesian, Subtype.val_inj] at *; rw [←hx.2]

@[simp]
theorem SetTheory.Set.mk_cartesian_fst_snd_eq {X Y: Set} (z: X ×ˢ Y) :
    (mk_cartesian (fst z) (snd z)) = z := by
  rw [mk_cartesian, Subtype.mk.injEq, pair_eq_fst_snd]

/--
  Connections with the Mathlib set product, which consists of Lean pairs like `(x, y)`
  equipped with a proof that `x` is in the left set, and `y` is in the right set.
  Lean pairs like `(x, y)` are similar to our `OrderedPair`, but more general.
-/
noncomputable abbrev SetTheory.Set.prod_equiv_prod (X Y:Set) :
    ((X ×ˢ Y):_root_.Set Object) ≃ (X:_root_.Set Object) ×ˢ (Y:_root_.Set Object) where
  toFun z := ⟨(fst z, snd z), by simp⟩
  invFun z := mk_cartesian ⟨z.val.1, z.prop.1⟩ ⟨z.val.2, z.prop.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Example 3.5.5 -/
example : ({1, 2}: Set) ×ˢ ({3, 4, 5}: Set) = ({
  ((mk_cartesian (1: Nat) (3: Nat)): Object),
  ((mk_cartesian (1: Nat) (4: Nat)): Object),
  ((mk_cartesian (1: Nat) (5: Nat)): Object),
  ((mk_cartesian (2: Nat) (3: Nat)): Object),
  ((mk_cartesian (2: Nat) (4: Nat)): Object),
  ((mk_cartesian (2: Nat) (5: Nat)): Object)
}: Set) := by ext; aesop

/-- Example 3.5.5 / Exercise 3.6.5. There is a bijection between `X ×ˢ Y` and `Y ×ˢ X`. -/
noncomputable abbrev SetTheory.Set.prod_commutator (X Y:Set) : X ×ˢ Y ≃ Y ×ˢ X where
  toFun := fun x ↦ mk_cartesian (snd x) (fst x)
  invFun := fun x ↦ mk_cartesian (snd x) (fst x)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- Example 3.5.5. A function of two variables can be thought of as a function of a pair. -/
noncomputable abbrev SetTheory.Set.curry_equiv {X Y Z:Set} : (X → Y → Z) ≃ (X ×ˢ Y → Z) where
  toFun f z := f (fst z) (snd z)
  invFun f x y := f ⟨ (⟨ x, y ⟩:OrderedPair), by simp ⟩
  left_inv _ := by simp
  right_inv _ := by simp [←pair_eq_fst_snd]

/-- Definition 3.5.6.  The indexing set `I` plays the role of `{ i : 1 ≤ i ≤ n }` in the text.
    See Exercise 3.5.10 below for some connections betweeen this concept and the preceding notion
    of Cartesian product and ordered pair.  -/
abbrev SetTheory.Set.tuple {I:Set} {X: I → Set} (x: ∀ i, X i) : Object :=
  ((fun i ↦ ⟨ x i, by rw [mem_iUnion]; use i; exact (x i).property ⟩):I → iUnion I X)

/-- Definition 3.5.6 -/
abbrev SetTheory.Set.iProd {I: Set} (X: I → Set) : Set :=
  ((iUnion I X)^I).specify (fun t ↦ ∃ x : ∀ i, X i, t = tuple x)

/-- Definition 3.5.6 -/
theorem SetTheory.Set.mem_iProd {I: Set} {X: I → Set} (t:Object) :
    t ∈ iProd X ↔ ∃ x: ∀ i, X i, t = tuple x := by
  simp only [iProd, specification_axiom'']; constructor
  . intro ⟨ ht, x, h ⟩; use x
  intro ⟨ x, hx ⟩
  have h : t ∈ (I.iUnion X)^I := by simp [hx]
  use h, x

theorem SetTheory.Set.mem_iProd'  {I: Set} {X: I → Set} (t: iProd X) :
    ∃ x: ∀ i, X i, t = tuple x := (mem_iProd t.val).mp t.property

theorem SetTheory.Set.tuple_mem_iProd {I: Set} {X: I → Set} (x: ∀ i, X i) :
    tuple x ∈ iProd X := by rw [mem_iProd]; use x

abbrev SetTheory.Set.tuple' {I:Set} {X: I → Set} (x: ∀ i, X i) : iProd X := ⟨tuple x, tuple_mem_iProd x⟩

@[simp]
theorem SetTheory.Set.tuple_inj {I:Set} {X: I → Set} (x y: ∀ i, X i) :
    tuple x = tuple y ↔ x = y := by
  simp only [coe_of_fun_inj, funext_iff, Subtype.mk_eq_mk, Subtype.val_inj]

noncomputable def SetTheory.Set.tupleToFn {I : Set} {X : I → Set} (t : iProd X) : ∀ i, X i :=
  (mem_iProd' t).choose

set_option pp.proofs true in
@[simp]
theorem SetTheory.Set.tupleToFn_inj {I : Set} {X : I → Set} (t t' : iProd X) : tupleToFn t = tupleToFn t' ↔ t = t' := by
  constructor
  . intro h; unfold tupleToFn at h
    have h₁ := (mem_iProd' t).choose_spec
    have h₂ := (mem_iProd' t').choose_spec
    rwa [h, ←h₂, Subtype.val_inj] at h₁
  . grind

set_option pp.proofs true in
@[simp]
theorem SetTheory.Set.tupleToFn_tuple_eq {I : Set} {X : I → Set} (x: ∀ i, X i) : tupleToFn (tuple' x) = x := by
  have := (mem_iProd' ⟨tuple x, tuple_mem_iProd x⟩).choose_spec
  rw [tuple_inj] at this
  conv_rhs => rw [this]
  rfl

set_option pp.proofs true in
@[simp]
theorem SetTheory.Set.tuple_tupleToFn_eq {I : Set} {X : I → Set} (t: iProd X) : tuple' (tupleToFn t) = t := by
  have := (mem_iProd' t).choose_spec
  rw [Subtype.eq_iff, this, tuple_inj]
  rfl

/-- Example 3.5.8. There is a bijection between `(X ×ˢ Y) ×ˢ Z` and `X ×ˢ (Y ×ˢ Z)`. -/
noncomputable abbrev SetTheory.Set.prod_associator (X Y Z:Set) : (X ×ˢ Y) ×ˢ Z ≃ X ×ˢ (Y ×ˢ Z) where
  toFun p := mk_cartesian (fst (fst p)) (mk_cartesian (snd (fst p)) (snd p))
  invFun p := mk_cartesian (mk_cartesian (fst p) (fst (snd p))) (snd (snd p))
  left_inv _ := by simp
  right_inv _ := by simp

/--
  Example 3.5.10. I suspect most of the equivalences will require classical reasoning and only be
  defined non-computably, but would be happy to learn of counterexamples.
-/
noncomputable abbrev SetTheory.Set.singleton_iProd_equiv (i:Object) (X:Set) :
    iProd (fun _:({i}:Set) ↦ X) ≃ X where
  toFun := fun x ↦ tupleToFn x ⟨i, by aesop⟩
  invFun := fun x ↦ tuple' (fun _ ↦ x)
  left_inv := by
      intro ⟨x, hx⟩; rw [mem_iProd] at hx; obtain ⟨x, rfl⟩ := hx
      simp only [Subtype.mk_eq_mk, coe_of_fun_inj, tupleToFn_tuple_eq]
      funext ⟨i', hi'⟩; rw [mem_singleton] at hi'; subst i'; rfl
  right_inv := by intro; simp

/-- Example 3.5.10 -/
abbrev SetTheory.Set.empty_iProd_equiv (X: (∅:Set) → Set) : iProd X ≃ Unit where
  toFun := fun _ ↦ ()
  invFun := fun a ↦ tuple' (fun x : (∅: Set) ↦ absurd x.property (not_mem_empty x.val))
  left_inv := by
    intro ⟨t, ht⟩; obtain ⟨x, rfl⟩ := (mem_iProd t).mp ht
    simp only [Subtype.mk_eq_mk, tuple_inj]
    funext x'; grind
  right_inv := by intro; simp

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_of_const_equiv (I:Set) (X: Set) :
    iProd (fun _:I ↦ X) ≃ (I → X) where
  toFun := fun t ↦ tupleToFn t
  invFun := fun x ↦ tuple' x
  left_inv := by intro; simp
  right_inv := by intro; simp

open Classical in
/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod (X: ({0,1}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) where
  toFun := fun t ↦ let x := tupleToFn t; mk_cartesian (x ⟨0, by simp⟩) (x ⟨1, by simp⟩)
  invFun := fun x ↦ tuple' fun i ↦ by
    if h : i.val = 0 then
      have : i = ⟨0, by simp⟩ := by ext; exact h
      rw [this]; exact fst x
    else
      have : i = ⟨1, by simp⟩ := by ext; have hi := i.property; rw [mem_pair] at hi; tauto
      rw [this]; exact snd x
  left_inv := by
    intro ⟨t, ht⟩; simp only [fst_of_mk_cartesian, snd_of_mk_cartesian, eq_mpr_eq_cast]
    have ⟨x, hx⟩ := (mem_iProd t).mp ht;
    ext; simp only [hx, coe_of_fun_inj]
    funext ⟨i, hi⟩; simp only [Subtype.mk_eq_mk, Subtype.val_inj, tupleToFn_tuple_eq]
    rw [mem_pair] at hi; grind
  right_inv := by intro; simp

/-- Example 3.5.10 -/
noncomputable abbrev SetTheory.Set.iProd_equiv_prod_triple (X: ({0,1,2}:Set) → Set) :
    iProd X ≃ (X ⟨ 0, by simp ⟩) ×ˢ (X ⟨ 1, by simp ⟩) ×ˢ (X ⟨ 2, by simp ⟩) where
  toFun := fun t ↦ let x := tupleToFn t; mk_cartesian (
      x ⟨0, by simp⟩) (mk_cartesian (x ⟨1, by simp⟩) (x ⟨2, by simp⟩))
  invFun := fun x ↦ tuple' fun i ↦ by
    if h : i.val = 0 then
      have : i = ⟨0, by simp⟩ := by ext; exact h
      rw [this]; exact fst x
    else if h' : i.val = 1 then
      have : i = ⟨1, by simp⟩ := by ext; exact h'
      rw [this]; exact fst (snd x)
    else
      have : i = ⟨2, by simp⟩ := by ext; have hi := i.property; rw [mem_triple] at hi; tauto
      rw [this]; exact snd (snd x)
  left_inv := by
    intro ⟨t, ht⟩;
    have ⟨x, hx⟩ := (mem_iProd t).mp ht;
    ext; simp only [hx, tupleToFn_tuple_eq, eq_mpr_eq_cast, coe_of_fun_inj,
        fst_of_mk_cartesian, snd_of_mk_cartesian]
    funext ⟨i, hi⟩; simp only [Subtype.mk_eq_mk, Subtype.val_inj]
    rw [mem_triple] at hi; grind
  right_inv := by intro; simp

/-- Connections with Mathlib's `Set.pi` -/
noncomputable abbrev SetTheory.Set.iProd_equiv_pi (I:Set) (X: I → Set) :
    iProd X ≃ Set.pi .univ (fun i:I ↦ ((X i):_root_.Set Object)) where
  toFun t := ⟨fun i ↦ ((mem_iProd _).mp t.property).choose i, by simp⟩
  invFun x :=
    ⟨tuple fun i ↦ ⟨x.val i, by have := x.property i; simpa⟩, by apply tuple_mem_iProd⟩
  left_inv t := by ext; rw [((mem_iProd _).mp t.property).choose_spec, tuple_inj]
  right_inv x := by
    ext; dsimp
    generalize_proofs _ h
    rw [←(tuple_inj _ _).mp h.choose_spec]


/-
remark: there are also additional relations between these equivalences, but this begins to drift
into the field of higher order category theory, which we will not pursue here.
-/

/--
  Here we set up some an analogue of Mathlib `Fin n` types within the Chapter 3 Set Theory,
  with rudimentary API.
-/
abbrev SetTheory.Set.Fin (n:ℕ) : Set := nat.specify (fun m ↦ (m:ℕ) < n)

theorem SetTheory.Set.mem_Fin (n:ℕ) (x:Object) : x ∈ Fin n ↔ ∃ m, m < n ∧ x = m := by
  rw [specification_axiom'']; constructor
  . intro ⟨ h1, h2 ⟩; use ↑(⟨ x, h1 ⟩:nat); simp [h2]
  intro ⟨ m, hm, h ⟩
  use (by rw [h, ←Object.ofnat_eq]; exact (m:nat).property)
  grind [Object.ofnat_eq''']

abbrev SetTheory.Set.Fin_mk (n m:ℕ) (h: m < n): Fin n := ⟨ m, by rw [mem_Fin]; use m ⟩

theorem SetTheory.Set.mem_Fin' {n:ℕ} (x:Fin n) : ∃ m, ∃ h : m < n, x = Fin_mk n m h := by
  choose m hm this using (mem_Fin _ _).mp x.property; use m, hm
  simp [Fin_mk, ←Subtype.val_inj, this]

@[coe]
noncomputable abbrev SetTheory.Set.Fin.toNat {n:ℕ} (i: Fin n) : ℕ := (mem_Fin' i).choose

noncomputable instance SetTheory.Set.Fin.inst_coeNat {n:ℕ} : CoeOut (Fin n) ℕ where
  coe := toNat

theorem SetTheory.Set.Fin.toNat_spec {n:ℕ} (i: Fin n) :
    ∃ h : i < n, i = Fin_mk n i h := (mem_Fin' i).choose_spec

theorem SetTheory.Set.Fin.toNat_lt {n:ℕ} (i: Fin n) : i < n := (toNat_spec i).choose

@[simp]
theorem SetTheory.Set.Fin.coe_toNat {n:ℕ} (i: Fin n) : ((i:ℕ):Object) = (i:Object) := by
  set j := (i:ℕ); obtain ⟨ h, h':i = Fin_mk n j h ⟩ := toNat_spec i; rw [h']

@[simp low]
lemma SetTheory.Set.Fin.coe_inj {n:ℕ} {i j: Fin n} : i = j ↔ (i:ℕ) = (j:ℕ) := by
  constructor
  · simp_all
  obtain ⟨_, hi⟩ := toNat_spec i
  obtain ⟨_, hj⟩ := toNat_spec j
  grind

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff {n:ℕ} (i: Fin n) {j:ℕ} : (i:Object) = (j:Object) ↔ i = j := by
  constructor
  · intro h
    rw [Subtype.coe_eq_iff] at h
    obtain ⟨_, rfl⟩ := h
    simp [←Object.natCast_inj]
  aesop

@[simp]
theorem SetTheory.Set.Fin.coe_eq_iff' {n m:ℕ} (i: Fin n) (hi : ↑i ∈ Fin m) : ((⟨i, hi⟩ : Fin m):ℕ) = (i:ℕ) := by
  obtain ⟨val, property⟩ := i
  simp only [toNat, Subtype.mk.injEq, exists_prop]
  generalize_proofs h1 h2
  suffices : (h1.choose: Object) = h2.choose
  · aesop
  have := h1.choose_spec
  have := h2.choose_spec
  grind

@[simp]
theorem SetTheory.Set.Fin.toNat_mk {n:ℕ} (m:ℕ) (h: m < n) : (Fin_mk n m h : ℕ) = m := by
  have := coe_toNat (Fin_mk n m h)
  rwa [Object.natCast_inj] at this

abbrev SetTheory.Set.Fin_embed (n N:ℕ) (h: n ≤ N) (i: Fin n) : Fin N := ⟨ i.val, by
  have := i.property; rw [mem_Fin] at *; grind
⟩

/-- Connections with Mathlib's `Fin n` -/
noncomputable abbrev SetTheory.Set.Fin.Fin_equiv_Fin (n:ℕ) : Fin n ≃ _root_.Fin n where
  toFun m := _root_.Fin.mk m (toNat_lt m)
  invFun m := Fin_mk n m.val m.isLt
  left_inv m := (toNat_spec m).2.symm
  right_inv m := by simp

/-- Lemma 3.5.11 (finite choice) -/
theorem SetTheory.Set.finite_choice {n:ℕ} {X: Fin n → Set} (h: ∀ i, X i ≠ ∅) : iProd X ≠ ∅ := by
  -- This proof broadly follows the one in the text
  -- (although it is more convenient to induct from 0 rather than 1)
  induction' n with n hn
  . have : Fin 0 = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      grind [specification_axiom'']
    have empty (i:Fin 0) : X i := False.elim (by rw [this] at i; exact not_mem_empty i i.property)
    apply nonempty_of_inhabited (x := tuple empty); rw [mem_iProd]; use empty
  set X' : Fin n → Set := fun i ↦ X (Fin_embed n (n+1) (by linarith) i)
  have hX' (i: Fin n) : X' i ≠ ∅ := h _
  choose x'_obj hx' using nonempty_def (hn hX')
  rw [mem_iProd] at hx'; obtain ⟨ x', rfl ⟩ := hx'
  set last : Fin (n+1) := Fin_mk (n+1) n (by linarith)
  choose a ha using nonempty_def (h last)
  have x : ∀ i, X i := fun i =>
    if h : i = n then
      have : i = last := by ext; simpa [←Fin.coe_toNat, last]
      ⟨a, by grind⟩
    else
      have : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Fin.toNat_lt i)) h
      let i' := Fin_mk n i this
      have : X i = X' i' := by simp [X', i', Fin_embed]
      ⟨x' i', by grind⟩
  exact nonempty_of_inhabited (tuple_mem_iProd x)

/-- Exercise 3.5.1, second part (requires axiom of regularity) -/
abbrev OrderedPair.toObject' : OrderedPair ↪ Object where
  toFun p := ({ p.fst, (({p.fst, p.snd}:Set):Object) }:Set)
  inj' := by
    intro ⟨a, b⟩ ⟨a', b'⟩ h; simp only [coe_eq_iff] at h; apply pair_eq_pair at h
    rw [OrderedPair.eq]
    cases' h with h h
    . obtain ⟨ha, hab⟩ := h; subst a'
      rw [coe_eq_iff] at hab; apply pair_eq_pair at hab
      grind
    . obtain ⟨ha, ha'⟩ := h; rw [←ha'] at ha
      have := not_mem_mem {(({a, b}: Set): Object), b'} {a, b}
      simp only [mem_pair, true_or, not_true_eq_false, or_false, not_or] at this
      grind


/-- An alternate definition of a tuple, used in Exercise 3.5.2 -/
structure SetTheory.Set.Tuple (n:ℕ) where
  X: Set
  x: Fin n → X
  surj: Function.Surjective x

/--
  Custom extensionality lemma for Exercise 3.5.2.
  Placing `@[ext]` on the structure would generate a lemma requiring proof of `t.x = t'.x`,
  but these functions have different types when `t.X ≠ t'.X`. This lemma handles that part.
-/
@[ext]
lemma SetTheory.Set.Tuple.ext {n:ℕ} {t t':Tuple n}
    (hX : t.X = t'.X)
    (hx : ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object)) :
    t = t' := by
  have ⟨_, _, _⟩ := t; have ⟨_, _, _⟩ := t'; subst hX; congr; ext; grind

/-- Exercise 3.5.2 -/
theorem SetTheory.Set.Tuple.eq {n:ℕ} (t t':Tuple n) :
    t = t' ↔ ∀ n : Fin n, ((t.x n):Object) = ((t'.x n):Object) := by
  constructor
  . grind
  . intro h; ext y
    . constructor <;> intro hy <;> [have ⟨x, hx⟩ := t.surj ⟨y, hy⟩; have ⟨x, hx⟩ := t'.surj ⟨y, hy⟩]
      all_goals
        specialize h x; simp only [hx, ←exists_subtype_mk_eq_iff, ←exists_eq_subtype_mk_iff] at h
        exact h.fst
    . specialize h y; assumption

noncomputable abbrev SetTheory.Set.iProd_equiv_tuples (n:ℕ) (X: Fin n → Set) :
    iProd X ≃ { t:Tuple n // ∀ i, (t.x i:Object) ∈ X i } where
  toFun := fun t ↦
      let x := tupleToFn t
      ⟨Tuple.mk
          (iUnion (Fin n) fun i ↦ {(x i).val})
          (fun (i : Fin n) ↦ ⟨x i, by simp only [mem_iUnion, mem_singleton]; use i⟩)
          (by intro ⟨y, hy⟩; simp only [mem_iUnion, mem_singleton] at hy; grind),
          by intro i; simp [(x i).property]⟩
  invFun := fun ⟨x, hx⟩ ↦ tuple' fun i ↦ ⟨x.x i, by grind⟩
  left_inv := by intro t; simp
  right_inv := by
    intro ⟨x, hx⟩; ext x'
    . simp only [tupleToFn_tuple_eq, mem_iUnion, mem_singleton]
      constructor
      . intro ⟨i, hx'⟩
        have := (x.x i).property; rwa [hx']
      . intro hx'
        have ⟨i, hi⟩ := x.surj ⟨x', hx'⟩; simp only [Subtype.ext_iff_val] at hi
        use i; exact hi.symm
    . simp

/--
  Exercise 3.5.3. The spirit here is to avoid direct rewrites (which make all of these claims
  trivial), and instead use `OrderedPair.eq` or `SetTheory.Set.tuple_inj`
-/
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  rw [OrderedPair.eq]
  constructor <;> rfl

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  constructor
  . intro h; rw [OrderedPair.eq] at h ⊢
    constructor
    . exact h.left.symm
    . exact h.right.symm
  . intro h; exact h.symm

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  rw [OrderedPair.eq] at hpq hqr ⊢
  rwa [hqr.left, hqr.right] at hpq

theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := by
  rw [tuple_inj]

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a := by
  constructor
  all_goals
    intro h; rw [tuple_inj] at h ⊢
    exact h.symm

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
  rw [tuple_inj] at hab hbc ⊢
  rwa [hbc] at hab

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_union (A B C:Set) : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  ext c; simp only [mem_cartesian, mem_union]
  constructor
  . intro ⟨x, ⟨y, hy⟩, hxy⟩; rw [mem_union] at hy
    cases hy <;> [left; right] <;> use x, ⟨y, by assumption⟩
  . intro h
    cases' h with h h <;> obtain ⟨x, ⟨y, hy⟩, h⟩ := h <;> use x, ⟨y, by simp_all⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_inter (A B C:Set) : A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  ext c; simp only [mem_cartesian, mem_inter]
  constructor
  . intro ⟨x, ⟨y, hy⟩, hxy⟩; rw [mem_inter] at hy
    constructor
    . use x, ⟨y, hy.left⟩
    . use x, ⟨y, hy.right⟩
  . rintro ⟨⟨x, ⟨y, hy⟩, hxy⟩, ⟨x', ⟨y', hy'⟩, hxy'⟩⟩
    have h := hxy
    rw [hxy', EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq, Subtype.val_inj,
        ←exists_eq_subtype_mk_iff] at h
    use x, ⟨y, by rw [mem_inter]; grind⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.prod_diff (A B C:Set) : A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  ext c; simp only [mem_cartesian, mem_sdiff]
  constructor
  . intro ⟨x, ⟨y, hy⟩, hc⟩; simp only [mem_sdiff] at hy
    subst c; simp [hy]
  . intro ⟨⟨x, ⟨y, hy⟩, hc⟩, h⟩
    simp only [not_exists, hc, EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq] at h
    specialize h x; simp only [true_and, Subtype.forall] at h
    have : y ∉ C := by intro hy; specialize h y hy; contradiction
    use x, ⟨y, by simp_all⟩

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.union_prod (A B C:Set) : (A ∪ B) ×ˢ C = (A ×ˢ C) ∪ (B ×ˢ C) := by
  ext c; simp only [mem_cartesian, mem_union]
  constructor
  . intro ⟨⟨x, hx⟩, y, hxy⟩; rw [mem_union] at hx
    cases hx <;> [left; right] <;> use ⟨x, by assumption⟩, y
  . intro h
    cases' h with h h <;> obtain ⟨⟨x, hx⟩, y, h⟩ := h <;> use ⟨x, by simp_all⟩, y

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.inter_prod (A B C:Set) : (A ∩ B) ×ˢ C = (A ×ˢ C) ∩ (B ×ˢ C) := by
  ext c; simp only [mem_cartesian, mem_inter]
  constructor
  . intro ⟨⟨x, hx⟩, y, hxy⟩; rw [mem_inter] at hx
    constructor
    . use ⟨x, hx.left⟩, y
    . use ⟨x, hx.right⟩, y
  . rintro ⟨⟨⟨x, hx⟩, y, hxy⟩, ⟨⟨x', hx'⟩, y', hxy'⟩⟩
    have h := hxy
    rw [hxy', EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq, Subtype.val_inj,
        ←exists_eq_subtype_mk_iff] at h
    use ⟨x, by rw [mem_inter]; grind⟩, y

/-- Exercise 3.5.4 -/
theorem SetTheory.Set.diff_prod (A B C:Set) : (A \ B) ×ˢ C = (A ×ˢ C) \ (B ×ˢ C) := by
  ext c; simp only [mem_cartesian, mem_sdiff]
  constructor
  . intro ⟨⟨x, hx⟩, y, hc⟩; simp only [mem_sdiff] at hx
    subst c; simp [hx]
  . intro ⟨⟨⟨x, hx⟩, y, hc⟩, h⟩
    simp only [not_exists, hc, EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq] at h
    have : x ∉ B := by intro hx; specialize h ⟨x, hx⟩ y; simp_all
    use ⟨x, by simp_all⟩, y

/-- Exercise 3.5.5 -/
theorem SetTheory.Set.inter_of_prod (A B C D:Set) :
    (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  ext c; simp only [mem_cartesian, mem_inter]
  constructor
  . intro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩, ⟨⟨x', hx'⟩, ⟨y', hy'⟩, h'⟩⟩
    simp only [h', EmbeddingLike.apply_eq_iff_eq, OrderedPair.eq] at h
    obtain ⟨hxx', hyy'⟩ := h; subst x' y'
    use ⟨x, by simp_all⟩, ⟨y, by simp_all⟩
  . intro ⟨⟨x, hx⟩, ⟨y, hy⟩, h⟩
    rw [mem_inter] at hx hy
    constructor <;> use ⟨x, by tauto⟩, ⟨y, by tauto⟩

/- Exercise 3.5.5 -/
def SetTheory.Set.union_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro h; specialize h ∅ {0} {0} ∅
  simp [SetTheory.Set.ext_iff] at h

/- Exercise 3.5.5 -/
def SetTheory.Set.diff_of_prod :
  Decidable (∀ (A B C D:Set), (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D)) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro h; specialize h {0} {0} {0} {1}
  simp [SetTheory.Set.ext_iff] at h

/--
  Exercise 3.5.6.
-/
theorem SetTheory.Set.prod_subset_prod {A B C D:Set}
  (hA: A ≠ ∅) (hB: B ≠ ∅) (hC: C ≠ ∅) (hD: D ≠ ∅) :
    A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D := by
  have ⟨a, ha⟩ := nonempty_def hA
  have ⟨b, hb⟩ := nonempty_def hB
  constructor
  . intro h
    constructor <;>
    intro x hx <;> [
      let c := mk_cartesian ⟨x, hx⟩ ⟨b, hb⟩;
      let c := mk_cartesian ⟨a, ha⟩ ⟨x, hx⟩] <;>
    specialize h c.val c.property <;>
    simp only [mem_cartesian, pair_eq_fst_snd, EmbeddingLike.apply_eq_iff_eq,
        OrderedPair.eq, fst_of_mk_cartesian, snd_of_mk_cartesian] at h <;>
    grind
  . intro h c hc; rw [mem_cartesian] at hc; obtain ⟨x, y, hc⟩ := hc
    rw [mem_cartesian]
    use ⟨x, h.left x.val x.prop⟩, ⟨y, h.right y.val y.prop⟩

def SetTheory.Set.prod_subset_prod' :
  Decidable (∀ (A B C D:Set), A ×ˢ B ⊆ C ×ˢ D ↔ A ⊆ C ∧ B ⊆ D) := by
  -- the first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro h; specialize h {0} ∅ ∅ ∅
  have := h.mp ?_
  . simp only [subset_self, and_true] at this
    have zero_mem := (mem_singleton 0 0).mpr rfl
    specialize this 0 zero_mem
    exact not_mem_empty 0 this
  . intro; simp

/-- Exercise 3.5.7 -/
theorem SetTheory.Set.direct_sum {X Y Z:Set} (f: Z → X) (g: Z → Y) :
    ∃! h: Z → X ×ˢ Y, fst ∘ h = f ∧ snd ∘ h = g := by
  let h (z: Z) : X ×ˢ Y := mk_cartesian (f z) (g z)
  use h; dsimp
  constructor
  . constructor <;> ext z <;> simp
  . intro h' hh'; ext z
    simp only [funext_iff, ←forall_and, Function.comp_apply] at hh'
    specialize hh' z
    have ⟨x', y', h'z⟩ := mem_cartesian' (h' z)
    simp only [h'z, fst_of_mk_cartesian, snd_of_mk_cartesian] at hh'
    simp [mk_cartesian, h'z, h, hh']

/-- Exercise 3.5.8 -/
@[simp]
theorem SetTheory.Set.iProd_empty_iff {n:ℕ} {X: Fin n → Set} :
    iProd X = ∅ ↔ ∃ i, X i = ∅ := by
  constructor
  . intro h; by_contra h'; rw [not_exists] at h'
    have := not_mem_empty; simp only [←h, mem_iProd, not_exists] at this
    let x (i : Fin n) : X i := nonempty_choose (h' i)
    specialize this (tuple x) x; contradiction
  . intro ⟨i, hi⟩; ext t
    simp only [not_mem_empty, iff_false, mem_iProd, not_exists]
    intro x; specialize x i
    have := not_mem_empty; rw [←hi] at this
    grind

/-- Exercise 3.5.9-/
theorem SetTheory.Set.iUnion_inter_iUnion {I J: Set} (A: I → Set) (B: J → Set) :
    (iUnion I A) ∩ (iUnion J B) = iUnion (I ×ˢ J) (fun p ↦ (A (fst p)) ∩ (B (snd p))) := by
  ext x; simp only [mem_inter, mem_iUnion]
  constructor
  . intro ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
    use mk_cartesian α β
    simp only [fst_of_mk_cartesian, snd_of_mk_cartesian]
    tauto
  . intro ⟨t, ht⟩
    constructor
    . use fst t; tauto
    . use snd t; tauto

abbrev SetTheory.Set.graph {X Y:Set} (f: X → Y) : Set :=
  (X ×ˢ Y).specify (fun p ↦ (f (fst p) = snd p))

/-- Exercise 3.5.10 -/
theorem SetTheory.Set.graph_inj {X Y:Set} (f f': X → Y) :
    graph f = graph f' ↔ f = f' := by
  constructor
  . intro h; ext x
    simp only [SetTheory.Set.ext_iff, specification_axiom''] at h
    specialize h (mk_cartesian x (f x))
    simp only [mem_cartesian, fst_of_mk_cartesian, snd_of_mk_cartesian, mk_cartesian, EmbeddingLike.apply_eq_iff_eq,
        OrderedPair.eq, exists_const, exists_and_left, exists_apply_eq_apply', and_true, true_iff] at h
    tauto
  . tauto

set_option pp.proofs true in
theorem SetTheory.Set.is_graph {X Y G:Set} (hG: G ⊆ X ×ˢ Y)
  (hvert: ∀ x:X, ∃! y:Y, ((⟨x,y⟩:OrderedPair):Object) ∈ G) :
    ∃! f: X → Y, G = graph f := by
  let f (x : X) : Y := (hvert x).choose
  use f; dsimp
  suffices G = graph f by simp [this, graph_inj]
  ext xy
  simp only [specification_axiom'']
  constructor
  . intro hxy
    specialize hG xy hxy; use hG
    have := hvert (fst ⟨xy, hG⟩) |>.choose_spec.right (snd ⟨xy, hG⟩)
    simp only [←pair_eq_fst_snd] at this
    grind
  . intro ⟨hxy, h⟩
    have := hvert (fst ⟨xy, hxy⟩) |>.choose_spec.left
    dsimp [f] at h; rwa [h, ←pair_eq_fst_snd] at this

/--
  Exercise 3.5.11. This trivially follows from `SetTheory.Set.powerset_axiom`, but the
  exercise is to derive it from `SetTheory.Set.exists_powerset` instead.
-/
theorem SetTheory.Set.powerset_axiom' (X Y:Set) :
    ∃! S:Set, ∀(F:Object), F ∈ S ↔ ∃ f: Y → X, f = F := by
  have ⟨Z, hZ⟩ := exists_powerset (Y ×ˢ X)
  let Zf := Z.replace (P := fun s F ↦ ∃ S : Set, ∃ f : Y → X, S = s.val ∧ f = F ∧
      ∀ y : Y, ↑(OrderedPair.mk y (f y)) ∈ S ∧
      ∀ x : X, ↑(OrderedPair.mk y x) ∈ S → x = f y)
      (by
        rintro s _ _ ⟨⟨S, f, hS, rfl, h⟩, ⟨S', f', hS', rfl, h'⟩⟩
        rw [←hS', coe_eq_iff] at hS; subst S'
        congr; grind)

  have f_in_Zf (f : Y → X) : ↑f ∈ Zf := by
    let z := Y.replace (P := fun y z ↦
        ∃ hz : z ∈ Y ×ˢ X, y = fst ⟨z, hz⟩ ∧ f y = snd ⟨z, hz⟩)
        (by
          rintro ⟨y, hy⟩ z z' ⟨⟨hz, hf, hs⟩, ⟨hz', hf', hs'⟩⟩
          have h₁ := mk_cartesian_fst_snd_eq ⟨z, hz⟩
          have h₂ := mk_cartesian_fst_snd_eq ⟨z', hz'⟩
          grind)
    have hz : ↑z ∈ Z := by
      apply (hZ z).mpr
      use z; simp only [true_and]
      intro x hx; simp only [z, replacement_axiom] at hx
      grind
    simp only [Zf, replacement_axiom]
    use ⟨z, hz⟩, z, f; simp only [true_and, z, replacement_axiom]
    simp

  use Zf
  constructor
  . intro F
    constructor
    . grind [replacement_axiom]
    . rintro ⟨f, rfl⟩; exact f_in_Zf f
  . intro S hF; ext F
    specialize hF F
    constructor
    . intro h
      have ⟨f, hf⟩ := hF.mp h
      subst F; exact f_in_Zf f
    . grind [replacement_axiom]

/-- Exercise 3.5.12, with errata from web site incorporated -/
theorem SetTheory.Set.recursion (X: Set) (f: nat → X → X) (c:X) :
    ∃! a: nat → X, a 0 = c ∧ ∀ n, a (n + 1:ℕ) = f n (a n) := by
  let a (n : nat) : X := (n : ℕ).rec c fun n x => f n x
  use a; and_intros
  . simp [a]
  . intro n; simp [a]
  . intro a' ⟨ha0', ha'⟩
    ext x; simp only [a]
    induction' h : (x : ℕ) with n ih generalizing x
    . rw [←nat_equiv_coe_of_coe'' 0, nat_equiv_symm_inj] at h
      rw [←h] at ha0'
      simp_all
    . specialize ha' n; rw [←h, nat_equiv_coe_of_coe'] at ha'
      specialize ih n
      simp only [nat_equiv_coe_of_coe, true_implies, Subtype.val_inj] at ih
      simp_all

/-- Exercise 3.5.13 -/
theorem SetTheory.Set.nat_unique (nat':Set) (zero:nat') (succ:nat' → nat')
  (succ_ne: ∀ n:nat', succ n ≠ zero) (succ_of_ne: ∀ n m:nat', n ≠ m → succ n ≠ succ m)
  (ind: ∀ P: nat' → Prop, P zero → (∀ n, P n → P (succ n)) → ∀ n, P n) :
    ∃! f : nat → nat', Function.Bijective f ∧ f 0 = zero
    ∧ ∀ (n:nat) (n':nat'), f n = n' ↔ f (n+1:ℕ) = succ n' := by
  have nat_coe_eq {m:nat} {n} : (m:ℕ) = n → m = n := by aesop
  have nat_coe_eq_zero {m:nat} : (m:ℕ) = 0 → m = 0 := nat_coe_eq
  obtain ⟨f, hf⟩ := recursion nat' (fun _ n' ↦ succ n') zero
  apply existsUnique_of_exists_of_unique
  · use f
    constructor
    · constructor
      · intro x1 x2 heq
        induction' hx1: (x1:ℕ) with i ih generalizing x1 x2
        · apply nat_coe_eq_zero at hx1; subst x1
          rw [hf.left.left] at heq
          cases hx2 : (x2 : ℕ) <;> grind
        . apply nat_coe_eq at hx1; subst x1
          cases' hx2: (x2 : ℕ) with i'
          . grind
          . apply nat_coe_eq at hx2; subst x2
            simp only [hf.left.right] at heq
            simp only [not_imp_not] at succ_of_ne
            apply succ_of_ne at heq
            apply ih at heq
            simp only [nat_equiv_coe_of_coe, nat_equiv_inj, forall_const] at heq
            rw [heq]
      . intro n'
        induction' n' using ind with n' ih
        . use 0; exact hf.left.left
        . obtain ⟨n, ih⟩ := ih
          use (n: ℕ) + (1: ℕ)
          rw [hf.left.right, nat_equiv_coe_of_coe', ih]
    . use hf.left.left; intro n n'
      simp only [hf.left.right, nat_equiv_coe_of_coe']
      constructor
      . grind
      . simp only [not_imp_not] at succ_of_ne
        apply succ_of_ne
  . intro f₁ f₂ ⟨_, hf₁⟩ ⟨_, hf₂⟩
    suffices f₁ = f ∧ f₂ = f by grind
    constructor <;> [rename' hf₁ => hf'; rename' hf₂ => hf']
    all_goals
      apply hf.right
      simp only [hf'.left, true_and]
      intro n
      have := hf'.right n
      simp only [nat_equiv_coe_of_coe] at this
      rw [←this]


end Chapter3
