import Mathlib.Tactic
import Analysis.Section_3_5

/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.


Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Definition 3.6.1 (Equal cardinality) -/
abbrev SetTheory.Set.EqualCard (X Y:Set) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  use open Classical in fun x ↦
    ⟨if x.val = 0 then 3 else if x.val = 1 then 4 else 5, by aesop⟩
  constructor
  · intro; aesop
  intro y
  have : y = (3: Object) ∨ y = (4: Object) ∨ y = (5: Object) := by
    have := y.property
    aesop
  rcases this with (_ | _ | _)
  · use ⟨0, by simp⟩; aesop
  · use ⟨1, by simp⟩; aesop
  · use ⟨2, by simp⟩; aesop

/-- Example 3.6.3 -/
theorem SetTheory.Set.Example_3_6_3 : EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by
  use fun n ↦
    let res : nat :=  (2: ℕ) * (n: ℕ)
    ⟨res, by rw [specification_axiom'']; use res.prop, n; simp [res, two_mul]⟩
  simp only [Object.ofnat_eq]
  constructor
  . intro n n' h; simp_all
  . intro ⟨m, hm⟩
    rw [specification_axiom''] at hm
    obtain ⟨hm, n, hn⟩ := hm; rw [←two_mul] at hn
    use n; simp [←hn]

@[refl]
theorem SetTheory.Set.EqualCard.refl (X:Set) : EqualCard X X := by
  use id
  exact Function.bijective_id

@[symm]
theorem SetTheory.Set.EqualCard.symm {X Y:Set} (h: EqualCard X Y) : EqualCard Y X := by
  obtain ⟨f, hf⟩ := h
  have ⟨g, hg⟩ := Function.bijective_iff_has_inverse.mp hf
  use g; rw [Function.bijective_iff_has_inverse]
  use f; exact hg.symm

@[trans]
theorem SetTheory.Set.EqualCard.trans {X Y Z:Set} (h1: EqualCard X Y) (h2: EqualCard Y Z) : EqualCard X Z := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  use g ∘ f; exact Function.Bijective.comp hg hf

/-- Proposition 3.6.4 / Exercise 3.6.1 -/
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := ⟨ EqualCard, {refl, symm, trans} ⟩

/-- Definition 3.6.5 -/
abbrev SetTheory.Set.has_card (X:Set) (n:ℕ) : Prop := X ≈ Fin n

theorem SetTheory.Set.has_card_iff (X:Set) (n:ℕ) :
    X.has_card n ↔ ∃ f: X → Fin n, Function.Bijective f := by
  simp [has_card, HasEquiv.Equiv, Setoid.r, EqualCard]

/-- Remark 3.6.6 -/
theorem SetTheory.Set.Remark_3_6_6 (n:ℕ) :
    (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n)).has_card n := by
  have ex_fin (x : (nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n))) : ∃ x' : Fin n, x.val = ↑((x': ℕ) + 1) := by
    obtain ⟨x, hx⟩ := x
    rw [specification_axiom''] at hx
    obtain ⟨hx, x_ge, x_le⟩ := hx
    cases' h : ((⟨x, hx⟩ : nat) : ℕ) with x'
    . simp [h] at x_ge
    rw [h, ←Nat.lt_iff_add_one_le] at x_le
    refine ⟨⟨x', ?fin⟩, ?eq⟩
    . simp only [specification_axiom'', Object.ofnat_eq''']
      exact ⟨(x' : Nat).prop, x_le⟩
    . rw [Fin.toNat_mk x' x_le, ←h, Object.ofnat_eq'']

  rw [has_card_iff]
  choose f hf using ex_fin
  use f
  constructor
  . intro x x' hxx'
    have hx := hf x
    have hx' := hf x'
    rwa [hxx', ←hx', Subtype.val_inj] at hx
  . intro x'
    let sx' : ℕ := x' + 1
    have hsx' : ↑sx' ∈ nat.specify (fun x ↦ 1 ≤ (x:ℕ) ∧ (x:ℕ) ≤ n) := by
      simp only [specification_axiom'', Object.ofnat_eq''', sx', le_add_iff_nonneg_left, zero_le, true_and]
      use (sx' : Nat).prop
      rw [←Nat.lt_iff_add_one_le]
      apply Fin.toNat_lt
    use ⟨sx', hsx'⟩
    specialize hf ⟨sx', hsx'⟩
    simp only [sx', Object.natCast_inj, add_right_cancel_iff, ←Fin.coe_inj] at hf
    rw [hf]

/-- Example 3.6.7 -/
theorem SetTheory.Set.Example_3_6_7a (a:Object) : ({a}:Set).has_card 1 := by
  rw [has_card_iff]
  use fun _ ↦ Fin_mk _ 0 (by simp)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  use ⟨a, by simp⟩
  have := Fin.toNat_lt y
  simp_all

theorem SetTheory.Set.Example_3_6_7b {a b c d:Object} (hab: a ≠ b) (hac: a ≠ c) (had: a ≠ d)
    (hbc: b ≠ c) (hbd: b ≠ d) (hcd: c ≠ d) : ({a,b,c,d}:Set).has_card 4 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (
    if x.val = a then 0 else if x.val = b then 1 else if x.val = c then 2 else 3
  ) (by aesop)
  constructor
  · intro x1 x2 hf; aesop
  intro y
  have : y = (0:ℕ) ∨ y = (1:ℕ) ∨ y = (2:ℕ) ∨ y = (3:ℕ) := by
    have := Fin.toNat_lt y
    omega
  rcases this with (_ | _ | _ | _)
  · use ⟨a, by aesop⟩; aesop
  · use ⟨b, by aesop⟩; aesop
  · use ⟨c, by aesop⟩; aesop
  · use ⟨d, by aesop⟩; aesop

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.pos_card_nonempty {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) : X ≠ ∅ := by
  -- This proof is written to follow the structure of the original text.
  by_contra! this
  have hnon : Fin n ≠ ∅ := by
    apply nonempty_of_inhabited (x := 0); rw [mem_Fin]; use 0, (by omega); rfl
  rw [has_card_iff] at hX
  choose f hf using hX
  -- obtain a contradiction from the fact that `f` is a bijection from the empty set to a
  -- non-empty set.
  simp only [Nat.one_le_iff_ne_zero, Nat.ne_zero_iff_zero_lt] at h
  have ⟨⟨x, hx⟩, _⟩ := hf.right (Fin_mk n 0 h)
  subst X; exact not_mem_empty x hx

/-- Exercise 3.6.2a -/
theorem SetTheory.Set.has_card_zero {X:Set} : X.has_card 0 ↔ X = ∅ := by
  simp only [has_card_iff]
  constructor
  . intro ⟨f, hf⟩
    by_contra!
    have ⟨x, hx⟩ := nonempty_def this
    have y := f ⟨x, hx⟩
    have := Fin.toNat_lt y
    contradiction
  . intro hX
    have f : X → Fin 0 := by intro ⟨x, hx⟩; subst X; absurd hx; apply not_mem_empty
    use f
    constructor
    . intro ⟨x, hx⟩; subst X; absurd hx; apply not_mem_empty
    . intro y; have := Fin.toNat_lt y; contradiction

/-- Lemma 3.6.9 -/
theorem SetTheory.Set.card_erase {n:ℕ} (h: n ≥ 1) {X:Set} (hX: X.has_card n) (x:X) :
    (X \ {x.val}).has_card (n-1) := by
  -- This proof has been rewritten from the original text to try to make it friendlier to
  -- formalize in Lean.
  rw [has_card_iff] at hX; choose f hf using hX
  set X' : Set := X \ {x.val}
  set ι : X' → X := fun ⟨y, hy⟩ ↦ ⟨ y, by aesop ⟩
  observe hι : ∀ x:X', (ι x:Object) = x
  choose m₀ hm₀ hm₀f using (mem_Fin _ _).mp (f x).property
  set g : X' → Fin (n-1) := fun x' ↦
    let := Fin.toNat_lt (f (ι x'))
    let : (f (ι x'):ℕ) ≠ m₀ := by
      by_contra!; simp [←this, Subtype.val_inj, hf.1.eq_iff, ι] at hm₀f
      have := x'.property; aesop
    if h' : f (ι x') < m₀ then Fin_mk _ (f (ι x')) (by omega)
    else Fin_mk _ (f (ι x') - 1) (by omega)
  have hg_def (x':X') : if (f (ι x'):ℕ) < m₀ then (g x':ℕ) = f (ι x') else (g x':ℕ) = f (ι x') - 1 := by
    split_ifs with h' <;> simp [g,h']
  have hg : Function.Bijective g := by
    rw [Fin.coe_eq_iff] at hm₀f
    constructor
    . intro x₁ x₂ hx₁x₂
      have hx₁ := hg_def x₁
      have hx₂ := hg_def x₂
      have rev_lt {x' : X'} (h : ¬↑(f (ι x')) < m₀) : m₀ < ↑(f (ι x')) := by
        rw [not_lt] at h
        apply Nat.lt_of_le_of_ne at h; apply h
        . intro h; simp only [←hm₀f, ←Fin.coe_inj, hf.injective.eq_iff, ι, Subtype.ext_iff] at h
          have hx := h.symm ▸ x'.prop; simp [X'] at hx
      split_ifs at hx₁ hx₂ with hx₁' hx₂' hx₂'
      all_goals
        rw [hx₁x₂, hx₂] at hx₁
        try replace hx₂' := rev_lt hx₂'
        try replace hx₁' := rev_lt hx₁'
      rotate_right
      case _ | _ => all_goals
        try replace hx₁ := Nat.sub_one_cancel (Nat.zero_lt_of_lt hx₂') (Nat.zero_lt_of_lt hx₁') hx₁
        simp only [←Fin.coe_inj, hf.injective.eq_iff, ι, Subtype.ext_iff] at hx₁
        rw [Subtype.ext_iff_val, hx₁]
      all_goals
        grind
    . intro y
      if h : y < m₀ then
        have ⟨⟨x', hx'X⟩, hx'⟩ := hf.surjective ⟨y, by simp only [mem_Fin, Fin.coe_eq_iff]; grind⟩
        have hx'X' : x' ∈ X' := by
          simp only [X', mem_sdiff, hx'X, true_and, mem_singleton]
          intro hxx'; subst x'; rw [hx', Fin.coe_eq_iff'] at hm₀f; grind
        use! x'; specialize hg_def ⟨x', hx'X'⟩
        simp_all
      else
        rw [not_lt] at h;  apply Nat.lt_add_one_of_le at h
        have hy : y + 1 < n := by have hy := y.prop; simp only [mem_Fin, Fin.coe_eq_iff] at hy; grind
        have ⟨⟨x', hx'X⟩, hx'⟩ := hf.surjective ⟨(y : ℕ) + (1 : ℕ), by simp only [mem_Fin]; grind⟩
        have hx'X' : x' ∈ X' := by
          simp only [X', mem_sdiff, hx'X, true_and, mem_singleton]
          intro hxx'; subst x'; rw [hx', Fin.toNat_mk _ hy] at hm₀f; grind
        use! x'; specialize hg_def ⟨x', hx'X'⟩
        simp_all only [Fin.toNat_mk, add_tsub_cancel_right, Fin.coe_inj]
        grind
  use g

/-- Proposition 3.6.8 (Uniqueness of cardinality) -/
theorem SetTheory.Set.card_uniq {X:Set} {n m:ℕ} (h1: X.has_card n) (h2: X.has_card m) : n = m := by
  -- This proof is written to follow the structure of the original text.
  revert X m; induction' n with n hn
  . intro _ _ h1 h2; rw [has_card_zero] at h1; contrapose! h1
    apply pos_card_nonempty _ h2; omega
  intro X m h1 h2
  have : X ≠ ∅ := pos_card_nonempty (by omega) h1
  choose x hx using nonempty_def this
  have : m ≠ 0 := by contrapose! this; simpa [has_card_zero, this] using h2
  specialize hn (card_erase ?_ h1 ⟨ _, hx ⟩) (card_erase ?_ h2 ⟨ _, hx ⟩) <;> omega

lemma SetTheory.Set.Example_3_6_8_a: ({0,1,2}:Set).has_card 3 := by
  rw [has_card_iff]
  have : ({0, 1, 2}: Set) = SetTheory.Set.Fin 3 := by
    ext x
    simp only [mem_insert, mem_singleton, mem_Fin]
    constructor
    · aesop
    rintro ⟨x, ⟨_, rfl⟩⟩
    simp only [nat_coe_eq_iff]
    omega
  rw [this]
  use id
  exact Function.bijective_id

lemma SetTheory.Set.Example_3_6_8_b: ({3,4}:Set).has_card 2 := by
  rw [has_card_iff]
  use open Classical in fun x ↦ Fin_mk _ (if x = (3:Object) then 0 else 1) (by aesop)
  constructor
  · intro x1 x2
    aesop
  intro y
  have := Fin.toNat_lt y
  have : y = (0:ℕ) ∨ y = (1:ℕ) := by omega
  aesop

lemma SetTheory.Set.Example_3_6_8_c : ¬({0,1,2}:Set) ≈ ({3,4}:Set) := by
  by_contra h
  have h1 : Fin 3 ≈ Fin 2 := (Example_3_6_8_a.symm.trans h).trans Example_3_6_8_b
  have h2 : Fin 3 ≈ Fin 3 := by rfl
  have := card_uniq h1 h2
  contradiction

abbrev SetTheory.Set.finite (X:Set) : Prop := ∃ n:ℕ, X.has_card n

abbrev SetTheory.Set.infinite (X:Set) : Prop := ¬ finite X

/-- Exercise 3.6.3, phrased using Mathlib natural numbers -/
theorem SetTheory.Set.bounded_on_finite {n:ℕ} (f: Fin n → nat) : ∃ M, ∀ i, (f i:ℕ) ≤ M := by
  induction' n with n ih
  . use 0; intro ⟨i, hi⟩; rw [mem_Fin] at hi; grind
  . let f' (i : Fin n) : nat := f ⟨i, by
      have hi := i.prop; simp only [mem_Fin, Fin.coe_eq_iff] at hi ⊢; grind⟩
    specialize ih f'; obtain ⟨m, hm⟩ := ih
    let l : ℕ := f (Fin_mk (n + 1) n (by grind))
    have ne_n_le_m (i : Fin (n + 1)) (h : ¬↑i = n) : ↑(f i) ≤ m := by
      have := Fin.toNat_lt i; apply Nat.le_of_lt_add_one at this; replace := Nat.lt_of_le_of_ne this h
      specialize hm (Fin_mk n i this); simpa [f'] using hm
    by_cases hl : l ≤ m
    . use m; intro i
      by_cases hi : i = n
      . simpa [l, ←hi, Fin_mk] using hl
      . grind
    . use l; intro i
      by_cases hi : i = n
      . simp [l, ←hi, Fin_mk]
      . grind

/-- Theorem 3.6.12 -/
theorem SetTheory.Set.nat_infinite : infinite nat := by
  -- This proof is written to follow the structure of the original text.
  by_contra this; choose n hn using this
  simp [has_card] at hn; symm at hn; simp [HasEquiv.Equiv, Setoid.r, EqualCard] at hn
  choose f hf using hn; choose M hM using bounded_on_finite f
  replace hf := hf.surjective ↑(M+1); contrapose! hf
  peel hM with hi; contrapose! hi
  apply_fun nat_equiv.symm at hi; simp_all

open Classical in
/-- It is convenient for Lean purposes to give infinite sets the ``junk`` cardinality of zero. -/
noncomputable def SetTheory.Set.card (X:Set) : ℕ := if h:X.finite then h.choose else 0

theorem SetTheory.Set.has_card_card {X:Set} (hX: X.finite) : X.has_card (SetTheory.Set.card X) := by
  simp [card, hX, hX.choose_spec]

theorem SetTheory.Set.has_card_to_card {X:Set} {n: ℕ}: X.has_card n → X.card = n := by
  intro h; simp [card, card_uniq (⟨ n, h ⟩:X.finite).choose_spec h]; aesop

theorem SetTheory.Set.card_to_has_card {X:Set} {n: ℕ} (hn: n ≠ 0): X.card = n → X.has_card n
  := by grind [card, has_card_card]

theorem SetTheory.Set.card_fin_eq (n:ℕ): (Fin n).has_card n := (has_card_iff _ _).mp ⟨ id, Function.bijective_id ⟩

theorem SetTheory.Set.Fin_card (n:ℕ): (Fin n).card = n := has_card_to_card (card_fin_eq n)

theorem SetTheory.Set.Fin_finite (n:ℕ): (Fin n).finite := ⟨n, card_fin_eq n⟩

theorem SetTheory.Set.EquivCard_to_has_card_eq {X Y:Set} {n: ℕ} (h: X ≈ Y): X.has_card n ↔ Y.has_card n := by
  choose f hf using h; let e := Equiv.ofBijective f hf
  constructor <;> (intro h'; rw [has_card_iff] at *; choose g hg using h')
  . use e.symm.trans (.ofBijective _ hg); apply Equiv.bijective
  . use e.trans (.ofBijective _ hg); apply Equiv.bijective

theorem SetTheory.Set.EquivCard_to_card_eq {X Y:Set} (h: X ≈ Y): X.card = Y.card := by
  by_cases hX: X.finite <;> by_cases hY: Y.finite <;> try rw [finite] at hX hY
  . choose nX hXn using hX; choose nY hYn using hY
    simp [has_card_to_card hXn, has_card_to_card hYn, EquivCard_to_has_card_eq h] at *
    solve_by_elim [card_uniq]
  . choose nX hXn using hX; rw [EquivCard_to_has_card_eq h] at hXn; tauto
  . choose nY hYn using hY; rw [←EquivCard_to_has_card_eq h] at hYn; tauto
  simp [card, hX, hY]

/-- Exercise 3.6.2 -/
theorem SetTheory.Set.empty_iff_card_eq_zero {X:Set} : X = ∅ ↔ X.finite ∧ X.card = 0 := by
  constructor
  . intro hX
    have := has_card_zero.mpr hX
    constructor
    . use 0
    . exact has_card_to_card this
  . intro hX
    rw [←has_card_zero]
    convert has_card_card hX.left; exact hX.right.symm

lemma SetTheory.Set.empty_of_card_eq_zero {X:Set} (hX : X.finite) : X.card = 0 → X = ∅ := by
  intro h
  rw [empty_iff_card_eq_zero]
  exact ⟨hX, h⟩

lemma SetTheory.Set.finite_of_empty {X:Set} : X = ∅ → X.finite := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.1

lemma SetTheory.Set.card_eq_zero_of_empty {X:Set} : X = ∅ → X.card = 0 := by
  intro h
  rw [empty_iff_card_eq_zero] at h
  exact h.2

@[simp]
lemma SetTheory.Set.empty_finite : (∅: Set).finite := finite_of_empty rfl

@[simp]
lemma SetTheory.Set.empty_card_eq_zero : (∅: Set).card = 0 := card_eq_zero_of_empty rfl

/-- Proposition 3.6.14 (a) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_insert {X:Set} (hX: X.finite) {x:Object} (hx: x ∉ X) :
    (X ∪ {x}).finite ∧ (X ∪ {x}).card = X.card + 1 := by
  obtain ⟨c, f, hf⟩ := hX
  have hc : c = X.card := by symm; apply has_card_to_card; use f
  open Classical in
  let f' (x' : (X ∪ {x} : Set)) : Fin (c + 1) :=
    if h : x' = x then
      Fin_mk _ c (by simp)
    else
      let y' := f ⟨x', by have := x'.prop; rw [mem_union, mem_singleton] at this; grind⟩
      Fin_mk _ y' (by observe : y' < c; grind)
  have hf : Function.Bijective f' := by
    constructor
    . intro x₁ x₂ hx₁x₂; rw [Subtype.eq_iff]
      unfold f' at hx₁x₂; split_ifs at hx₁x₂ with hx₁ hx₂ <;>
      simp only [Fin_mk, Fin.coe_toNat, Subtype.eq_iff] at hx₁x₂ <;>
      [skip; replace hx₁x₂ := hx₁x₂.symm; skip; skip]
      . rw [hx₁, hx₂]
      case _ | _ => all_goals
        rw [Fin.coe_eq_iff] at hx₁x₂
        set y := f ⟨_, _⟩
        have := Fin.toNat_lt y
        grind
      . simp only [Subtype.val_inj] at hx₁x₂
        simpa [hf.injective.eq_iff] using hx₁x₂
    . intro y
      by_cases hy : c = y
      . use ⟨x, by simp⟩; simpa [f']
      . have ⟨x', hx'⟩ := hf.surjective ⟨y, by
          observe : y < c + 1; observe : y ≤ c; observe : y < c
          simp only [mem_Fin]; use y; simpa⟩
        use ⟨x', by simp only [mem_union]; grind⟩
        have h : x' ≠ x := by intro h; rw [←h] at hx; exact hx x'.prop
        simpa [f', h] using hx'
  have : has_card (X ∪ {x}) (c + 1) := by rw [has_card_iff]; use f'
  constructor
  . use c + 1
  . apply has_card_to_card; grind

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ∪ Y).finite ∧ (X ∪ Y).card ≤ X.card + Y.card := by
  induction' hc : Y.card with c ih generalizing Y
  . apply empty_of_card_eq_zero hY at hc; subst Y; simp [hX]
  . have ⟨y, hy⟩ := not_imp_not.mpr card_eq_zero_of_empty (by grind: Y.card ≠ 0) |> nonempty_def
    have hY' := card_erase (by grind) (card_to_has_card (by grind) hc) ⟨y, hy⟩
    simp only [add_tsub_cancel_right] at hY'
    have ⟨XY'f, hXY'⟩ : (X ∪ Y \ {y}).finite ∧ (X ∪ Y \ {y}).card ≤ X.card + c := by
      apply ih
      . use c
      . exact has_card_to_card hY'
    by_cases hyX : y ∈ X
    . have : X ∪ Y \ {y} = X ∪ Y := by
        ext x; simp only [mem_union, mem_sdiff, mem_singleton]; grind
      simp only [←this, XY'f]; grind
    . replace hyX : y ∉ X ∪ Y \ {y} := by simpa
      have hXY := card_insert XY'f hyX
      have : X ∪ Y \ {y} ∪ {y} = X ∪ Y := by
        ext x; simp only [mem_union, mem_sdiff, mem_singleton]; grind
      simp only [←this, hXY]; grind

/-- Proposition 3.6.14 (b) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_union_disjoint {X Y:Set} (hX: X.finite) (hY: Y.finite)
  (hdisj: Disjoint X Y) : (X ∪ Y).card = X.card + Y.card := by
  suffices (X ∪ Y).finite ∧ _ from this.right
  induction' hc : Y.card with c ih generalizing Y
  . apply empty_of_card_eq_zero hY at hc; subst Y; simp [hX]
  . have ⟨y, hy⟩ := not_imp_not.mpr card_eq_zero_of_empty (by grind: Y.card ≠ 0) |> nonempty_def
    have hY' := card_erase (by grind) (card_to_has_card (by grind) hc) ⟨y, hy⟩
    simp only [add_tsub_cancel_right] at hY'
    have ⟨XY'f, hXY'⟩ : (X ∪ Y \ {y}).finite ∧ (X ∪ Y \ {y}).card = X.card + c := by
      apply ih
      . use c
      . simp only [disjoint_iff, Set.ext_iff, mem_inter, mem_sdiff, not_mem_empty] at hdisj ⊢
        grind
      . exact has_card_to_card hY'
    have hyXY' : y ∉ X ∪ Y \ {y} := by
      simp only [disjoint_iff, Set.ext_iff, mem_inter, not_mem_empty, iff_false] at hdisj
      specialize hdisj y; simpa [hy] using hdisj
    have hXY := card_insert XY'f hyXY'
    have : X ∪ Y \ {y} ∪ {y} = X ∪ Y := by
      ext x; simp only [mem_union, mem_sdiff, mem_singleton]; grind
    simpa [this, hXY'] using hXY

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_subset {X Y:Set} (hX: X.finite) (hY: Y ⊆ X) :
    Y.finite ∧ Y.card ≤ X.card := by
  induction' hc : X.card with c ih generalizing X
  . apply empty_of_card_eq_zero hX at hc; subst X
    have : Y = ∅ := by
      ext y; simp only [not_mem_empty, iff_false];
      intro hy; specialize hY y hy; exact not_mem_empty y hY
    subst Y; simp
  . by_cases hy' : Y = X
    . subst Y; simp [hX, hc]
    . have ⟨x, hx⟩ : ∃ x ∈ X, Y ⊆ X \ {x} := by
        contrapose! hy' with hX'
        ext x; constructor
        . specialize hY x; assumption
        . intro hx; specialize hX' x hx
          simp only [subset_def, not_forall, mem_sdiff, mem_singleton, not_and_not_right] at hX'
          obtain ⟨x', hx'Y, hx'⟩ := hX'; specialize hY x' hx'Y
          grind
      have hX' := card_erase (by grind : c + 1 ≥ 1) (card_to_has_card (by grind) hc) ⟨x, hx.left⟩
      simp only [add_tsub_cancel_right] at hX'
      set X' := X \ {x}
      specialize ih (by use c : X'.finite) hx.right (has_card_to_card hX')
      exact ⟨ih.left, Nat.le_add_right_of_le ih.right⟩

/-- Proposition 3.6.14 (c) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_ssubset {X Y:Set} (hX: X.finite) (hY: Y ⊂ X) :
    Y.card < X.card := by
  let X' := X \ Y
  have hX' : X' ⊆ X := by simp only [X', subset_def, mem_sdiff]; grind
  have ⟨hXf, _⟩ := card_subset hX hX'
  have hdisj : Disjoint Y X' := by
    rw [disjoint_iff]; ext x
    simp only [X', mem_inter, mem_sdiff, not_mem_empty]; grind
  have hYX' : Y ∪ X' = X := by
    ext x; simp only [mem_union, X', mem_sdiff]
    have := hY.left; specialize_all x; grind
  have := card_union_disjoint (card_subset hX hY.left).left hXf hdisj
  rw [hYX'] at this; simp only [this, lt_add_iff_pos_right, ←Nat.ne_zero_iff_zero_lt]
  intro h; apply empty_of_card_eq_zero hXf at h
  rw [h, union_empty] at hYX'; exact hY.right hYX'

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image {X Y:Set} (hX: X.finite) (f: X → Y) :
    (image f X).finite ∧ (image f X).card ≤ X.card := by
  suffices ∀ (X₀ : Set) (hX₀ : X ⊆ X₀) (f : X₀ → Y),
    (image f X).finite ∧ (image f X).card ≤ X.card from this X (subset_self X) f
  clear f
  intro X₀ hX₀ f
  induction' hc : X.card with c ih generalizing X
  . apply empty_of_card_eq_zero hX at hc; subst X
    have : image f ∅ = ∅ := by ext x; simp [↓mem_image]
    simp [this]
  . have ⟨x, hx⟩ := not_imp_not.mpr card_eq_zero_of_empty (by grind: X.card ≠ 0) |> nonempty_def
    have hX' := card_erase (by grind) (card_to_has_card (by grind) hc) ⟨x, hx⟩
    simp only [add_tsub_cancel_right] at hX'
    set X' := X \ {x}
    specialize ih ⟨c, hX'⟩
      (by intro x' hx'; simp only [X', mem_sdiff] at hx'; specialize hX₀ x'; grind)
      (has_card_to_card hX')
    let ix : Set := image f {x}
    let fx := f ⟨x, by specialize hX₀ x; grind⟩
    have hfx : ix = {↑fx} := by ext x'; simp only [ix, mem_image, mem_singleton]; grind
    have : image f X = image f X' ∪ ix := by
      ext x'; simp only [ix, X', ←image_of_union, mem_image, mem_union, mem_sdiff, mem_singleton];
      grind
    by_cases hix : ix ⊆ image f X'
    . replace : image f X = image f X' := by
        ext x; simp only [Set.ext_iff, mem_union] at this; specialize_all x; grind
      simp only [this, ih.left]; grind
    . have ixc : has_card ix 1 := by
        rw [hfx]; apply card_to_has_card (by decide)
        have := card_insert (by simp : (∅ : Set).finite) (by simp : ↑fx ∉ ∅) |>.right
        simpa using this
      have hd : Disjoint (image f X') ix := by
        rw [disjoint_iff]; ext x'
        simp only [not_mem_empty, iff_false, mem_inter, hfx, subset_def, mem_singleton] at hix ⊢
        grind
      have h := card_union_disjoint ih.left ⟨1, ixc⟩ hd
      simp only [h, this, has_card_to_card ixc, add_le_add_iff_right, ih, and_true]
      exact card_union ih.left ⟨1, ixc⟩ |>.left

/-- Proposition 3.6.14 (d) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_image_inj {X Y:Set} (hX: X.finite) {f: X → Y}
  (hf: Function.Injective f) : (image f X).card = X.card := by
  have ⟨c, hc⟩ := hX
  have ⟨c', hc'⟩ := card_image hX f |>.left
  rw [show (image f X).card = c' from has_card_to_card hc']
  symm; apply has_card_to_card
  have ⟨g, hg⟩ := hc'
  let f' (x : X) : Fin c' := g ⟨f x, by simp only [mem_image]; grind⟩
  use f'
  constructor
  . intro x x' h
    simp_rw [f', hg.injective.eq_iff, Subtype.eq_iff, Subtype.val_inj, hf.eq_iff] at h
    assumption
  . intro n; simp only [f']
    have ⟨y, hy⟩ := hg.surjective n
    have ⟨x, hx⟩ := mem_image f X y |>.mp y.prop
    grind

/-- Proposition 3.6.14 (e) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_prod {X Y:Set} (hX: X.finite) (hY: Y.finite) :
    (X ×ˢ Y).finite ∧ (X ×ˢ Y).card = X.card * Y.card := by
  have ⟨c, hc⟩ := hX; have ⟨d, hd⟩ := hY
  suffices (X ×ˢ Y).has_card (c * d) by
    use ⟨c * d, this⟩; apply_rw [has_card_to_card] at hc hd this; grind
  have ⟨f, hf⟩ := hc; have ⟨g, hg⟩ := hd
  have ⟨f₀, hf₀⟩ := Function.bijective_iff_has_inverse.mp hf
  have ⟨g₀, hg₀⟩ := Function.bijective_iff_has_inverse.mp hg
  have e₁ := Fin.Fin_equiv_Fin c
  have e₂ := Fin.Fin_equiv_Fin d
  have e₃ := @_root_.finProdFinEquiv c d
  have e₄ : X ×ˢ Y ≃ _root_.Fin (c * d) := ⟨
    fun x ↦ e₃ ⟨e₁ (f (fst x)), e₂ (g (snd x))⟩,
    fun y ↦ let ⟨x₁, x₂⟩ := e₃.invFun y; mk_cartesian (f₀ (e₁.invFun x₁)) (g₀ (e₂.invFun x₂)),
    fun x ↦ by simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply]; rw [hf₀.left, hg₀.left]; simp,
    fun y ↦ by simp only [Equiv.invFun_as_coe, fst_of_mk_cartesian, snd_of_mk_cartesian]; rw [hf₀.right, hg₀.right]; simp
  ⟩
  have e := Equiv.trans e₄ (Fin.Fin_equiv_Fin (c * d)).symm
  exact ⟨e, e.bijective⟩

noncomputable def SetTheory.Set.pow_fun_equiv {A B : Set} : ↑(A ^ B) ≃ (B → A) where
  toFun := fun F ↦ powerset_axiom F |>.mp F.prop |>.choose
  invFun := fun f ↦ ⟨f, by simp⟩
  left_inv := fun F ↦ by simp [powerset_axiom F |>.mp F.prop |>.choose_spec]
  right_inv := fun f ↦ by simp

lemma SetTheory.Set.pow_fun_eq_iff {A B : Set} (x y : ↑(A ^ B)) : x = y ↔ pow_fun_equiv x = pow_fun_equiv y := by
  rw [←pow_fun_equiv.apply_eq_iff_eq]

/-- Proposition 3.6.14 (f) / Exercise 3.6.4 -/
theorem SetTheory.Set.card_pow {X Y:Set} (hY: Y.finite) (hX: X.finite) :
    (Y ^ X).finite ∧ (Y ^ X).card = Y.card ^ X.card := by
  suffices (Y ^ X).has_card (Y.card ^ X.card) by
    use ⟨Y.card ^ X.card, this⟩; exact has_card_to_card this
  induction' hX' : X.card with c ih generalizing X
  . observe : X = ∅; subst X
    let f' (F : (Y ^ (∅ : Set)).toSubtype) : Fin 1 := Fin_mk 1 0 (by decide)
    rw [pow_zero]; use f'; constructor
    . intro F F' _; rw [pow_fun_eq_iff]
      ext x; absurd x.prop; simp
    . intro y
      use pow_fun_equiv.symm fun x ↦ by absurd x.prop; simp
      have := Fin.toNat_lt y; grind
  . have x : X := by
      have : X ≠ ∅ := by intro h; rw [card_eq_zero_of_empty h] at hX'; grind
      have := nonempty_def this
      exact ⟨this.choose, this.choose_spec⟩
    have := card_erase (by grind) (card_to_has_card (by grind) hX') x
    simp only [add_tsub_cancel_right] at this
    set X' := X \ {↑x}
    specialize ih ⟨c, this⟩ (has_card_to_card this)
    open Classical in
    have e : (Y ^ X : Set) ≃ (Y ^ X') ×ˢ Y := ⟨
      fun F ↦
        let f := pow_fun_equiv F
        mk_cartesian (pow_fun_equiv.symm fun ⟨x', hx'⟩ ↦
            f ⟨x', by grind [mem_sdiff]⟩) (f x),
      fun F ↦ pow_fun_equiv.symm fun x' ↦
        if h : x' = x then
          snd F
        else
          (pow_fun_equiv (fst F)) ⟨x', by grind [mem_sdiff, mem_singleton]⟩,
      fun F ↦ by
        simp only [snd_of_mk_cartesian, fst_of_mk_cartesian,
          Equiv.apply_symm_apply, pow_fun_eq_iff]; grind,
      fun F ↦ by
        simp only [Subtype.eq_iff, Equiv.apply_symm_apply, Subtype.coe_eta, dite_eq_ite,
          ↓reduceDIte];
        conv_rhs => rw [←mk_cartesian_fst_snd_eq F]
        congr; rw [pow_fun_eq_iff]; ext x'
        have := x'.prop; simp only [mem_sdiff, mem_singleton, X'] at this
        grind
    ⟩
    have ⟨hC, hC'⟩ := card_prod ⟨Y.card ^ c, ih⟩ hY
    apply has_card_card at hC; rw [hC'] at hC; clear hC'
    rw [has_card_to_card ih, ←Nat.pow_add_one] at hC
    obtain ⟨f, hf⟩ := hC
    exact ⟨f ∘ e, Function.Bijective.comp hf e.bijective⟩

/-- Exercise 3.6.5. You might find `SetTheory.Set.prod_commutator` useful. -/
theorem SetTheory.Set.prod_EqualCard_prod (A B:Set) :
    EqualCard (A ×ˢ B) (B ×ˢ A) := by
  have e := prod_commutator A B
  exact ⟨e, e.bijective⟩

noncomputable abbrev SetTheory.Set.pow_fun_equiv' (A B : Set) : ↑(A ^ B) ≃ (B → A) :=
  pow_fun_equiv (A:=A) (B:=B)

/-- Exercise 3.6.6. You may find `SetTheory.Set.curry_equiv` useful. -/
theorem SetTheory.Set.pow_pow_EqualCard_pow_prod (A B C:Set) :
    EqualCard ((A ^ B) ^ C) (A ^ (B ×ˢ C)) := by
  let g (F : ((A ^ B) ^ C).toSubtype) : (A ^ (B ×ˢ C)).toSubtype :=
    let f₁ (c : C) (b : B) : A :=
      pow_fun_equiv (pow_fun_equiv F c) b
    let f₂ (x : B ×ˢ C) : A :=
      curry_equiv f₁ (mk_cartesian (snd x) (fst x))
    pow_fun_equiv.symm f₂
  use g
  rw [Function.bijective_iff_has_inverse]
  use fun F ↦ pow_fun_equiv.symm fun c ↦ pow_fun_equiv.symm fun b ↦
    pow_fun_equiv F (mk_cartesian b c)
  simp [g, Function.LeftInverse, Function.RightInverse]

theorem SetTheory.Set.pow_pow_eq_pow_mul (a b c:ℕ): (a^b)^c = a^(b*c) := by
  have ⟨ab_f, ab_c⟩ := card_pow (Fin_finite a) (Fin_finite b)
  have ⟨abc_f, abc_c⟩ := card_pow ab_f (Fin_finite c)
  have ⟨bc_f', bc_c'⟩ := card_prod (Fin_finite b) (Fin_finite c)
  have ⟨abc_f', abc_c'⟩ := card_pow (Fin_finite a) bc_f'
  rw [←Fin_card a, ←Fin_card b, ←Fin_card c, ←ab_c, ←abc_c, ←bc_c', ←abc_c']
  have := pow_pow_EqualCard_pow_prod (Fin a) (Fin b) (Fin c)
  exact EquivCard_to_card_eq this

theorem SetTheory.Set.pow_prod_pow_EqualCard_pow_union (A B C:Set) (hd: Disjoint B C) :
    EqualCard ((A ^ B) ×ˢ (A ^ C)) (A ^ (B ∪ C)) := by
  open Classical in
  use fun F ↦ pow_fun_equiv.symm fun x ↦
    if h : ↑x ∈ B then
      pow_fun_equiv (fst F) ⟨↑x, h⟩
    else
      pow_fun_equiv (snd F) ⟨↑x, by have := x.prop; simpa [h] using this⟩
  rw [Function.bijective_iff_has_inverse]
  use fun G ↦
    let g := pow_fun_equiv G
    mk_cartesian
      (pow_fun_equiv.symm fun b ↦ g ⟨↑b, by simp [b.prop]⟩)
      (pow_fun_equiv.symm fun c ↦ g ⟨↑c, by simp [c.prop]⟩)
  replace hd : ∀ x, ↑x ∉ B ∨ ↑x ∉ C := by
    rw [disjoint_iff] at hd
    intro x; rw [←not_and_or, ←mem_inter, hd]
    apply not_mem_empty
  constructor
  . intro F
    beta_reduce; simp only [Equiv.apply_symm_apply, Subtype.coe_eta]
    conv_rhs => rw [←mk_cartesian_fst_snd_eq F]
    congr
    all_goals
      rw [←pow_fun_equiv.apply_eq_iff_eq]
      ext x; rw [Equiv.apply_symm_apply]
      split <;> grind
  . simp [Function.RightInverse, Function.LeftInverse]

theorem SetTheory.Set.pow_mul_pow_eq_pow_add (a b c:ℕ): (a^b) * a^c = a^(b+c) := by
  have singleton_has_card (x : Object) : ({x} : Set).has_card 1 := by
    use fun x ↦ Fin_mk 1 0 (by decide)
    rw [Function.bijective_iff_has_inverse]
    use fun n ↦ ⟨x, by simp⟩
    simp only [Function.LeftInverse, Function.RightInverse, Fin.coe_inj, Fin.toNat_mk]
    constructor
    . simp
    . intro n; have hn := Fin.toNat_lt n; grind
  have singleton_finite (x : Object) : ({x} : Set).finite := ⟨1, singleton_has_card x⟩
  have singleton_card (x : Object) : ({x} : Set).card = 1 := has_card_to_card (singleton_has_card x)

  let A := Fin a
  have Af : A.finite := Fin_finite a
  have Ac : A.card = a := Fin_card a

  let B := Fin b ×ˢ ({0} : Set)
  have hB : B.finite ∧ B.card = _ := card_prod (Fin_finite b) (singleton_finite _)
  simp only [Fin_card, singleton_card, mul_one] at hB
  obtain ⟨Bf, Bc⟩ := hB

  let C := Fin c ×ˢ ({1} : Set)
  have hC : C.finite ∧ C.card = _ := card_prod (Fin_finite c) (singleton_finite _)
  simp only [Fin_card, singleton_card, mul_one] at hC
  obtain ⟨Cf, Cc⟩ := hC

  have : Disjoint B C := by
    rw [disjoint_iff]; ext x
    simp only [B, C, mem_inter, mem_cartesian, not_mem_empty, iff_false, not_and, not_exists]
    rintro ⟨b', zero, rfl⟩ c' one h
    have hzero := zero.prop; rw [mem_singleton] at hzero
    have hone := one.prop; rw [mem_singleton] at hone
    simp [hzero, hone] at h

  have ⟨ABf, ABc⟩ := card_pow Af Bf
  have ⟨ACf, ACc⟩ := card_pow Af Cf
  have ⟨ABCf, ABCc⟩ := card_prod ABf ACf
  have BCf := card_union Bf Cf |>.left
  have BCc' := card_union_disjoint Bf Cf this
  have ⟨ABCf', ABCc'⟩ := card_pow Af BCf
  rw [←Ac, ←Bc, ←Cc, ←ABc, ←ACc, ←ABCc, ←BCc', ←ABCc']
  apply EquivCard_to_card_eq
  exact pow_prod_pow_EqualCard_pow_union A B C this

/-- Exercise 3.6.7 -/
theorem SetTheory.Set.injection_iff_card_le {A B:Set} (hA: A.finite) (hB: B.finite) :
    (∃ f:A → B, Function.Injective f) ↔ A.card ≤ B.card := by
  constructor
  . intro ⟨f, hf⟩
    rw [←card_image_inj hA hf]
    exact card_subset hB (image_in_codomain f A) |>.right
  . intro hABc
    have ⟨f, hf⟩ := has_card_card hA
    have ⟨g, hg⟩ := has_card_card hB
    have hAB : Fin A.card ⊆ Fin B.card := by
      intro n hn; let n' : Fin A.card := ⟨n, hn⟩
      rw [mem_Fin]; use n'; rw [Fin.coe_toNat]
      have := Fin.toNat_lt n'; grind
    use fun a ↦
      let ⟨n, hn⟩ := f a
      g.surjInv hg.surjective ⟨n, hAB n hn⟩
    intro a a' haa'
    simpa [(Function.injective_surjInv _).eq_iff, Subtype.val_inj, hf.injective.eq_iff] using haa'

/-- Exercise 3.6.8 -/
theorem SetTheory.Set.surjection_from_injection {A B:Set} (hA: A ≠ ∅) (f: A → B)
  (hf: Function.Injective f) : ∃ g:B → A, Function.Surjective g := by
  open Classical in
  use fun b ↦ if h : ∃ a, f a = b then h.choose else Classical.indefiniteDescription _ (nonempty_def hA)
  rw [Function.surjective_iff_hasRightInverse]; use f
  intro a; simp [hf.eq_iff]

/-- Exercise 3.6.9 -/
theorem SetTheory.Set.card_union_add_card_inter {A B:Set} (hA: A.finite) (hB: B.finite) :
    A.card + B.card = (A ∪ B).card + (A ∩ B).card := by
  induction' h : (A ∩ B).card with c ih generalizing B
  . have hAiB := card_subset hA (inter_subset_left A B) |>.left
    apply empty_of_card_eq_zero hAiB at h; rw [←disjoint_iff] at h
    simp [card_union_disjoint hA hB h]
  . have hAiB: (A ∩ B) ≠ ∅ := by intro h'; apply card_eq_zero_of_empty at h'; rw [h'] at h; contradiction
    have ⟨x, hx⟩ := nonempty_def hAiB
    have ⟨hxA, hxB⟩ := mem_inter x _ _ |>.mp hx
    have hBc : B.card ≠ 0 := by intro h'; apply empty_of_card_eq_zero hB at h'; have := not_mem_empty x; grind
    rw [←Nat.sub_one_add_one hBc, ←Nat.add_assoc, ←Nat.add_assoc, Nat.add_one_inj]
    have := card_erase (by grind : B.card > 0) (has_card_card hB) ⟨x, hxB⟩
    set B' := B \ {x}
    have hAiB' : (A ∩ B').card = c := by
      have hAiB' : A ∩ B' = (A ∩ B) \ {x} := by ext x'; simp [B', and_assoc]
      have := card_erase (by simp) (card_to_has_card (by simp) h) ⟨x, by simp [hxA, hxB]⟩
      apply has_card_to_card at this; simpa [hAiB']
    have hAuB' : A ∪ B' = A ∪ B := by ext x'; simp only [B', mem_union, mem_sdiff, mem_singleton]; grind
    specialize ih ⟨_, this⟩ hAiB'
    rwa [←has_card_to_card this, ←hAuB']

/-- Exercise 3.6.10 -/
lemma SetTheory.Set.iUnion_Fin_zero (A : Fin 0 → Set) : iUnion _ A = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  simp [mem_iUnion]

lemma SetTheory.Set.iUnion_Fin_union (A : Fin (n + 1) → Set) : iUnion _ A =
    iUnion (Fin n) (fun m ↦ A ⟨m, by rw [mem_Fin]; use m; have := Fin.toNat_lt m; rw [Fin.coe_toNat]; grind⟩)
    ∪ A ⟨n, by rw [mem_Fin]; grind⟩ := by
  ext x; simp only [mem_union, mem_iUnion]
  constructor
  . intro ⟨i, hx⟩
    by_cases hi: i < n;
    . left; use ⟨i, by rw [mem_Fin]; use i; simp [hi]⟩
    . right
      replace hi : i = ⟨n, by rw [mem_Fin]; grind⟩ := by
        have := Fin.toNat_lt i; rw [Fin.coe_inj, Fin.toNat_mk] <;> grind
      simpa [←hi]
  . grind

lemma SetTheory.Set.iUnion_Fin_finite (A : Fin n → Set) (hA : ∀ i, (A i).finite) : (iUnion _ A).finite := by
  induction' n with n ih
  . rw [iUnion_Fin_zero]; exact empty_finite
  . rw [iUnion_Fin_union]; set A' : Fin n → Set := fun m ↦ _
    specialize ih A' (by intro i; simp [A']; apply hA)
    exact card_union ih (hA _) |>.left

theorem SetTheory.Set.pigeonhole_principle {n:ℕ} {A: Fin n → Set}
  (hA: ∀ i, (A i).finite) (hAcard: (iUnion _ A).card > n) : ∃ i, (A i).card ≥ 2 := by
  induction' n with n ih
  . rw [iUnion_Fin_zero A, empty_card_eq_zero] at hAcard; contradiction
  . let n' := Fin_mk (n + 1) n (by simp)
    by_cases h : 2 ≤ (A n').card
    . grind
    . simp only [not_le] at h
      have hAA' := iUnion_Fin_union A; set A' : Fin n → Set := fun m ↦ _
      have hA'f := iUnion_Fin_finite A' (by intro i; unfold A'; apply hA)
      have hA' : (iUnion _ A').card > n := by
        rw [hAA'] at hAcard
        have ⟨_, hU⟩ := card_union hA'f (hA n')
        grind
      specialize ih (by intro i; dsimp [A']; apply hA) hA'
      grind

/-- Exercise 3.6.11 -/
theorem SetTheory.Set.two_to_two_iff {X Y:Set} (f: X → Y): Function.Injective f ↔
    ∀ S ⊆ X, S.card = 2 → (image f S).card = 2 := by
  constructor
  . intro hf S hSX hS
    have hSf : S.finite := ⟨2, card_to_has_card (by simp) hS⟩
    let f' (x : S) : Y := f ⟨x, by specialize hSX x x.prop; grind⟩
    have hf' : Function.Injective f' := by intro x x' hxx'; specialize hf hxx'; grind
    have hf'S := card_image_inj hSf hf'
    have : image f' S = image f S := by ext x; simp; grind
    grind
  . intro hS x x' hxx'
    let S : Set := {↑x, ↑x'}
    let Y' : Set := {↑(f x)}
    have hY' : image f S = Y' := by ext z; simp [S, Y']; grind
    have hY'c : Y'.card = 1 := by
      have := card_insert empty_finite (not_mem_empty (f x)) |>.right; simpa
    by_contra h
    have hSc : S.card = 2 := by
      have h:= card_insert empty_finite (not_mem_empty x)
      simp only [empty_union, empty_card_eq_zero, zero_add] at h
      have := card_insert h.left (by rw [mem_singleton]; grind : ↑x' ∉ ({↑x} : Set)) |>.right
      simpa [h.right, ←pair_eq] using this
    specialize hS S (by intro s; simp_rw [S, mem_pair]; grind) hSc
    grind

/-- Exercise 3.6.12 -/
def SetTheory.Set.Permutations (n: ℕ): Set := (Fin n ^ Fin n).specify (fun F ↦
    Function.Bijective (pow_fun_equiv F))

/-- Exercise 3.6.12 (i), first part -/
theorem SetTheory.Set.Permutations_finite (n: ℕ): (Permutations n).finite := by
  have := card_pow (Fin_finite n) (Fin_finite n) |>.left
  exact card_subset this (specify_subset _) |>.left

/- To continue Exercise 3.6.12 (i), we'll first develop some theory about `Permutations` and `Fin`. -/

noncomputable def SetTheory.Set.Permutations_toFun {n: ℕ} (p: Permutations n) : (Fin n) → (Fin n) := by
  have := p.property
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  exact this.choose.choose

theorem SetTheory.Set.Permutations_bijective {n: ℕ} (p: Permutations n) :
    Function.Bijective (Permutations_toFun p) := by
  have := p.prop
  simp only [Permutations, specification_axiom'', powerset_axiom] at this
  obtain ⟨⟨p', hp'⟩, hp'b⟩ := this
  simpa [Permutations_toFun, hp', pow_fun_equiv] using hp'b

theorem SetTheory.Set.Permutations_inj {n: ℕ} (p1 p2: Permutations n) :
    Permutations_toFun p1 = Permutations_toFun p2 ↔ p1 = p2 := by
  have hp1 := p1.prop; have hp2 := p2.prop
  simp only [Permutations, specification_axiom'', powerset_axiom] at hp1 hp2
  obtain ⟨⟨p1', hp1'⟩, hp1'b⟩ := hp1
  obtain ⟨⟨p2', hp2'⟩, hp2'b⟩ := hp2
  simp [Permutations_toFun, ←hp1', ←hp2', Subtype.ext_iff]

/-- This connects our concept of a permutation with Mathlib's `Equiv` between `Fin n` and `Fin n`. -/
noncomputable def SetTheory.Set.perm_equiv_equiv {n : ℕ} : Permutations n ≃ (Fin n ≃ Fin n) := {
  toFun := fun p => Equiv.ofBijective (Permutations_toFun p) (Permutations_bijective p)
  invFun := fun p => ⟨p, by simp [Permutations, pow_fun_equiv, Equiv.bijective]⟩
  left_inv := by intro; simp [Permutations_toFun, Equiv.ofBijective, ←Permutations_inj]
  right_inv := by intro; simp [Permutations_toFun, Equiv.ofBijective, ←Equiv.coe_inj]
}

/- Exercise 3.6.12 involves a lot of moving between `Fin n` and `Fin (n + 1)` so let's add some conveniences. -/

/-- Any `Fin n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.castSucc`. -/
def SetTheory.Set.Fin.castSucc {n} (x : Fin n) : Fin (n + 1) :=
  Fin_embed _ _ (by omega) x

@[simp]
lemma SetTheory.Set.Fin.castSucc_inj {n} {x y : Fin n} : castSucc x = castSucc y ↔ x = y := by simp [castSucc, Subtype.val_inj]

@[simp]
theorem SetTheory.Set.Fin.castSucc_ne {n} (x : Fin n) : castSucc x ≠ n := by
  intro h
  simp only [castSucc, coe_eq_iff'] at h
  have := Fin.toNat_lt x
  grind

/-- Any `Fin (n + 1)` except `n` can be cast to `Fin n`. Compare to Mathlib `Fin.castPred`. -/
noncomputable def SetTheory.Set.Fin.castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) : Fin n :=
  Fin_mk _ (x : ℕ) (by have := Fin.toNat_lt x; omega)

@[simp]
theorem SetTheory.Set.Fin.castSucc_castPred {n} (x : Fin (n + 1)) (h : (x : ℕ) ≠ n) :
    castSucc (castPred x h) = x := by simp [castSucc, castPred]

@[simp]
theorem SetTheory.Set.Fin.castPred_castSucc {n} (x : Fin n) (h : ((castSucc x : Fin (n + 1)) : ℕ) ≠ n) :
    castPred (castSucc x) h = x := by simp [castPred, castSucc]

/-- Any natural `n` can be cast to `Fin (n + 1)`. Compare to Mathlib `Fin.last`. -/
def SetTheory.Set.Fin.last (n : ℕ) : Fin (n + 1) := Fin_mk _ n (by omega)

/-- Now is a good time to prove this result, which will be useful for completing Exercise 3.6.12 (i). -/
theorem SetTheory.Set.card_iUnion_card_disjoint {n m: ℕ} {S : Fin n → Set}
    (hSc : ∀ i, (S i).has_card m)
    (hSd : Pairwise fun i j => Disjoint (S i) (S j)) :
    ((Fin n).iUnion S).finite ∧ ((Fin n).iUnion S).card = n * m := by
  induction' n with n ih
  . simp [iUnion_Fin_zero]
  . rw [iUnion_Fin_union, card_union_disjoint] <;>
    set S' : Fin n → Set := fun m ↦ S ⟨m, (Fin.castSucc m).prop⟩
    . specialize @ih S'
        (by intro i; specialize hSc ⟨i, (Fin.castSucc i).prop⟩; simpa [S'])
        (by
          intro i j hij
          specialize hSd (by intro h; rw [Fin.castSucc_inj] at h; contradiction)
          simpa [S'])
      specialize hSc (Fin.last n); rw [Fin.last, Fin_mk] at hSc
      rw [has_card_to_card hSc, add_one_mul, add_right_cancel_iff]
      constructor
      . exact card_union ih.left ⟨m, hSc⟩ |>.left
      . exact ih.right
    . apply iUnion_Fin_finite; intro i; exact ⟨m, hSc (Fin.castSucc i)⟩
    . exact ⟨m, hSc (Fin.last n)⟩
    . rw [disjoint_iff]; ext x
      simp_rw [mem_inter, mem_iUnion, not_mem_empty, iff_false, S']
      intro ⟨⟨i, hi⟩, hh⟩; specialize hSd (by simp : Fin.castSucc i ≠ Fin.last n)
      simp_rw [disjoint_iff, Fin.castSucc, Fin_embed, Fin.last, Fin_mk,
          Set.ext_iff, mem_inter, not_mem_empty, iff_false] at hSd
      grind

/- Finally, we'll set up a way to shrink `Fin (n + 1)` into `Fin n` (or expand the latter) by making a hole. -/

/--
  If some `x : Fin (n+1)` is never equal to `i`, we can shrink it into `Fin n` by shifting all `x > i` down by one.
  Compare to Mathlib `Fin.predAbove`.
-/
noncomputable def SetTheory.Set.Fin.predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) : Fin n :=
  if hx : (x:ℕ) < i then
    Fin_mk _ (x:ℕ) (by have := Fin.toNat_lt i; grind)
  else
    Fin_mk _ ((x:ℕ) - 1) (by
      have := Nat.le_of_lt_add_one (Fin.toNat_lt x)
      have := Nat.lt_of_le_of_ne (not_lt.mp hx) (by simpa using h.symm)
      grind)

/--
  We can expand `x : Fin n` into `Fin (n + 1)` by shifting all `x ≥ i` up by one.
  The output is never `i`, so it forms an inverse to the shrinking done by `predAbove`.
  Compare to Mathlib `Fin.succAbove`.
-/
noncomputable def SetTheory.Set.Fin.succAbove {n} (i : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if (x:ℕ) < i then
    Fin_embed _ _ (by simp) x
  else
    Fin_mk _ ((x:ℕ) + 1) (by simpa using Fin.toNat_lt x)

@[simp]
theorem SetTheory.Set.Fin.succAbove_ne {n} (i : Fin (n + 1)) (x : Fin n) : succAbove i x ≠ i := by
  intro h; simp only [succAbove, Fin_embed, Fin_mk] at h
  split_ifs at h with h'
  . rw [coe_inj, coe_eq_iff'] at h; grind
  . rw [coe_inj, toNat_mk] at h
    . grind
    . simpa using toNat_lt x

@[simp]
theorem SetTheory.Set.Fin.succAbove_predAbove {n} (i : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ i) :
    (succAbove i) (predAbove i x h) = x := by
  simp only [succAbove, predAbove, Fin_embed, Fin_mk, coe_toNat]
  split_ifs with h₁ _ h₂ <;> simp_all <;>
  replace h₁ := lt_of_le_of_ne (not_lt.mp h₁) (by simp only [ne_eq, coe_inj] at h; grind)
  . have := Nat.lt_of_lt_of_le h₂ (Nat.le_sub_one_of_lt h₁) |> ne_of_lt
    simp [←coe_eq_iff] at this
  . simp_rw [←coe_eq_iff, coe_toNat]; symm; rw [coe_eq_iff, toNat_mk]
    . grind
    . have := toNat_lt x; grind

@[simp]
theorem SetTheory.Set.Fin.predAbove_succAbove {n} (i : Fin (n + 1)) (x : Fin n) :
    (predAbove i) (succAbove i x) (succAbove_ne i x) = x := by
  simp only [predAbove, succAbove, coe_inj, Fin_embed]
  split_ifs with h₁ h₂ h₃ <;> simp_all
  . rw [coe_eq_iff', not_lt] at h₂; grind
  . rw [coe_eq_iff', not_lt] at h₁; rw [toNat_mk] at h₃; grind

/-- Exercise 3.6.12 (i), second part -/
theorem SetTheory.Set.Permutations_ih (n: ℕ):
    (Permutations (n + 1)).card = (n + 1) * (Permutations n).card := by
  let S i := (Permutations (n + 1)).specify (fun p ↦ perm_equiv_equiv p (Fin.last n) = i)

  have hSe : ∀ i, S i ≈ Permutations n := by
    intro i
    -- Hint: you might find `perm_equiv_equiv`, `Fin.succAbove`, and `Fin.predAbove` useful.
    have equiv : S i ≃ Permutations n := ⟨
      fun p ↦
        let p' := perm_equiv_equiv ⟨p, specify_subset _ p.val p.prop⟩
        let f (j : Fin n) : Fin n :=
          let k := p' (Fin.castSucc j)
          Fin.predAbove i k (by
            have := p.prop; simp_rw [S, specification_axiom''] at this
            have ⟨hp, hp'⟩ := this
            intro h; simp [k, p', ←hp'] at h)
        have hf : f.Bijective := by
          rw [Function.bijective_iff_has_inverse]
          use fun j ↦ Fin.castPred (p'.symm (Fin.succAbove i j)) (by
            have := p.prop; simp_rw [S, specification_axiom'', Fin.last, Fin_mk] at this
            have ⟨hp, hp'⟩ := this
            intro h; rw [←Fin.coe_eq_iff, Subtype.coe_eq_iff] at h
            have ⟨hn, h⟩ := h; simp [p'.symm_apply_eq, p', hp'] at h)
          simp [Function.LeftInverse, Function.RightInverse, p', f]
        perm_equiv_equiv.symm (Equiv.ofBijective f hf),
      fun p ↦
        let p' := perm_equiv_equiv p
        open Classical in
        let f (j : Fin (n + 1)) : Fin (n + 1) :=
          if h : j = Fin.last n then
            i
          else
            let k := p' (Fin.castPred j (by simpa [Fin.last, Fin_mk] using h))
            Fin.succAbove i k
        ⟨f, by
          simp [S, Permutations, pow_fun_equiv]
          simp [perm_equiv_equiv, Permutations_toFun]
          constructor
          . rw [Function.bijective_iff_has_inverse]
            open Classical in
            use fun j ↦ if h : j = i then
              Fin.last n
            else
              Fin.castSucc (p'.symm (Fin.predAbove i j (by grind)))
            constructor
            . intro j; dsimp [f]; split_ifs <;> simp_all; grind
            . intro j; dsimp [f]; split_ifs <;> simp_all; grind
          . grind⟩,
      fun p ↦ by
        have := p.prop
        simp only [Permutations, specification_axiom'', powerset_axiom, S] at this
        have ⟨⟨⟨f, hf⟩, hf'⟩, hp⟩ := this
        simp [Subtype.ext_iff, ←hf, ←hp, perm_equiv_equiv, Equiv.ofBijective, Permutations_toFun]
        grind,
      fun p ↦ by
        have := p.prop
        simp only [Permutations, specification_axiom'', powerset_axiom] at this
        have ⟨⟨f, hf⟩, hp⟩ := this
        simp [Subtype.ext_iff, ←hf, perm_equiv_equiv, Equiv.ofBijective, Permutations_toFun]
        ext x; simp
    ⟩
    use equiv, equiv.injective, equiv.surjective

  -- Hint: you might find `card_iUnion_card_disjoint` and `Permutations_finite` useful.
  have hP : Permutations (n + 1) = iUnion _ S := by
    ext p; simp only [mem_iUnion, S, specification_axiom'']; grind
  rw [hP]
  refine' card_iUnion_card_disjoint _ _ |>.right
  . intro i
    rw [EquivCard_to_has_card_eq (hSe i)]
    exact has_card_card (Permutations_finite n)
  . intro i j hij; rw [disjoint_iff]
    ext x; simp only [mem_inter, not_mem_empty, iff_false, S, specification_axiom'']
    grind


/-- Exercise 3.6.12 (ii) -/
theorem SetTheory.Set.Permutations_card (n: ℕ):
    (Permutations n).card = n.factorial := by
  induction' n with n ih
  . apply has_card_to_card
    use fun _ ↦ Fin_mk 1 0 (by decide)
    rw [Function.bijective_iff_has_inverse]
    let perm0 (i : Fin 0) : Fin 0 := by have := Fin.toNat_lt i; grind
    use fun _ ↦ ⟨perm0, by
      simp [perm0, Permutations, pow_fun_equiv]
      rw [Function.bijective_iff_has_inverse]
      use perm0; grind⟩
    simp only [Function.LeftInverse, Function.RightInverse, Permutations, perm0]
    constructor
    . intro ⟨p, hp⟩; simp_rw [specification_axiom'', powerset_axiom] at hp
      obtain ⟨⟨f, hf⟩, hf'⟩ := hp
      simp_rw [←hf, Subtype.ext_iff, coe_of_fun_inj]
      grind
    . intro i; have := Fin.toNat_lt i
      simp_rw [Nat.factorial_zero, Nat.lt_one_iff] at this
      simpa using this.symm
  . simp [Permutations_ih, ih, Nat.factorial_succ]

/-- Connections with Mathlib's `Finite` -/
theorem SetTheory.Set.finite_iff_finite {X:Set} : X.finite ↔ Finite X := by
  rw [finite_iff_exists_equiv_fin, finite]
  constructor
  · rintro ⟨n, hn⟩
    use n
    obtain ⟨f, hf⟩ := hn
    have eq := (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin n)
    exact ⟨eq⟩
  rintro ⟨n, hn⟩
  use n
  have eq := hn.some.trans (Fin.Fin_equiv_Fin n).symm
  exact ⟨eq, eq.bijective⟩

/-- Connections with Mathlib's `Set.Finite` -/
theorem SetTheory.Set.finite_iff_set_finite {X:Set} :
    X.finite ↔ (X :_root_.Set Object).Finite := by
  rw [finite_iff_finite]
  rfl

/-- Connections with Mathlib's `Nat.card` -/
theorem SetTheory.Set.card_eq_nat_card {X:Set} : X.card = Nat.card X := by
  by_cases hf : X.finite
  · by_cases hz : X.card = 0
    · rw [hz]; symm
      have : X = ∅ := empty_of_card_eq_zero hf hz
      rw [this, Nat.card_eq_zero, isEmpty_iff]
      aesop
    symm
    have hc := has_card_card hf
    obtain ⟨f, hf⟩ := hc
    apply Nat.card_eq_of_equiv_fin
    exact (Equiv.ofBijective f hf).trans (Fin.Fin_equiv_Fin X.card)
  simp only [card, hf, ↓reduceDIte]; symm
  rw [Nat.card_eq_zero, ←not_finite_iff_infinite]
  right
  rwa [finite_iff_set_finite] at hf

/-- Connections with Mathlib's `Set.ncard` -/
theorem SetTheory.Set.card_eq_ncard {X:Set} : X.card = (X: _root_.Set Object).ncard := by
  rw [card_eq_nat_card]
  rfl

end Chapter3
