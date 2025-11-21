import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  set n := x.num / x.den with hn
  have hn₁ : n ≤ x := by
    rw_mod_cast [Rat.le_iff, mul_one]
    exact Int.ediv_mul_le _ (by simp)
  have hn₂ : x < n + 1 := by
    rw_mod_cast [Rat.lt_iff, ←Int.ediv_add_emod' x.num x.den, mul_one, add_one_mul]
    gcongr
    exact Int.natAbs_natCast x.den ▸ Int.emod_lt _ (by simp)
  use! n, hn₁, hn₂
  intro n' ⟨hn₁', hn₂'⟩
  have hnn' := lt_of_le_of_lt hn₁ hn₂'
  have hn'n := lt_of_le_of_lt hn₁' hn₂
  rw_mod_cast [Int.lt_add_one_iff] at hn'n hnn'
  exact le_antisymm hnn' hn'n |>.symm

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  have ⟨n, ⟨hn₁, hn₂⟩, hn₃⟩ := x.between_int
  use n.toNat + 1
  rw [cast_add, cast_one, gt_iff_lt]
  apply lt_of_lt_of_le hn₂
  rw [add_le_add_iff_right]
  exact_mod_cast Int.self_le_toNat n

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  simp_rw [not_exists, not_forall, not_lt]
  intro a
  induction' ha₀ : a 0 using Nat.strongRec with a₀ ih generalizing a
  by_cases ha₁ : a 0 ≤ a 1
  . use 0
  . rw [not_le, ha₀] at ha₁
    obtain ⟨n, hn⟩ := ih (a 1) ha₁ (fun n ↦ a (n + 1)) rfl
    use n + 1

def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use fun n ↦ -n
  intro n
  simp

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  have hn := Nat.div_add_mod n 2 |>.symm
  by_cases h : n % 2 = 0
  . left; use n / 2
    simpa [h, two_mul] using hn
  . right; use n / 2
    rw [mod_two_not_eq_zero] at h
    simpa [h, two_mul] using hn

set_option trace.grind.ematch.instance true in
theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  intro ⟨⟨m, hm⟩, ⟨k, hk⟩⟩
  rw [hm, ←two_mul] at hk
  have := Nat.eq_div_of_mul_eq_right (by decide) hk
  simp [this, Nat.mul_add_div] at hk

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply this _ _ _ (show -x>0 by simp; order) <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . rw [←Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0), this, mul_pow,
            show 2 ^ 2 = 2 * 2 by decide, mul_assoc, mul_lt_mul_left (by decide)]
        refine' lt_mul_left _ (by decide)
        have h : q ^ 2 ≠ 0 := Nat.pow_pos hpos |> Nat.ne_zero_of_lt
        rw [this, mul_ne_zero_iff] at h
        exact Nat.zero_lt_of_ne_zero h.right
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      obtain ⟨k, hp⟩ := hp
      use 2 * k ^ 2 + 2 * k
      grind
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
