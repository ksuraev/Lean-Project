import Mathlib
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity

-- Proving that a relation is transitive
namespace ProvingTransitive

def R (a b : ℤ) : Prop := ∃ m : ℤ, a = m * b

example : Transitive R := by
  unfold Transitive R
  intro a b c h1 h2 -- assume R a b and R b c
  cases h1 with
  | intro k h_eq1 -- assume a = k * b
  cases h2 with
  | intro l h_eq2 -- assume b = l * c
  rw[h_eq2] at h_eq1
  rw[← mul_assoc] at h_eq1
  use k * l

-- Different way to write the same proof
example : Transitive R := by
  unfold Transitive R
  intro a b c h1 h2
  rcases h1 with ⟨k, h_eq1⟩
  rcases h2 with ⟨l, h_eq2⟩
  rw [h_eq2, ← mul_assoc] at h_eq1
  use k * l

-- Even more concise way to write the same proof
example : Transitive R := by
  intro a b c ⟨k, h_eq1⟩ ⟨l, h_eq2⟩
  use k * l
  rw [h_eq2, ← mul_assoc] at h_eq1
  exact h_eq1

end ProvingTransitive

-- Disproving that a relation is transitive
namespace DisprovingTransitive

example : ¬ Odd (-2) := by
  intro ⟨k, h_eq⟩
  have h_mod : (-2) % 2 = 1 := by
    rw [h_eq]
    simp
  simp at h_mod

-- Worse way to write the same proof
example : ¬ Odd (-2) := by
  intro h
  cases h with
  | intro k h_eq
  have h_contra : 2 * k = -3 := by
    linarith
  have h_mod : (-3) % 2 = 1 := by decide
  have h_mod2 : (2 * k) % 2 = 0 := by
    simp
  rw [h_contra] at h_mod2
  contradiction

-- Define relation R
def R (a b : ℤ) : Prop := Odd (a - b)

example : ¬Transitive R := by
  unfold Transitive R
  push_neg
  use 1, 2, 3, by norm_num, by norm_num, by norm_num

end DisprovingTransitive
