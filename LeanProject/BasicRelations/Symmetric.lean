import Mathlib
import Mathlib.Algebra.Ring.Parity

-- Proving that a relation is symmetric
namespace ProvingSymmetric

def R (a b : ℤ) : Prop := a + b = 0

example : Symmetric R := by
  unfold R
  intro a b h
  -- Given a + b = 0, we need to show b + a = 0
  rw [add_comm] at h
  exact h

end ProvingSymmetric

-- Disproving that a relation is symmetric
namespace DisprovingSymmetric

def R (a b : ℤ) : Prop := ∃ m : ℤ, a = m * b

example : ¬ R 7 3 := by
  intro h
  cases h with
  | intro m h_eq
  have h_mod : 7 % 3 = 1 := by decide
  have h_mod2 : (m * 3) % 3 = 0 := by simp
  symm at h_eq
  rw [h_eq] at h_mod2
  contradiction

-- Three examples doing the same proof in different ways
example : ¬ Symmetric R := by
  unfold Symmetric
  intro h_symmetric
  have h1 : R 2 1:= by
    unfold R
    use 2
    rfl
  have h2 : R 1 2 := h_symmetric h1
  unfold R at h2
  cases h2 with
  | intro m h_eq
  have h_mod : 1 % 2 = 1 := by decide -- 1 is not divisible by 2
  have h_mod2 : (m * 2) % 2 = 0 := by simp -- any multiple of 2 is divisible by 2
  symm at h_eq -- make m * 2 the first term
  rw [h_eq] at h_mod2
  contradiction -- 1 % 2 = 1 and 1 % 2 = 0 contradict each other

example : ¬ Symmetric R := by
  unfold Symmetric R
  push_neg -- turns ¬∀ x y : ℤ, (∃ m, x = m * y) → ∃ m, y = m * x into ∃ x y, (∃ m, x = m * y) ∧ ∀ (l : ℤ), y ≠ l * x. In standard mode, it transforms ¬(p ∧ q) into p → ¬q
  use 0, 1 -- choose x = 0, y = 1
  constructor
  use 0 -- choose m = 0
  rfl -- show 0 = 0 * 1
  intro m h_eq
  -- We need to show that 1 ≠ m * 2
  rw[mul_zero] at h_eq
  contradiction

-- From Lean chat
example : ¬ Symmetric R := by
  intro h -- Turn Symmetric R into h assumption
  specialize @h 0 1 ⟨0, by norm_num⟩ -- specialise the assumption to 0 and 1 - the goal is 0 = 0 * 1 because R 0 1 is true
  obtain ⟨y, hy⟩ := h -- obtain the y value from the assumption R 1 0
  simp at hy

end DisprovingSymmetric
