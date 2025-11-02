import Mathlib
import Mathlib.Algebra.Ring.Parity

-- Proving that a relation is symmetric
namespace ProvingSymmetric

def R (a b : ℤ) : Prop := a + b = 0

example : Symmetric R := by
  unfold R
  intro a b h
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
  have h_mod : 1 % 2 = 1 := by decide
  have h_mod2 : (m * 2) % 2 = 0 := by simp
  symm at h_eq
  rw [h_eq] at h_mod2
  contradiction -- 1 % 2 = 1 and 1 % 2 = 0 contradict

example : ¬ Symmetric R := by
  unfold Symmetric R
  push_neg
  use 0, 1
  constructor
  use 0
  rfl
  intro m h_eq
  rw[mul_zero] at h_eq
  contradiction

example : ¬ Symmetric R := by
  intro h
  specialize @h 0 1 ⟨0, by norm_num⟩
  obtain ⟨y, hy⟩ := h
  simp at hy

end DisprovingSymmetric
