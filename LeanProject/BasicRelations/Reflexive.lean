import Mathlib
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity

#check Reflexive
#check Symmetric
#check Transitive

namespace ProvingReflexive

-- Define relation R
def R (a b : ℤ) : Prop := Even (a + b)

theorem R_Reflexive : ∀ a : ℤ, R a a := by
  intro a
  unfold R
  ring_nf -- rewrite a + a to a * 2
  rw[mul_comm]
  apply even_two_mul

end ProvingReflexive


namespace DisprovingReflexive

def R (m a b: ℤ) : Prop := a = m * b

-- Different examples, different approaches
example : ¬ (2 * 2 = 2 * 4) := by
  intro h
  rw [mul_comm] at h
  have h_false : 4 = 8 := h -- Explicitly compute the values
  contradiction

example (a : ℤ) : a ≠ 0 → ¬ (a * 2 = a * 4) := by
  intro h_nonzero h_eq
  have h_cancel : (2 : ℤ) = (4 : ℤ) := Int.eq_of_mul_eq_mul_left h_nonzero h_eq -- cancel 'a' from both sides
  exact (by decide : (2 : ℤ) ≠ (4 : ℤ)) h_cancel

example (a : ℤ) : a ≠ 0 → ¬ (a = 2 * a) := by
  intro h_nonzero h_eq
  nth_rewrite 1 [← one_mul a] at h_eq
  rw [mul_comm, mul_comm 2] at h_eq
  have h_contradiction : (1 : ℤ) = 2 := Int.eq_of_mul_eq_mul_left h_nonzero h_eq -- cancel 'a' from both sides
  exact (by decide : (1 : ℤ) ≠ (2 : ℤ)) h_contradiction

-- Prove R is not reflexive
theorem R_Not_Reflexive :  ∃ (m : ℤ) (a : ℤ), ¬ R m a a := by
  unfold R
  use 2,2 -- Choose m = 2 and a = 2
  intro h
  contradiction

-- Different way to prove R is not reflexive
example (a : ℤ) : ∃ (m : ℤ), a ≠ 0 → ¬ (R m a a) := by
  use 2
  intro h_nonzero h
  unfold R at h
  nth_rewrite 1 [← one_mul a] at h
  rw [mul_comm, mul_comm 2] at h
  have h_contra : (1 : ℤ) = 2 := Int.eq_of_mul_eq_mul_left h_nonzero h
  exact (by decide : (1 : ℤ) ≠ 2) h_contra

end DisprovingReflexive
