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
  rw[h_eq2] at h_eq1 -- substitute b in the first equation
  -- Now we have a = k * (l * c) and we know k * l is an integer
  rw[← mul_assoc] at h_eq1
  use k * l -- k * l is an integer

end ProvingTransitive

-- Disproving that a relation is transitive
namespace DisprovingTransitive

example : ¬ Odd (-2) := by
  intro h
  -- Expand the definition of Odd
  cases h with
  | intro k h_eq
  -- Rearrange the equation -2 = 2 * k + 1
  have h_contra : 2 * k = -3 := by
    linarith -- Subtract 1 from both sides
  -- Use modular arithmetic to show k cannot be an integer
  have h_mod : (-3) % 2 = 1 := by decide -- Compute the remainder of -3 divided by 2
  -- Contradiction: 2 * k is divisible by 2, so (-3) % 2 must be 0
  have h_mod2 : (2 * k) % 2 = 0 := by
    simp -- 2 * k is even, so its remainder when divided by 2 is 0
  rw [h_contra] at h_mod2
  contradiction

def R (a b : ℤ) : Prop := Odd (a - b)

example : ¬ Transitive R := by
  unfold Transitive R
  intro h_transitive -- assume R is transitive
  have h1 : R 1 2 := by
    unfold R Odd -- ∃k, 1 - 3 = 2 * k + 1
    use -1
    ring_nf -- simplifies 1 - 2 to -1
  have h2 : R 2 3 := by
    unfold R Odd
    use -1
    ring_nf
  have h3 : R 1 3 := h_transitive h1 h2
  unfold R Odd at h3
  cases h3 with -- extract the integer k
  | intro k h3_eq -- assume 1 - 3 = 2 * k + 1
  have h_lhs : 1 - 3 = -2 := by ring_nf
  have h_rearrange : 2 * k = -3 := by linarith
  have h_mod1 : (-2) % 2 = 0 := by decide -- take h_lhs and get the remainder when divided by 2
  have h_mod2 : (2 * k) % 2 = 0 := by simp -- 2 * k is even
  rw[h_rearrange] at h_mod2 -- sub in 2 * k = -3
  contradiction -- -3 % 2 = 0 is a contradiction

-- From Zulip chat
example : ¬Transitive R := by
  unfold Transitive R
  push_neg
  use 1, 2, 3, by norm_num, by norm_num, by norm_num

end DisprovingTransitive
