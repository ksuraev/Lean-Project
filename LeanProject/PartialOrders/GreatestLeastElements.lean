import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Fintype.Defs

namespace Greatest

-- Define greatest element 'x'
-- https://www.uv.es/coslloen/Lean4/Leancap11.html
def greatest {S : Type _} [PartialOrder S] (x : S) : Prop := ∀ {y : S}, y ≤ x

-- Show uniqueness of greatest element
theorem greatest_is_unique (α : Type _) [Fintype α] [PartialOrder α] [Nonempty α] [DecidableRel (fun (x y : α) => x ≤ y)] [DecidableEq α] : ∀ x z : α, greatest x ∧ greatest z → x = z := by
  intro x z hxz
  -- Assume greatest x and greatest z
  rcases hxz with ⟨hx, hz⟩
  -- Use antisymm prop to show x = z
  exact le_antisymm hz hx

end Greatest

namespace Least
-- Define least element 'x'
def least {S : Type _} [PartialOrder S] (x : S) : Prop := ∀ {y : S}, x ≤ y

-- Show uniqueness of least element
theorem least_is_unique (α : Type _) [Fintype α] [PartialOrder α] [Nonempty α] [DecidableRel (fun (x y : α) => x ≤ y)] [DecidableEq α] : ∀ x z : α, least x ∧ least z → x = z := by
  intro x z hxz
  rcases hxz with ⟨hx, hz⟩
  exact le_antisymm hx hz

end Least
