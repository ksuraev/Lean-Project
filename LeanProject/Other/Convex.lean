import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
namespace Convex

variable {𝕂 α : Type*} [Semiring 𝕂] [PartialOrder 𝕂] [AddCommMonoid α] [SMul 𝕂 α]

theorem inter_is_convex (S L : Set α) (hS : Convex 𝕂 S) (hL : Convex 𝕂 L) : Convex 𝕂 (S ∩ L) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hxS, hxL⟩ := hx
  obtain ⟨hyS, hyL⟩ := hy
  constructor
  · exact hS hxS hyS ha hb hab
  · exact hL hxL hyL ha hb hab

variable {𝕂 α : Type*} [PartialOrder 𝕂] [Semiring 𝕂] [AddCommMonoid α] [Module 𝕂 α] [IsOrderedRing 𝕂]

-- Show that a set is convex if and only if its intersection with any line is convex
theorem convex_iff_convex_inter_with_lines (S : Set α) :
  Convex 𝕂 S ↔ ∀ (x y : α), Convex 𝕂 (S ∩ segment 𝕂 x y) := by
  constructor
  · intro hS x y
    apply Convex.inter
    exact hS
    apply convex_segment
  · intro h x hx y hy a b ha hb hab
    have h_inter := h x y
    have hx_in_inter : x ∈ S ∩ segment 𝕂 x y := by
      constructor
      · exact hx
      · exact left_mem_segment 𝕂 x y
    have hy_in_inter : y ∈ S ∩ segment 𝕂 x y := by
      constructor
      · exact hy
      · exact right_mem_segment 𝕂 x y
    have h_result := h x y hx_in_inter hy_in_inter ha hb hab
    exact h_result.1








end Convex
