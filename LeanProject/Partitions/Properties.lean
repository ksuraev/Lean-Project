import Mathlib
import Init.Prelude
import Init.Core
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Disjoint
import LeanProject.EquivalenceClasses.Properties


namespace Partitions

structure Partition (α : Type _) where
  subsets : Set (Set α) -- collection of subsets of α
  nonempty_subsets : ∀ s ∈ subsets, s.Nonempty
  disjoint_subsets : ∀ s₁ ∈ subsets, ∀ s₂ ∈ subsets, s₁ ≠ s₂ → Disjoint s₁ s₂
  union_eq_univ : Set.sUnion subsets = Set.univ

-- Using equivalence class properties from EqClasses_Setoid namespace
open EqClasses_Setoid

-- Set of all equivalence classes
def eq_classes {α : Type _} (R : Setoid α) : Set (Set α) :=
  { s | ∃ a, s = equiv_class R a }

lemma eq_classes_nonempty {α : Type _} (R : Setoid α) :
  ∀ s ∈ eq_classes R, s.Nonempty := by
  intro s hs
  rcases hs with ⟨a, rfl⟩
  use a
  exact EqClasses_Setoid.Property1 R a

lemma eq_classes_disjoint {α : Type _} (R : Setoid α) :
  ∀ s₁ ∈ eq_classes R, ∀ s₂ ∈ eq_classes R, s₁ ≠ s₂ → Disjoint s₁ s₂ := by
  intro s₁ hs₁ s₂ hs₂ hne
  by_contra h_nonempty
  rw [Set.not_disjoint_iff_nonempty_inter] at h_nonempty
  rcases h_nonempty with ⟨x, hx⟩
  rcases hs₁ with ⟨a, rfl⟩
  rcases hs₂ with ⟨b, rfl⟩
  have hxa : x ∈ [a]__R := hx.left
  have hxb : x ∈ [b]__R := hx.right
  have hab : a ∈ [b]__R := R.trans (R.symm hxa) hxb
  have h_eq_classes := (EqClasses_Setoid.Property2 R a b).mp hab
  rw [h_eq_classes] at hne
  exact hne rfl

lemma eq_classes_union_eq_univ {α : Type _} (R : Setoid α) :
  Set.sUnion (eq_classes R) = Set.univ := by
  ext x
  constructor
  · intro h
    trivial
  · intro h
    use equiv_class R x
    constructor
    · use x
    · simp [equiv_class]
      exact R.iseqv.1 x

theorem eq_classes_form_partition {α : Type _} (R : Setoid α) : ∃ P : Partition α, P.subsets = eq_classes R :=
  ⟨{ subsets := eq_classes R,

      nonempty_subsets := by
        exact eq_classes_nonempty R,

      disjoint_subsets := by
        exact eq_classes_disjoint R,

      union_eq_univ := by
        exact eq_classes_union_eq_univ R
    }, rfl⟩

end Partitions

-- Alternate definition of partitions
namespace PartitionsAlt

-- Define a collection P of subsets of a set S that partition S
def Partition {S : Type} (P : Set (Set S)) : Prop :=
  (∀ p ∈ P, p ≠ ∅) ∧
  (∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → p1 ∩ p2 = ∅) ∧
  (⋃₀ P = Set.univ)

-- Alternative definition using a structure
-- Lean summer lectures 2/18: partitions - XenaProject
@[ext] structure Partition' (X : Type) where
  (S : Set (Set X))
  (nonempty : S.Nonempty)
  (disjoint : ∀ p1 ∈ S, ∀ p2 ∈ S, p1 ≠ p2 → p1 ∩ p2 = ∅)
  (cover : ⋃₀ S = Set.univ)
end PartitionsAlt
