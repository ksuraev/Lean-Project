import Init.Prelude
import Init.Core
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Disjoint
import LeanProject.EquivalenceClasses.Properties

namespace Partitions

@[ext] structure Partition (α : Type _) where
  subsets : Set (Set α) -- collection of subsets of α
  nonempty_subsets : ∀ s ∈ subsets, s.Nonempty
  disjoint_subsets : ∀ s₁ ∈ subsets, ∀ s₂ ∈ subsets, s₁ ≠ s₂ → Disjoint s₁ s₂
  union_eq_univ : Set.sUnion subsets = Set.univ

-- Lemma to show that the intersection of two sets containing a common element is non-empty
lemma intersection_nonempty {α : Type _} (s₁ s₂ : Set α) (x : α) (h : x ∈ s₁ ∩ s₂) :
  (s₁ ∩ s₂).Nonempty := by
  use x

-- Lemma to show that if two subsets of a partition share an element, they must be equal
lemma subsets_equal {α : Type _} (P : Partition α)
    (s₁ s₂ : Set α) (hs₁ : s₁ ∈ P.subsets) (hs₂ : s₂ ∈ P.subsets) (x : α) (hx₁ : x ∈ s₁) (hx₂ : x ∈ s₂) : s₁ = s₂ := by
    have h_inter : (s₁ ∩ s₂).Nonempty := intersection_nonempty s₁ s₂ x ⟨hx₁, hx₂⟩
    rw[← Set.not_disjoint_iff_nonempty_inter] at h_inter
    by_contra h_neq
    have h_disjoint := P.disjoint_subsets s₁ hs₁ s₂ hs₂ h_neq
    exact h_inter h_disjoint


-- Using equivalence class properties from EqClasses_Setoid namespace
open EqClasses_Setoid

-- Set of all equivalence classes
def eq_classes {α : Type _} (R : Setoid α) : Set (Set α) :=
  { s | ∃ a, s = equiv_class R a }

-- Show that eq_classes form a partition
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
  have hxa : x ∈ [a]_R := hx.left
  have hxb : x ∈ [b]_R := hx.right
  have hab : a ∈ [b]_R := R.trans (R.symm hxa) hxb
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
      nonempty_subsets := eq_classes_nonempty R,
      disjoint_subsets := eq_classes_disjoint R,
      union_eq_univ := eq_classes_union_eq_univ R}, rfl⟩


-- Rewrite eq_classes_form_partition to use subtype
-- Explicitly construct the subtype
def eq_classes_form_partition_sub {α : Type _} (R : Setoid α) : { P : Partition α // P.subsets = eq_classes R } :=
    ⟨{ subsets := eq_classes R,
       nonempty_subsets := eq_classes_nonempty R,
       disjoint_subsets := eq_classes_disjoint R,
       union_eq_univ := eq_classes_union_eq_univ R },
     rfl⟩


-- Alternate to using subtypes
def def_eq_classes_form_partition {α : Type _} (R : α → α → Prop) (hR : Equivalence R) : Partition α :=
{ subsets := eq_classes ⟨R, hR⟩,
  nonempty_subsets := eq_classes_nonempty ⟨R, hR⟩,
  disjoint_subsets := eq_classes_disjoint ⟨R, hR⟩,
  union_eq_univ := eq_classes_union_eq_univ ⟨R, hR⟩ }
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
