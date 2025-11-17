import Mathlib.Logic.Equiv.Defs
import Init.Notation
import Init.Core
import Init.Prelude
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Disjoint
import LeanProject.EquivalenceClasses.Properties
import LeanProject.Partitions.Properties

-- Following along with Lean summer lectures 2/18: partitions (Xena Project)
-- https://www.youtube.com/watch?v=FEKsZj3WkTY

-- @[ext] structure partition (X : Type) where
-- (C : Set (Set X))
-- (Hnonempty : ∀ c ∈ C, c ≠ ∅)
-- (Hcover : ∀ x, ∃ c ∈ C, x ∈ c)
-- (Hunique : ∀ c ∈ C, ∀ d ∈ C, c ∩ d ≠ ∅ → c = d)

-- def equiv_class {α : Type _} (R : Setoid α) (a : α) : Set α :=
--   { x | R.r x a }

-- lemma mem_class {X : Type} (R : X → X → Prop) (hR : Equivalence R) (x : X) : x ∈ equiv_class R x := by
--   exact hR.1 x

-- lemma subset_of_rel {X : Type} (R : X → X → Prop) (x y : X) (hxy : R x y) (hR : Equivalence R) : equiv_class R y ⊆ equiv_class R x := by
--   intro z hz
--   change R y z at hz
--   change R x z
--   exact hR.3 hxy hz

-- example (X : Type) : {R : X → X → Prop // Equivalence R} ≃ partition X :=
-- {
--   toFun := fun R => {
--     C := {S : Set X | ∃ x : X, S = equiv_class R x}
--     Hnonempty := by
--       rintro _ ⟨x, rfl⟩
--       rw [← Set.nonempty_iff_ne_empty]
--       use x
--       exact mem_class R.1 R.2 x
--     Hcover := by
--       intro x
--       use equiv_class R x
--       constructor
--       · use x
--       · exact mem_class R.1 R.2 x
--     Hunique := by
--       intros x hx y hy hxy
--       rcases hx with ⟨x, rfl⟩
--       rcases hy with ⟨y, rfl⟩
--       rw [← Set.nonempty_iff_ne_empty] at hxy
--       rcases hxy with ⟨z, hxz, hyz⟩
--       change R.1 x z at hxz
--       change R.1 y z at hyz
--       apply Set.Subset.antisymm
--       apply subset_of_rel R.1 y x
--       rcases R.2 with ⟨ref, symm, trans⟩
--       apply trans hyz (symm hxz)
--       exact R.2
--       apply subset_of_rel R.1 x y
--       rcases R.2 with ⟨ref, symm, trans⟩
--       exact trans hxz (symm hyz)
--       exact R.2
--   }
--   invFun := fun P => ⟨fun x y => ∃ c ∈ P.C, x ∈ c ∧ y ∈ c,
--     {
--       -- reflexive
--       refl := by
--         intro x
--         rcases P.Hcover x with ⟨c, hc, hxc⟩
--         use c
--       -- symmetric
--       symm := by
--         intro x y hxy
--         rcases hxy with ⟨c, hc, hxc, hyc⟩
--         use c
--       trans := by
--         intro x y z
--         rintro ⟨B, hB, hBx, hBy⟩ ⟨C, hC, hCy, hCz⟩
--         use B, hB, hBx
--         convert hCz
--         apply P.Hunique B hB C hC
--         rw [← Set.nonempty_iff_ne_empty]
--         use y
--         exact ⟨hBy, hCy⟩
--     }
--   ⟩
--   left_inv := by
--     intro R
--     dsimp
--     ext x y
--     sorry,
--   right_inv := by
--     intro P
--     ext c
--     dsimp
--     constructor
--     · intro h
--       rcases h with ⟨x, rfl⟩


-- }

structure partition (X : Type*) where
(C : Set (Set X))
(disjoint : ∀ A ∈ C, ∀ B ∈ C, A ≠ B → A ∩ B = ∅)
(cover : ∀ x : X, ∃ A ∈ C, x ∈ A)
(nonempty : ∀ A ∈ C, A ≠ ∅)


open EqClasses_Setoid

variable {X : Type*}

def F (R : Setoid X) : partition X :=
{
  C := {S : Set X | ∃ x : X, S = equiv_class R x},
  nonempty := by
    rintro _ ⟨x, rfl⟩
    rw [← Set.nonempty_iff_ne_empty]
    use x
    exact R.iseqv.1 x
  disjoint := by
    intro s₁ hs₁ s₂ hs₂ hne
    by_contra h_nonempty
    change s₁ ∩ s₂ ≠ ∅ at h_nonempty
    rw [← Set.nonempty_iff_ne_empty] at h_nonempty
    rw [← Set.not_disjoint_iff_nonempty_inter] at h_nonempty
    rcases hs₁ with ⟨a, rfl⟩
    rcases hs₂ with ⟨b, rfl⟩
    rw[Set.not_disjoint_iff] at h_nonempty
    rcases h_nonempty with ⟨x, hx⟩
    have hxa : x ∈ [a]_R := hx.left
    have hxb : x ∈ [b]_R := hx.right
    have hab : R.r a b := R.iseqv.3 (R.iseqv.2 hxa) hxb
    have h_eq_classes := (EqClasses_Setoid.Property2 R a b).mp hab
    rw [h_eq_classes] at hne
    exact hne rfl
  cover := by
    intro x
    use equiv_class R x
    constructor
    · use x
    · exact R.iseqv.1 x
}

-- Lemma to show that the intersection of two sets containing a common element is non-empty
lemma intersection_nonempty {α : Type _} (s₁ s₂ : Set α) (x : α) (h : x ∈ s₁ ∩ s₂) :
  (s₁ ∩ s₂).Nonempty := by
  use x


-- Lemma to show that if two subsets of a partition share an element, they must be equal
lemma subsets_equal {α : Type _} (P : partition α)
    (s₁ s₂ : Set α) (hs₁ : s₁ ∈ P.C) (hs₂ : s₂ ∈ P.C) (x : α) (hx₁ : x ∈ s₁) (hx₂ : x ∈ s₂) : s₁ = s₂ := by
    have h_inter : (s₁ ∩ s₂).Nonempty := intersection_nonempty s₁ s₂ x ⟨hx₁, hx₂⟩
    by_contra h_neq
    have h_disjoint := P.disjoint s₁ hs₁ s₂ hs₂ h_neq
    change (s₁ ∩ s₂).Empty at h_disjoint
    exact h_inter h_disjoint

def G (P : partition X) : Setoid X :=
{
  r := fun x y => ∃ A ∈ P.C, x ∈ A ∧ y ∈ A,
  iseqv := by
  {
    constructor
    -- reflexive
    { intro x
      rcases P.cover x with ⟨A, hA, hxA⟩
      use A, hA, hxA, hxA }
    -- symmetric
    { intro x y hxy
      rcases hxy with ⟨A, hA, hxA, hyA⟩
      use A, hA, hyA, hxA }
    -- transitive
    {
      intro x y z hxy hyz
      rcases hxy with ⟨s₁, hs₁P, ⟨hx, hy₁⟩⟩
      rcases hyz with ⟨s₂, hs₂P, ⟨hy₂, hz⟩⟩
      have h_eq : s₁ = s₂ := Partitions.subsets_equal P s₁ s₂ hs₁P hs₂P y hy₁ hy₂
      subst h_eq
      exact ⟨s₁, hs₁P, ⟨hx, hz⟩⟩
  }

}
