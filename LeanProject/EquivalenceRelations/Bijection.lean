import Init.Notation
import Mathlib.Data.Set.Operations
import LeanProject.EquivalenceRelations.PartitionInducedRelation
import LeanProject.EquivalenceClasses.Properties
import LeanProject.Partitions.Properties

-- Bijection between Equivalence Relations and Partitions

namespace EqRelBijection

open EqClasses_Setoid
open InducedRelation
open Partitions

-- Rewrite subset_equal to use in the bijection proof
lemma eq_of_mem
  {α} (P : Partition α) {s t : Set α}
  (hs : s ∈ P.subsets) (ht : t ∈ P.subsets)
  {a : α} (ha_s : a ∈ s) (ha_t : a ∈ t) :
  s = t := by
  apply subsets_equal P s t hs ht a ha_s ha_t

-- Define F and G functions and prove that the composite maps are identity functions
-- https://github.com/kbuzzard/xena/blob/268b3bab45ba8fbed09b45cbbdc80a3813f73b5e/partitions.lean#L4

-- Helper lemma to show that a subset in a partition is equal to the equivalence class induced by the partition
lemma subset_eq_equiv_class {X : Type _} (P : Partition X) (s : Set X) (hs : s ∈ P.subsets)
  (a : X) (ha : a ∈ s) :
  s = {x | induced_rel P x a} := by
  ext x
  constructor
  · intro hxs
    rw[Set.mem_setOf_eq]
    use s
  · intro hPxa
    rcases hPxa with ⟨t, htP, hxt, hat⟩
    have hst : s = t := eq_of_mem P hs htP ha hat
    rw[hst]
    exact hxt

-- Define the functions F and G
def F (S : Setoid X) : Partition X :=
  eq_classes_form_partition_sub S


def G (P : Partition X) : Setoid X :=
  ⟨induced_rel P, induced_rel_is_equivalence P⟩


-- Almost the same as the right_inv and left_inv proofs above
theorem FG_eq_id (P : Partition X) : F (G P) = P := by
  ext s -- s ∈ (F (G P)).subsets ↔ s ∈ P.subsets
  dsimp [F, G, eq_classes_form_partition_sub]
  constructor
  -- 1. Assume s ∈ eq_classes { r := induced_rel P, iseqv := ⋯ }
  · intro hs
    -- there exists a ∈ X such that s = {x | induced_rel P x a}
    rcases hs with ⟨a, rfl⟩
    -- Simplify the goal to show {x | induced_rel P x a} ∈ P.subsets
    simp [equiv_class]
    -- show that a ∈ ⋃₀ P.subsets
    have ha : a ∈ Set.sUnion P.subsets := by
      rw [P.union_eq_univ]
      exact Set.mem_univ a
    -- there exists t ∈ P.subsets such that a ∈ t
    rcases Set.mem_sUnion.mp ha with ⟨t, htP, hat⟩
    -- show {x | induced_rel P x a} = t
    have h_eq : { x | induced_rel P x a } = t := by
      apply symm (subset_eq_equiv_class P t htP a hat)
    -- Apply the equality to rewrite the goal
    rw [h_eq] -- t ∈ P.subsets
    exact htP
  -- 2. Assume s ∈ P.subsets
  · intro hsP
    -- there exists a ∈ X such that a ∈ s
    rcases P.nonempty_subsets s hsP with ⟨a, ha⟩ -- ha : a ∈ s
    use a -- s = [a]_{ r := induced_rel P, iseqv := ⋯ }
    simp [equiv_class] -- ⊢ s = {x | induced_rel P x a}
    ext x -- apply extensionality to x ∈ s ↔ x ∈ {x | induced_rel P x a}
    constructor
    · -- Assume x ∈ s
      intro hxs
      rw [Set.mem_setOf_eq]
      use s
    · -- Assume x ∈ {x | induced_rel P x a}
      intro hRxa
      -- there exists t ∈ P.subsets such that x ∈ t and a ∈ t
      rcases hRxa with ⟨t, htP, hxt, hat⟩
      -- show s = t
      have hst : s = t := eq_of_mem P hsP htP ha hat
      rw [hst] -- Goal: x ∈ t
      exact hxt


theorem GF_eq_id (S : Setoid X) : G (F S) = S := by
  ext x y -- (G (F S)) x y ↔ S x y
  dsimp [G, F, induced_rel, eq_classes_form_partition_sub] -- simplify definitions
  constructor
  · -- 1. Assume (∃ s ∈ eq_classes S, x ∈ s ∧ y ∈ s)
    intro hxy
    -- Add partition definition
    let P := (eq_classes_form_partition_sub S : Partition X)
    -- Then, there exists s ∈ eq_classes S such that x ∈ s and y ∈ s
    rcases hxy with ⟨s, hsP, ⟨hx, hy⟩⟩
    -- Introduce equality of subsets
    have hP_eq : eq_classes S = P.subsets := (eq_classes_form_partition_sub S).property
    -- Rewrite hsP: s ∈ eq_classes S to s ∈ P.subsets
    rw [hP_eq] at hsP
    -- There exists a ∈ X such that x ∈ [a]_R and y ∈ [a]_R
    rcases hsP with ⟨a, rfl⟩
    -- Therefore, x ≈ y under S
    exact S.trans hx (S.symm hy)
  · -- 2. Assume S x y
    intro hRxy
    -- Use the equivalence class of x under S
    use equiv_class S x
    constructor
    · -- Show [x]_S ∈ eq_classes S
      exact ⟨x, rfl⟩
    · -- Show x ∈ [x]_S and y ∈ [x]_S
      constructor
      · -- x ∈ [x]_S by reflexivity
        exact S.refl x
      · -- y ∈ [x]_S by symmetry and transitivity
        exact S.symm hRxy

-- Final bijection definition
def partitions_biject_with_equivalence_relations :
  Equiv (Setoid X) (Partition X) := by
  refine
    { toFun := F,
      invFun := G,
      left_inv := GF_eq_id,
      right_inv := FG_eq_id }

-- Prove that a function F : S → P is a bijection if and only if it is both injective and surjective where S is the set of equivalence relations and P is the set of partitions on X

theorem F_injective {X : Type _} : ∀ (S1 S2 : Setoid X), F S1 = F S2 → S1 = S2 := by
  intros S1 S2 h
  -- apply G to the equality and use GF_eq_id to simplify
  have h2 : G (F S1) = G (F S2) := congrArg G h
  -- G (F S1) = S1 and G (F S2) = S2 by GF_eq_id, so S1 = S2
  simp [GF_eq_id] at h2
  exact h2

theorem F_surjective {X : Type _} : ∀ P : Partition X, ∃ S : Setoid X, F S = P := by
  intro P
  use G P
  exact FG_eq_id P

theorem F_bijective {X : Type _} : Function.Bijective (F : Setoid X → Partition X) :=
  ⟨F_injective, F_surjective⟩
end EqRelBijection

-- First draft of the bijection
namespace EqRelBijectionDraft

open EqClasses_Setoid
open InducedRelation
open Partitions

-- the // indicates a subtype, meaning we are considering only those relations R that are equivalence relations (All the elements of a type that satisfy a predicate.) https://leanprover-community.github.io/mathlib4_docs/Init/Notation.html#%C2%ABterm{_:_//_}%C2%BB

-- Using the equiv structure to define a bijection between equivalence relations and partitions
-- Source: https://github.com/leanprover-community/mathlib4/blob/82ce028190bb8ed1a85ff2347d892c72aa439bef/Mathlib/Logic/Equiv/Defs.lean#L62-L73

lemma eq_of_mem
  {α} (P : Partition α) {s t : Set α}
  (hs : s ∈ P.subsets) (ht : t ∈ P.subsets)
  {a : α} (ha_s : a ∈ s) (ha_t : a ∈ t) :
  s = t := by
  apply subsets_equal P s t hs ht a ha_s ha_t

-- First draft
def eqrel_partition_bijection (X : Type _) : { R : X → X → Prop // Equivalence R } ≃ Partition X :=
{
  -- Define the forward function from equivalence relations to partitions
  toFun := fun ⟨R, hR⟩ => eq_classes_form_partition_sub ⟨R, hR⟩,
  -- Define the inverse function from partitions to equivalence relations
  invFun := fun P => ⟨induced_rel P, induced_rel_is_equivalence P⟩,
  -- Claiming toFun and invFun are inverses
  left_inv := by
    intro R
    dsimp
    ext x y -- the equivalence relation induced by the partition of equivalence classes is the same as the original equivalence relation R
    rcases R with ⟨R, hR⟩ -- unpack the subtype to get R and its equivalence property
    let S := Setoid.mk R hR
    let P := (eq_classes_form_partition_sub ⟨R, hR⟩ : Partition X)
    constructor
    · intro h
      rcases h with ⟨s, hsP, ⟨hx, hy⟩⟩
      have hP_eq : P.subsets = eq_classes S := (eq_classes_form_partition_sub ⟨R, hR⟩).property
      rw [hP_eq] at hsP -- s ∈ eq_classes S
      rcases hsP with ⟨a, rfl⟩ -- s = [a]_R
      -- Prove R x y
      have hxa : x ≈ a := hx
      have hya : y ≈ a := hy
      exact S.trans hxa (S.symm hya)
    -- Prove the other direction
    · intro hRxy
    -- witness: the class equiv_class S x contains both x and y
      use equiv_class S x
      constructor
      · -- show equiv_class S x ∈ eq_classes S
        exact ⟨x, rfl⟩
      · -- x ∈ equiv_class S x and y ∈ equiv_class S x
        constructor
        · exact hR.refl x
        · change x ≈ y at hRxy
          change y ≈ x
          exact S.symm hRxy
  right_inv := by
    intro P
    dsimp
    ext s
    constructor
    · intro hs
      rcases hs with ⟨a, rfl⟩ -- [a]_R ∈ P.subsets
      simp [equiv_class]
      have ha : a ∈ Set.sUnion P.subsets := by
        simp [P.union_eq_univ]
      rcases Set.mem_sUnion.mp ha with ⟨t, htP, hat⟩
      let R := induced_rel P
      let S := Setoid.mk R (induced_rel_is_equivalence P)
      have h_eq : { x | R x a } = t := by
        ext x
        constructor
        · intro hx
          rw[Set.mem_setOf_eq] at hx
          rcases hx with ⟨u, huP, hxu, hau⟩
          have hut : u = t := eq_of_mem P huP htP hau hat
          simpa [hut] using hxu
        · intro hxt
          rw[Set.mem_setOf_eq]
          use t
      rw [h_eq]
      exact htP
    · intro hsP
      rcases P.nonempty_subsets s hsP with ⟨a, ha⟩
      use a
      simp [equiv_class]
      -- Need to prove that s = { x | R x a }
      ext x
      constructor
      · intro hxs
        rw[Set.mem_setOf_eq]
        use s
      · intro hRxa
        rcases hRxa with ⟨t, htP, hxt, hat⟩
        have hst : s = t := eq_of_mem P hsP htP ha hat
        rw[hst]
        exact hxt
}

end EqRelBijectionDraft
