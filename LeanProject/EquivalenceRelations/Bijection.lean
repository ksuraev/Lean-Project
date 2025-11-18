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
-- the // indicates a subtype, meaning we are considering only those relations R that are equivalence relations (All the elements of a type that satisfy a predicate.) https://leanprover-community.github.io/mathlib4_docs/Init/Notation.html#%C2%ABterm{_:_//_}%C2%BB

-- Using the equiv structure to define a bijection between equivalence relations and partitions
-- Source: https://github.com/leanprover-community/mathlib4/blob/82ce028190bb8ed1a85ff2347d892c72aa439bef/Mathlib/Logic/Equiv/Defs.lean#L62-L73

def toSetoid {α : Type _} (R : { R : α → α → Prop // Equivalence R }) : Setoid α :=
{ r := R.val,
  iseqv := R.property }

def equiv_of_partition {α : Type _} (P : Partition α) : α → α → Prop :=
  induced_rel P

lemma equiv_of_partition_equiv {α : Type _} (P : Partition α) :
    Equivalence (equiv_of_partition P) :=
  induced_rel_is_equivalence P

lemma eq_of_mem
  {α} (P : Partition α) {s t : Set α}
  (hs : s ∈ P.subsets) (ht : t ∈ P.subsets)
  {a : α} (ha_s : a ∈ s) (ha_t : a ∈ t) :
  s = t := by
  apply subsets_equal P s t hs ht a ha_s ha_t

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












-- as theorem
theorem eqrel_bij_partition (X : Type u) :
  ∃ (f : { R : X → X → Prop // Equivalence R } ≃ Partitions.Partition X), True :=
⟨{ toFun := λ ⟨R, hR⟩ => sorry,
    invFun := λ P => sorry,
    left_inv := sorry,
    right_inv := sorry
  }, trivial⟩

def F (S : Setoid X) : Partition X := sorry
end EqRelBijection
