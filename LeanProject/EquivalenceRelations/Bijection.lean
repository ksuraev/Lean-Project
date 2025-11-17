import Init.Notation
import Mathlib.Data.Set.Operations
import LeanProject.EquivalenceRelations.PartitionInducedRelation
import LeanProject.EquivalenceClasses.Properties
import LeanProject.Partitions.Properties
-- Bijection between Equivalence Relations and Partitions
-- S is the collection of all equivalence relations on a set X.
-- U is the set of all partitions of X.
-- There is a bijection F from S to U , meaning there is a bijection between a set’s equivalence relations and partitions.
-- For every equivalence relation R ↓ S, if xRy, then x and y are in the same set of F (R).
-- Let X be a set, let S= {R | R is an equivalence relation on X}, and let U= {P |
-- P is a partition of X},
-- There is a bijection F : S ≃ U , such that ↗R ↓ S, if xRy, then x and y are in the same
-- set of F (R) [15].

namespace EqRelBijection
open EqClasses_Setoid
open InducedRelation
open Partitions
-- the // indicates a subtype, meaning we are considering only those relations R that are equivalence relations (All the elements of a type that satisfy a predicate.) https://leanprover-community.github.io/mathlib4_docs/Init/Notation.html#%C2%ABterm{_:_//_}%C2%BB

-- Using the equiv structure to define a bijection between equivalence relations and partitions
-- Source: https://github.com/leanprover-community/mathlib4/blob/82ce028190bb8ed1a85ff2347d892c72aa439bef/Mathlib/Logic/Equiv/Defs.lean#L62-L73
/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse.
structure Equiv (α : Sort*) (β : Sort _) where
  /-- The forward map of an equivalence.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : α → β
  /-- The backward map of an equivalence.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl --/

def toSetoid {α : Type _} (R : { R : α → α → Prop // Equivalence R }) : Setoid α :=
{ r := R.val,
  iseqv := R.property }


def equiv_of_partition {α : Type _} (P : Partition α) : α → α → Prop :=
  induced_rel P

lemma equiv_of_partition_equiv {α : Type _} (P : Partition α) :
    Equivalence (equiv_of_partition P) :=
  induced_rel_is_equivalence P

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
    ext x y
    constructor
    · intro h
      rcases h with ⟨s, hsP, ⟨hx, hy⟩⟩
      have R_setoid := toSetoid R
      have R_equiv := R.property -- Equivalence R
      -- Prove R x y
      have x_eq_class : x ∈ EqClasses_Setoid.equiv_class R_setoid x := R_setoid.iseqv.1 x
      have s_eq_class : s = EqClasses_Setoid.equiv_class R_setoid x := by
        apply Partitions.subsets_equal
    sorry,
  right_inv := by
    intro P
    ext x
    dsimp
    sorry

}

-- as theorem
theorem eqrel_bij_partition (X : Type u) :
  ∃ (f : { R : X → X → Prop // Equivalence R } ≃ Partitions.Partition X), True :=
⟨{ toFun := λ ⟨R, hR⟩ => sorry,
    invFun := λ P => sorry,
    left_inv := λ R => sorry, -- Prove that applying `toFun` and then `invFun` gives the original equivalence relation
    right_inv := λ P => sorry -- Prove that applying `invFun` and then `toFun` gives the original partition
  }, trivial⟩

def F (S : Setoid X) : Partition X := sorry
end EqRelBijection
