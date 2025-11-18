import LeanProject.EquivalenceClasses.Properties
import LeanProject.Partitions.Properties

namespace InducedRelation
open Partitions
open EqClasses_Setoid

-- Define the induced relation by a partition:
-- For a partition P of a set α, we define a relation on α
-- where x is related to y if they belong to the same subset in P.
def induced_rel {α : Type _} (P : Partition α) : α → α → Prop :=
  fun x y => ∃ s ∈ P.subsets, x ∈ s ∧ y ∈ s


-- Prove that induced_rel is an equivalence relation
lemma induced_rel_refl {α : Type _} (P : Partition α) :
    ∀ x : α, induced_rel P x x := by
  intro x
  have h_union : Set.sUnion P.subsets = Set.univ := P.union_eq_univ
  obtain ⟨s, hsP, hx⟩ := Set.mem_sUnion.mp (by
    rw [h_union]
    exact Set.mem_univ x)
  exact ⟨s, hsP, ⟨hx, hx⟩⟩

lemma induced_rel_symm {α : Type _} (P : Partition α) : ∀ x y : α, induced_rel P x y → induced_rel P y x := by
  intro x y hxy
  rcases hxy with ⟨s, hsP, ⟨hx, hy⟩⟩
  exact ⟨s, hsP, ⟨hy, hx⟩⟩

lemma induced_rel_trans {α : Type _} (P : Partition α) : ∀ x y z : α, induced_rel P x y → induced_rel P y z → induced_rel P x z := by
  intro x y z hxy hyz
  rcases hxy with ⟨s₁, hs₁P, ⟨hx, hy₁⟩⟩
  rcases hyz with ⟨s₂, hs₂P, ⟨hy₂, hz⟩⟩
  have h_eq : s₁ = s₂ := Partitions.subsets_equal P s₁ s₂ hs₁P hs₂P y hy₁ hy₂
  subst h_eq
  exact ⟨s₁, hs₁P, ⟨hx, hz⟩⟩


theorem induced_rel_is_equivalence {α : Type _} (P : Partition α) :
    Equivalence (induced_rel P) :=
{ refl := induced_rel_refl P,
  symm := @induced_rel_symm α P, -- disable implicit arguments
  trans := @induced_rel_trans α P }



end InducedRelation
