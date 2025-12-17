import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LinearOperators

variable {V W : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

structure LinearOperator (V W : Type _)
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] where
  toFun : V → W
  map_add' : ∀ (u v : V), toFun (u + v) = toFun u + toFun v
  map_smul' : ∀ (k : ℝ) (u : V), toFun (k • u) = k • toFun u

-- Allows for shorter hand notation of T.toFun v as T v
instance : CoeFun (LinearOperator V W) (fun _ => V → W) := ⟨LinearOperator.toFun⟩

def nullspace (T : LinearOperator V W) : Set V :=
  {v : V | T v = 0}

def range (T : LinearOperator V W) : Set W := { w : W | ∃ v, T v = w }

-- Nullspace of T is a subspace
def nullspace_is_subspace (T : LinearOperator V W) : Subspace ℝ V where
  -- The 'carrier' is the underlying set of the subspace
  carrier := nullspace T
  zero_mem' := by
    rw[nullspace, Set.mem_setOf_eq]
    -- Show T(0) = 0
    have h : T 0 = T ((0 : ℝ) • 0) := by rw[zero_smul]
    rw[h, T.map_smul', zero_smul]
  add_mem' := by
    intro a b ha hb
    rw[nullspace, Set.mem_setOf_eq] at *
    rw[T.map_add', ha, hb, zero_add]
  smul_mem' := by
    intro c x hx
    rw[nullspace, Set.mem_setOf_eq] at *
    rw[T.map_smul', hx, smul_zero]

-- Range of T is a subspace
def range_is_subspace (T : LinearOperator V W) : Subspace ℝ W where
  carrier := range T
  zero_mem' := by
    rw[range, Set.mem_setOf_eq]
    use 0
    have h : T 0 = T ((0 : ℝ) • 0) := by rw[zero_smul]
    rw[h, T.map_smul', zero_smul]
  add_mem' := by
    intro a b ha hb
    rw[range, Set.mem_setOf_eq] at *
    rcases ha with ⟨u1, rfl⟩
    rcases hb with ⟨u2, rfl⟩
    use u1 + u2
    rw[T.map_add']
  smul_mem' := by
    intro c x hx
    rw[range, Set.mem_setOf_eq] at *
    rcases hx with ⟨k, rfl⟩
    use c • k
    rw[T.map_smul']

end LinearOperators

namespace OrthogonalComplements
open LinearOperators

variable {V W : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]


def orthogonal_complement
(S : Subspace ℝ V) : Subspace ℝ V where
  -- All x such that ⟨x, s⟩ = 0 for every s in S
  carrier := { x : V | ∀ s ∈ S, inner ℝ x s = 0 }
  zero_mem' := by
    intro s _
    rw [inner_zero_left]
  add_mem' := by
    intro a b ha hb s hs
    rw[Set.mem_setOf_eq] at *
    rw[inner_add_left]
    rw[ha s hs, hb s hs, zero_add]
  smul_mem' := by
    intro c x hx s hs
    rw[Set.mem_setOf_eq] at *
    rw[inner_smul_left_eq_smul, hx s hs, smul_zero]

-- For Sᗮᗮ = S we need:
-- Sᗮᗮ ⊆ S: show v = w - u is orthogonal to every basis vector  bᵢ to then show that v ∈ Sᗮ. Show w ∈ Sᗮᗮ means w is orthogonal to every vector v and derive subset inclusion
-- S ⊆ Sᗮᗮ: assume x ∈ S, then x is orthogonal to every vector in Sᗮ but it is also in the orthogonal complement of Sᗮ so x ∈ Sᗮᗮ

lemma double_orth_subset_self (S : Submodule ℝ V) [FiniteDimensional ℝ V] (w : V)
  (h : w ∈ Sᗮᗮ) : w ∈ S := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S :=
    stdOrthonormalBasis ℝ S
  let u : S := ∑ i, inner ℝ w (b i) • (b i)
  let v : V := w - u
  -- Show v ⊥ bᵢ, ⟨v, bᵢ⟩ = 0
  have h_v_orth_to_basis : ∀ j, inner ℝ v (b j) = 0 := by
    intro j
    rw [inner_sub_left]
    dsimp[u]
    simp_rw [← Submodule.coe_inner]
    rw[sum_inner]
    simp_rw [real_inner_smul_left, b.inner_eq_ite]
    simp
  -- Show v ∈ Sᗮ, ⟨v, x : S⟩ = 0
  have h_v_in_orth_S : v ∈ Sᗮ := by
    intro x hx
    let x_sub : S := ⟨x, hx⟩
    change inner ℝ (x_sub : V) v = 0
    rw [real_inner_comm]
    nth_rw 1 [← b.toBasis.sum_repr x_sub]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw[inner_sum]
    simp_rw [inner_smul_right]
    simp [h_v_orth_to_basis]
  have hvw : inner ℝ v w = 0 := by
    rw [Submodule.inner_right_of_mem_orthogonal h_v_in_orth_S h]
  have hvu : inner ℝ v u = 0 := by
    rw[real_inner_comm]
    exact h_v_in_orth_S (u : V) u.2
  have hvv : inner ℝ v v = 0 := by
    change inner ℝ (w - u) v = 0
    rw[inner_sub_left]
    rw[real_inner_comm] at hvw hvu
    rw[hvw, hvu, sub_zero]
  have h_v_zero : v = 0 := inner_self_eq_zero.mp hvv
  rw[sub_eq_zero] at h_v_zero
  rw[h_v_zero]
  exact u.2

lemma subset_double_orth (S : Submodule ℝ V) (w : V) (h : w ∈ S) : w ∈ Sᗮᗮ := by
  intro s hs
  rw[real_inner_comm]
  rw[Submodule.inner_right_of_mem_orthogonal h hs]

theorem double_orth_eq_self [FiniteDimensional ℝ V] (S : Submodule ℝ V) : Sᗮᗮ = S := by
  apply le_antisymm
  -- Sᗮᗮ ⊆ S
  · intro w hw
    exact double_orth_subset_self S w hw
  -- S ⊆ Sᗮᗮ
  · exact subset_double_orth S





end OrthogonalComplements
