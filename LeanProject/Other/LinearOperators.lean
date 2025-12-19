import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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

noncomputable def proj (S : Submodule ℝ V) [FiniteDimensional ℝ V] (w : V) (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S) : V :=
  ∑ i, inner ℝ w (b i) • (b i : V)

lemma proj_mem_subspace (S : Submodule ℝ V) (w : V) [FiniteDimensional ℝ V] (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S) : proj S w b ∈ S := by
  dsimp[proj]
  apply Submodule.sum_mem S
  intro i hi
  apply Submodule.smul_mem
  exact (b i).2

lemma sub_proj_orth_basis (S : Submodule ℝ V) [FiniteDimensional ℝ V] (w : V) (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S) : ∀ i, inner ℝ (w - proj S w b) (b i) = 0 := by
  intro i
  rw[inner_sub_left]
  have h : inner ℝ (proj S w b) (b i) = inner ℝ w (b i) := by
    dsimp[proj]
    rw[sum_inner]
    simp_rw [real_inner_smul_left, ← Submodule.coe_inner, b.inner_eq_ite]
    simp
  rw[h, sub_self]

lemma sub_proj_mem_orth (S : Submodule ℝ V) [FiniteDimensional ℝ V] (w : V) (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S) : w - proj S w b ∈ Sᗮ := by
  intro x hx
  let x' : S := ⟨x, hx⟩
  change inner ℝ (x' : V) (w - proj S w b) = 0
  rw[← b.toBasis.sum_repr x']
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [sum_inner]
  simp_rw [real_inner_smul_left, real_inner_comm]
  simp [sub_proj_orth_basis S w b]


lemma double_orth_subset_self (S : Submodule ℝ V) [FiniteDimensional ℝ V] (w : V) (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S)
  (h : w ∈ Sᗮᗮ) : w ∈ S := by
  let u : V := proj S w b
  let v : V := w - u
  have hu : u ∈ S := proj_mem_subspace S w b
  -- Show v ⊥ bᵢ, ⟨v, bᵢ⟩ = 0
  have h_v_orth_to_basis : ∀ j, inner ℝ v (b j) = 0 := sub_proj_orth_basis S w b
  -- Show v ∈ Sᗮ, ⟨v, x : S⟩ = 0
  have h_v_in_orth_S : v ∈ Sᗮ := sub_proj_mem_orth S w b
  have h_v_zero : v = 0 := by
    have h_v_in_orth_orth : v ∈ Sᗮᗮ := by
      apply Submodule.sub_mem Sᗮᗮ h
      exact Submodule.le_orthogonal_orthogonal S hu
    apply inner_self_eq_zero.mp (h_v_in_orth_orth v h_v_in_orth_S)
  -- Show w ∈ S
  rw[sub_eq_zero] at h_v_zero -- w = u
  rw[h_v_zero]
  exact hu

lemma subset_double_orth (S : Submodule ℝ V) (w : V) (h : w ∈ S) : w ∈ Sᗮᗮ := by
  intro s hs
  rw[real_inner_comm]
  rw[Submodule.inner_right_of_mem_orthogonal h hs]

theorem double_orth_eq_self [FiniteDimensional ℝ V] (S : Submodule ℝ V) (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S) : Sᗮᗮ = S := by
  apply le_antisymm
  -- Sᗮᗮ ⊆ S
  · intro w hw
    exact double_orth_subset_self S w b hw
  -- S ⊆ Sᗮᗮ
  · exact subset_double_orth S

lemma decomp_exists (S : Submodule ℝ V) [FiniteDimensional ℝ V] (w : V) (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S) :
  ∃ (v : Sᗮ), w = proj S w b + v := by
  let v_vec := w - proj S w b
  have hv : v_vec ∈ Sᗮ := sub_proj_mem_orth S w b
  use ⟨v_vec, hv⟩
  simp [v_vec]

-- ⊔ represents + but can use + for submodules
-- ⊤ represents whole space V
-- ⊓ represents ∪
-- ⊥ represents zero subspace {0}
theorem direct_sum (U W : Submodule ℝ V) (h : IsCompl U W) :
    U + W = ⊤ ∧ U ⊓ W = ⊥ := by
  exact ⟨h.sup_eq_top, h.inf_eq_bot⟩

-- IsCompl splits into Disjoint and Codisjoint
theorem unique_direct_sum (S : Submodule ℝ V) [FiniteDimensional ℝ V] :
  IsCompl S Sᗮ := by
  constructor
  case disjoint =>
    -- Any x in S and Sᗮ, x = 0
    rw[Submodule.disjoint_def]
    intro x hx_S hx_orth
    have h_inner_zero : inner ℝ x x = 0 := hx_orth x hx_S
    exact inner_self_eq_zero.mp h_inner_zero
  case codisjoint =>
    rw[codisjoint_iff, eq_top_iff] -- V ≤ S + Sᗮ
    intro w _
    rw [Submodule.mem_sup]
    refine ⟨proj S w, proj_mem_subspace S w, w - proj S w, sub_proj_mem_orth S w, ?_⟩
    simp
end OrthogonalComplements
