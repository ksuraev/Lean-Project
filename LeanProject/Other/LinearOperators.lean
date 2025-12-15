import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

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
  carrier := { x : V | ∀ s ∈ S, inner ℝ s x = 0 }
  zero_mem' := by
    intro s hs
    rw [inner_zero_right]
  add_mem' := by
    intro a b ha hb
    rw[Set.mem_setOf_eq] at *
    intro s hs
    rw[inner_add_right]
    rw[ha, hb, zero_add]
    exact hs
    exact hs
  smul_mem' := by
    intro c x hx
    rw[Set.mem_setOf_eq] at *
    intro s hs
    rw[inner_smul_right_eq_smul, hx, smul_zero]
    exact hs





end OrthogonalComplements
