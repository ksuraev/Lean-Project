import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Set.Defs
import Mathlib.Order.RelClasses
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

-- Simple example mirroring Example 4.7 from report
namespace Example

def powerset : Set (Set ℕ) :=
  Set.powerset {1, 2, 3}

-- Define a partial order on the subset relation on sets of natural numbers
instance subsetPartialOrder : PartialOrder (Set ℕ) where
  le := (· ⊆ ·)
  le_refl := by
    intro A
    exact Set.Subset.refl A
  le_trans := by
    intro a b c
    exact Set.Subset.trans
  le_antisymm := by
    intro A B
    exact Set.Subset.antisymm

def R (X Y : Set ℕ) : Prop := X ⊆ Y
local infix:50 " ≼ " => R

-- Prove that for any sets X and Y in the powerset of {ℕ}, if X ≼ Y then X ⊆ Y
example (P : Set (Set ℕ)) (hR : ∀ X Y, X ≼ Y → X ⊆ Y) : ∀X ∈ P, ∀Y ∈ P, X ≼ Y → X ⊆ Y := by
  intros X hX Y hY hXY
  exact hR X Y hXY

end Example

namespace MaxMinElements

-- Define maximal and minimal
-- https://www.uv.es/coslloen/Lean4/Leancap11.html
def maximal {S : Type _} [PartialOrder S] (z : S) : Prop := ∀ {a : S}, z ≤ a → a = z

def minimal {S : Type _} [PartialOrder S] (z : S) : Prop  := ∀ {a : S}, a ≤ z → a = z

lemma exists_minimal_classical
    (α : Type _) [Fintype α] [PartialOrder α] [Nonempty α] :
  ∃ m : α, minimal m := by
  classical
  -- Define P(k) - inductive hypothesis
  let P := fun (k : ℕ) =>
    ∀ {β : Type _} [Fintype β] [PartialOrder β] [Nonempty β],
      Fintype.card β = k → ∃ m : β, minimal m
  -- Base case k = 1
  have base : P 1 := by
    intros β _ _ _  hcard
    -- If card is 1, the only element is minimal
    rcases (Fintype.card_eq_one_iff.mp hcard) with ⟨x, hx⟩
    use x
    intro y hy
    apply hx
  -- Inductive step: For some k : ℕ where k ≥ 1, P(k) → P(k + 1)
  have step : ∀ (k : ℕ), 1 ≤ k → P k → P (k + 1) := by
    intros k hk_pos ih β _ _ _ hcard
    -- Choose arbitrary x from β
    let x := Classical.choice (inferInstance : Nonempty β)
    -- Define subtype of remaining elements not equal to `x`
    let β_sub := { y : β // y ≠ x }
    -- Define the cardinality of the remaining elements to be k
    have hcard_sub : Fintype.card β_sub = k := by
      simp [β_sub, hcard]
    -- Show that the remaining set is nonempty
    have : Nonempty β_sub := by
      rw [← Fintype.card_pos_iff, hcard_sub]; exact hk_pos
    -- Deconstruct the inductive hypothesis and cardinality of subset
    -- We are saying we have some m : β such that m ≠ x and m is a minimal element
    rcases ih hcard_sub with ⟨⟨m, hm_ne⟩, hm_min⟩
    by_cases hxm : x < m
    · -- Case 1: x < m. We claim 'x' is minimal in the whole set.
      use x
      intro y hy -- Assume y ≤ x
      -- We want to show that x is minimal, i.e. for any y ≤ x, y = x
      by_contra h_neq -- Assume y ≠ x
      -- Derive y < x from y ≤ x and y ≠ x
      have y_lt_x : y < x := lt_of_le_of_ne hy h_neq
      -- Derive y < m from y < x and x < m
      have y_lt_m : y < m := lt_trans y_lt_x hxm
      -- Since we have assumed there is a minimal y then y must be in β_sub
      let y_sub : β_sub := ⟨y, h_neq⟩
      -- But m is a minimal element with rcases of β_sub
      have y_eq_m : y_sub = ⟨m, hm_ne⟩ := hm_min (le_of_lt y_lt_m)
      -- Simplify subtypes and constructors to get y = m
      rw [Subtype.ext_iff] at y_eq_m
      simp at y_eq_m
      change y = m at y_eq_m
      -- Rewrite y < m with y = m to get m < m
      rw [y_eq_m] at y_lt_m
      -- m < m closes false goal
      exact lt_irrefl m y_lt_m
    · -- Case 2: m is the minimal element in the whole set
      use m
      intro y hy -- Assume y ≤ m
      rcases eq_or_ne y x with rfl | h_ne
      · -- y = x case: If y = x (element we removed) and not strictly less than m then x = m
        exact eq_of_le_of_not_lt hy hxm
      · -- y ≠ x case: y must be in the subset and y = m
        have h_sub_eq : (⟨y, h_ne⟩ : β_sub) = ⟨m, hm_ne⟩ := hm_min (Subtype.mk_le_mk.mpr hy)
        rw [Subtype.ext_iff] at h_sub_eq
        exact h_sub_eq
  -- Prove P holds for n
  -- Set n to be the number of elements (card)
  let n := Fintype.card α
  -- Set condition that n ≥ 1
  have n_pos : 1 ≤ n := by
    have : 0 < n := Fintype.card_pos_iff.mpr (inferInstance : Nonempty α)
    exact Nat.succ_le_of_lt this
  have P_n : P n := Nat.le_induction (m := 1) (P := fun k _ => P k) base step n n_pos
  -- P_n needs the proof that 'card α = n', which is true by definition (rfl)
  exact P_n rfl

lemma exists_minimal_constructive
    (α : Type _) [Fintype α] [PartialOrder α] [Nonempty α]
    [DecidableRel (fun (x y : α) => x ≤ y)] -- Allows computation of `if x < y`
    [DecidableEq α] -- Allows computation of `if x == y`
    : ∃ m : α, minimal m := by
  let S : Finset α := Finset.univ
  -- Define what it means to be a minimal element in S
  let minimal_in (S : Finset α) (m : α) := m ∈ S ∧ ∀ y ∈ S, y ≤ m → y = m
  -- Claim that every finite nonempty set S has a minimal element m
  have claim : ∀ S : Finset α, S.Nonempty → ∃ m, minimal_in S m := by
    intro S
    -- Induction on Finset S
    induction S using Finset.induction_on with
    -- Base case: empty finset
    | empty =>
      -- the empty set cannot be Nonempty
      intro h_empty
      simp at h_empty
    -- Insert an element a into S and show prop holds
    | insert a S _ ih =>
      intro _
      -- Case 1: S is empty, then inserting a gives us {a}
      if h_s_empty : S = ∅ then
        use a
        constructor
        -- a ∈ insert a S
        · simp
        -- ∀ y ∈ insert a S, y ≤ a → y = a
        · intros y hy y_le_a
          simp [h_s_empty] at hy
          exact hy
      -- Case 2: S is not empty so use induction hypothesis on S
      else
        have s_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_s_empty
        rcases ih s_nonempty with ⟨m, hm_in_s, hm_min_s⟩
        -- Compare the new element 'a' with the old minimal 'm'
        -- Subcase 1: claim 'a' is the new minimal
        if a_le_m : a ≤ m then
          use a
          constructor
          · simp
          · intros y hy y_le_a
            simp at hy -- y = a ∨ y ∈ S
            cases hy with
            | inl y_eq_a => exact y_eq_a
            | inr y_in_s =>
              -- we have a ≤ m and y ≤ a so y ≤ m
              have y_le_m : y ≤ m := le_trans y_le_a a_le_m
              -- But m is minimal so y = m
              have y_eq_m : y = m := hm_min_s y y_in_s y_le_m
              rw[y_eq_m] at ⊢ y_le_a
              exact le_antisymm y_le_a a_le_m
        else
          -- Subcase 2: claim ¬a ≤ m, so m is minimal
          use m
          constructor
          · simp; right; exact hm_in_s
          · intro y hy y_le_m
            simp at hy
            cases hy with
            | inl y_eq_a =>
              rw [y_eq_a] at y_le_m
              contradiction -- ¬a ≤ m and a ≤ m
            | inr y_in_s =>
              exact hm_min_s y y_in_s y_le_m
  -- Apply the claim to the universal set
  have univ_nonempty : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
  rcases claim Finset.univ univ_nonempty with ⟨m, hm_in_univ, hm_min_local⟩
  use m
  -- We need to prove minimal m
  intros a ha
  have a_in_univ : a ∈ Finset.univ := Finset.mem_univ a
  exact hm_min_local a a_in_univ ha


theorem exists_maximal_classical (α : Type _) [Fintype α] [PartialOrder α] [Nonempty α] :
  ∃ m : α, maximal m := by
  classical
  let n := Fintype.card α
  have n_pos : 1 ≤ n := by
    have : 0 < n := Fintype.card_pos_iff.mpr (inferInstance : Nonempty α)
    exact Nat.succ_le_of_lt this
  let P := fun (k : ℕ) =>
    ∀ {β : Type _} [Fintype β] [PartialOrder β] [Nonempty β],
      Fintype.card β = k → ∃ m : β, maximal m
  have base : P 1 := by
    intros β _ _ _ hcard
    -- If card is 1, the only element is maximal
    -- There exists some x ∈ β such that ∀ y, y = x
    rcases (Fintype.card_eq_one_iff.mp hcard) with ⟨x, hx⟩
    use x
    intro y hy
    apply hx
  have step : ∀ (k : ℕ), 1 ≤ k → P k → P (k + 1) := by
    intros k hk_pos ih β _ _ _ hcard
    let x := Classical.choice (inferInstance : Nonempty β)
    -- Define the subtype of elements in set without x
    let β_sub := {y : β // y ≠ x}
    have hcard_sub : Fintype.card β_sub = k := by
      simp[β_sub, hcard]
    have : Nonempty β_sub := by
      rw [← Fintype.card_pos_iff, hcard_sub]; exact hk_pos
    rcases ih hcard_sub with ⟨⟨m, hm_ne⟩, hm_max⟩
    -- Claim x is maximal
    by_cases x_is_max : m < x
    · use x
      intro y hy
      -- If x < y, we get x contradiction
      by_contra h_neq -- assume y ≠ x
      -- Assume y is maximal
      have x_lt_y : x < y :=  LE.le.lt_of_ne' hy h_neq
      have m_lt_y : m < y := lt_trans' x_lt_y x_is_max
      let y_sub : β_sub := ⟨y, h_neq⟩
      -- But we said m is maximal so must be y = m
      have y_eq_m : y_sub = ⟨m, hm_ne⟩ := hm_max (le_of_lt m_lt_y)
      rw [Subtype.ext_iff] at y_eq_m
      simp at y_eq_m
      change y = m at y_eq_m
      rw[y_eq_m] at m_lt_y
      exact lt_irrefl m m_lt_y
    · -- Case 2: `m` is the maximal element
      use m
      intro y hy
      if h_eq : y = x then
        rw[h_eq] at hy ⊢
        exact eq_of_le_of_not_lt' hy x_is_max
      else
        let y_sub : β_sub := ⟨y, h_eq⟩
        have : y_sub = ⟨m, hm_ne⟩ := hm_max hy
        rw[Subtype.ext_iff] at this
        simp at this
        change y = m at this
        rw[this]
  -- Induction on n
  have P_holds : ∀ k, 1 ≤ k → P k := by
    intro k
    induction k with
    | zero =>
      intro _
      linarith
    | succ k' ih' =>
      intro hk_pos'
      match k' with
      | 0 => simp; apply base
      | (n + 1) =>
        apply step (n + 1)
        · simp
        · apply ih'; simp
  apply P_holds n n_pos
  rfl





end MaxMinElements

namespace LeastGreatestElements
-- Define least and greatest
-- https://www.uv.es/coslloen/Lean4/Leancap11.html
def least {A : Type} (R : A → A → Prop) (z : A) : Prop := ∀ {a : A}, R z a

def greatest {A : Type} (R : A → A → Prop) (z : A) : Prop := ∀ {a : A}, R a z


end LeastGreatestElements
