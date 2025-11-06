import Mathlib
import Init.Prelude
import Mathlib.Data.Set.Defs

namespace EquivalenceClasses

variable {α : Type}
variable {R : α → α → Prop}
variable {a : α}

-- Define BinRel as a type alias for binary relations
-- A → A → Prop - function that takes two elements of type A and returns a proposition indicating whether the relation holds
def BinRel (A : Type) := A → A → Prop

def EquivRel {A : Type} (R : BinRel A) : Prop :=
  Reflexive R ∧ Symmetric R ∧ Transitive R

def EquivClass {A : Type} (R : BinRel A) (x : A) : Set A :=
  {y | R y x}

-- Define notation for equivalence class
notation:100 "[" a "]_" R:100 => EquivClass R a

#check [a]_R

-- Property 1: Every element belongs to its own equivalence class - ∀a ∈ S, a ∈ [a]
lemma Property1 {A : Type} (R : BinRel A) (h_reflexive : ∀ x : A, R x x) (a : A) : a ∈ [a]_R := by
  exact h_reflexive a

-- Property 2: ∀a, b ∈ S, aRb if and only if [a] = [b]
lemma Property2 {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  constructor -- removes bidirectional implication
  intro h_aRb
  apply Set.ext -- remove the set equality goal and replace it with membership goal
  intro y
  constructor
  { intro h_yRa
    exact h_trans h_yRa h_aRb } -- use transitivity to show R y b
  { intro h_yRb
    have h_bRa := h_symm h_aRb -- use symmetry to show R b a
    exact h_trans h_yRb (h_bRa) } -- use transitivity to show R y a
  intro h_eq_classes
  exact h_eq_classes ▸ h_refl a -- ▸ operator is used for substitution and rewrites goal using equality h_eq_classes

-- Alternative proof using `rw` tactic
lemma Property2' {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
  unfold EquivClass
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  -- Forward direction
  constructor
  { intro h_aRb
    apply Set.ext
    intro y
    constructor
    { intro h_yRa
      exact h_trans h_yRa h_aRb }
    { intro h_yRb
      have h_bRa := h_symm h_aRb
      exact h_trans h_yRb h_bRa } }
  -- Backward direction
  { intro h_eq_classes
    rw[← h_eq_classes]
    exact h_refl a }

-- Alternative proof using lambda functions
lemma Property2'' {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
  unfold EquivClass
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  constructor
  { intro h_aRb
    apply Set.ext
    intro y
    -- 1st Lambda function taking assumption h_yRa and returns transitive property on h_yRa and h_aRb to conclude yRb (proves if y ∈ [a], then y ∈ [b])
    -- 2nd lambda func takes assumption yRb and returns transitive property on h_yRb and h_symm h_aRb to conclude yRa (proves if y ∈ [b], then y ∈ [a])
    exact ⟨fun h_yRa => h_trans h_yRa h_aRb, fun h_yRb => h_trans h_yRb (h_symm h_aRb)⟩ }
  { intro h_eq_classes
    rw [← h_eq_classes]
    exact h_refl a }


-- Property 3: Any two equivalence classes are either equal or disjoint - ∀a, b ∈ S, [a] = [b] ∨ [a] ∩[b] = ∅
lemma Property3 {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : ([a]_R = [b]_R) ∨ ([a]_R ∩ [b]_R = ∅) := by
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  by_cases h_aInb : a ∈ [b]_R
  { left
    -- Use Property2 to show equivalence classes are equal
    exact (Property2 R h_equiv a b).mp h_aInb}
  { right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x
    -- If x is in the intersection, then x is in both equivalence classes
    intro h_x_in_intersection
    cases h_x_in_intersection with
    | intro h_xIna h_xInb
    have h_aRb := h_trans (h_symm h_xIna) h_xInb
    exact h_aInb h_aRb
  }
end EquivalenceClasses

/- Notes on the above proof:
- `Set.eq_empty_iff_forall_notMem{α : Type u} {s : Set α} : s = ∅ ↔ ∀ (x : α), x ∉ s`
- s is a Set of type α, and the theorem states that s is empty if and only if for all x of type α, x is not in s
- So when we take right side of above, we get `[a]_R ∩ [b]_R = ∅`
- The intersection of the two equivalence classes is empty if and only if for all x, x is not in the intersection
- We use the backwards direction of Set.eq_empty_iff_forall_notMem to show that if the intersection is empty, then for all x, x is not in the intersection - `∀ (x : A), x ∉ [a]_R ∩ [b]_R`
- We then assume that x is in the intersection of the two equivalence classes and create two cases `x ∈ [a]_R` and `x ∈ [b]_R`
- If x is in the intersection, then x is in both equivalence classes, therefore by transitivity R a b holds i.e. xRa and xRb implies R a b
- This contradicts the assumption that a is not in the equivalence class of b
-/

-- Rewriting property proofs using type class notation
namespace UsingClass

class Equivalence (A : Type _) where
   R : A → A → Prop
   refl : Reflexive R
   symm : Symmetric R
   trans : Transitive R

local infix:50 " ~ " => Equivalence.R

def EquivClass {A : Type _} [Equivalence A] (x : A) : Set A :=
  {y : A | y ~ x}

notation:100 "[" a "]_R" => EquivClass a

-- rewrite using above notation and class
lemma Property1 {A : Type _} [Equivalence A] (a : A) : a ∈ [a]_R := by
  exact Equivalence.refl a

lemma Property2 {A : Type} [Equivalence A] (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
  constructor
  { intro h_aRb
    apply Set.ext
    intro y
    constructor
    { intro h_yRa
      exact Equivalence.trans h_yRa h_aRb }
    { intro h_yRb
      have h_bRa := Equivalence.symm h_aRb
      exact Equivalence.trans h_yRb h_bRa } }
  { intro h_eq_classes
    rw[← h_eq_classes]
    exact Equivalence.refl a }

lemma Property3 {A : Type} [Equivalence A] (a b : A) : ([a]_R = [b]_R) ∨ ([a]_R ∩ [b]_R = ∅) := by
  by_cases h_aInb : a ∈ [b]_R
  { left
    exact (Property2 a b).mp h_aInb}
  { right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x
    intro h_x_in_intersection
    cases h_x_in_intersection with
    | intro h_xIna h_xInb
    have h_aRb := Equivalence.trans (Equivalence.symm h_xIna) h_xInb
    exact h_aInb h_aRb
  }

end UsingClass

-- Rewriting property proofs using Mathlib's Setoid
namespace EqClasses_Setoid
open UsingClass
class Equivalence (A : Sort u) where
   R : A → A → Prop
   refl : Reflexive R
   symm : Symmetric R
   trans : Transitive R

def equiv_class {α : Type _} (R : Setoid α) (a : α) : Set α :=
  { x | R x a }

notation:100 "[" a "]__" R:100 => equiv_class R a

lemma Property1 {α : Type _} (R : Setoid α) (a : α) : a ∈ [a]__R := by
  exact R.refl a

lemma Property2 {α : Type _} (R : Setoid α) (a b : α) : (a ∈ [b]__R) ↔ ([a]__R = [b]__R) := by
  constructor
  { intro h_aRb
    apply Set.ext
    intro y
    constructor
    { intro h_yRa
      exact R.trans h_yRa h_aRb }
    { intro h_yRb
      have h_bRa := R.symm h_aRb
      exact R.trans h_yRb h_bRa } }
  { intro h_eq_classes
    rw[← h_eq_classes]
    exact R.refl a }

lemma Property3 {α : Type _} (R : Setoid α) (a b : α) : ([a]__R = [b]__R) ∨ ([a]__R ∩ [b]__R = ∅) := by
  by_cases h_aInb : a ∈ [b]__R
  { left
    exact (Property2 R a b).mp h_aInb}
  { right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x
    intro h_x_in_intersection
    cases h_x_in_intersection with
    | intro h_xIna h_xInb
    have h_aRb := R.trans (R.symm h_xIna) h_xInb
    exact h_aInb h_aRb
  }
end EqClasses_Setoid
