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

-- Property 1: Every element belongs to its own equivalence class
-- We need to show that `a` is in the set {y : A | R y a} as in, that R a a holds which the h_reflexive assumption gives us
lemma EquivalenceClass_Property1 {A : Type} (R : BinRel A) (h_reflexive : ∀ x : A, R x x) (a : A) : a ∈ [a]_R := by
  exact h_reflexive a

-- Property 2: ∀a, b ∈ S, aRb if and only if [a] = [b]
lemma EquivalenceClass_Property2 {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  constructor -- removes bidirectional implication and allows us to prove both directions separately
  intro h_aRb -- assume aRb
  apply Set.ext -- remove the set equality and turn into a function that takes an element y and returns a proposition
  intro y
  constructor
  { intro h_yRa -- Assume R y a
    exact h_trans h_yRa h_aRb } -- use transitivity to show R y b
  { intro h_yRb -- Assume R y b
    have h_bRa := h_symm h_aRb -- use symmetry to get R b a
    exact h_trans h_yRb (h_bRa) } -- use transitivity to show R y a
  intro h_eq_classes -- assume [a]_R = [b]_R
  exact h_eq_classes ▸ h_refl a -- ▸ operator is used for substitution and rewrites goal using equality h_eq_classes

-- Alternative proof using `rw` tactic
lemma EquivalenceClass_Property2' {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
  unfold EquivClass
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  -- Forward direction
  constructor
  { intro h_aRb -- Assume aRb
    apply Set.ext
    intro y
    constructor
    { intro h_yRa -- Assume yRa
      exact h_trans h_yRa h_aRb } -- Use transitivity to show yRb
    { intro h_yRb -- Assume yRb
      have h_bRa := h_symm h_aRb -- Use symmetry to show bRa
      exact h_trans h_yRb h_bRa } } -- Use transitivity to show yRa
  -- Backward direction
  { intro h_eq_classes -- Assume [a]_R = [b]_R
    rw[← h_eq_classes]
    exact h_refl a }

-- Alternative proof using lambda functions
lemma EquivalenceClass_Property2'' {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
  unfold EquivClass
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  constructor
  -- Forward direction: If a ∈ [b], then [a] = [b]
  { intro h_aRb
    apply Set.ext
    intro y
    -- 1st Lambda function taking assumption h_yRa and returns transitive property on h_yRa and h_aRb to conclude R y b (proves if y ∈ [a], then y ∈ [b])
    -- 2nd lambda func takes assumption yRb and returns transitive property on h_yRb and h_symm h_aRb (bRa) to conclude R y a (proves if y ∈ [b], then y ∈ [a])
    exact ⟨fun h_yRa => h_trans h_yRa h_aRb, fun h_yRb => h_trans h_yRb (h_symm h_aRb)⟩ }
  -- Backward direction: If [a] = [b], then a ∈ [b]
  { intro h_eq_classes
    rw [← h_eq_classes]
    exact h_refl a }


-- Property 3: Any two equivalence classes are either equal or disjoint - ∀a, b ∈ S, [a] = [b] ∨ [a] ∩[b] = ∅
lemma EquivalenceClass_Property3 {A : Type} (R : BinRel A) (h_equiv : EquivRel R) (a b : A) : ([a]_R = [b]_R) ∨ ([a]_R ∩ [b]_R = ∅) := by
  have h_refl := h_equiv.1
  have h_symm := h_equiv.2.1
  have h_trans := h_equiv.2.2
  by_cases h_aInb : a ∈ [b]_R
  { left
    -- Use EquivalenceClass_Property2 to show that the equivalence classes are equal - .mp applies forward direction of ↔
    exact (EquivalenceClass_Property2 R h_equiv a b).mp h_aInb}
  { right
    apply Set.eq_empty_iff_forall_notMem.mpr -- Use the backwards direction of Set.eq_empty_iff_forall_notMem
    intro x
    -- If x is in the intersection, then x is in both equivalence classes, therefore by transitivity R a b holds
    intro h_x_in_intersection
    cases h_x_in_intersection with
    | intro h_xIna h_xInb
    have h_aRb := h_trans (h_symm h_xIna) h_xInb
    -- But this contradicts the assumption that a is not in the equivalence class of b
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
namespace ClassNotation

class Equivalence (A : Type u) where
   R : A → A → Prop
   refl : Reflexive R
   symm : Symmetric R
   trans : Transitive R

local infix:50 " ~ " => Equivalence.R

def EquivClass {A : Type} [Equivalence A] (x : A) : Set A :=
  {y : A | y ~ x}

notation:100 "[" a "]_R" => EquivClass a

-- rewrite using above notation and class
lemma EquivalenceClass_Property1 {A : Type} [Equivalence A] (a : A) : a ∈ [a]_R := by
  exact Equivalence.refl a

lemma EquivalenceClass_Property2 {A : Type} [Equivalence A] (a b : A) : (a ∈ [b]_R) ↔ ([a]_R = [b]_R) := by
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

lemma EquivalenceClass_Property3 {A : Type} [Equivalence A] (a b : A) : ([a]_R = [b]_R) ∨ ([a]_R ∩ [b]_R = ∅) := by
  by_cases h_aInb : a ∈ [b]_R
  { left
    exact (EquivalenceClass_Property2 a b).mp h_aInb}
  { right
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x
    intro h_x_in_intersection
    cases h_x_in_intersection with
    | intro h_xIna h_xInb
    have h_aRb := Equivalence.trans (Equivalence.symm h_xIna) h_xInb
    exact h_aInb h_aRb
  }

end ClassNotation
