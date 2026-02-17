import Mathlib
set_option linter.style.longLine false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

open Set
open BooleanAlgebra

def BoolAlgSeq : Type := BooleanAlgebra (ℕ → Set ℝ)

--example {s} : s ⊓ sᶜ = (⊥ : Set ℝ) := by simp only [inf_compl_eq_bot]

-- structure DefinableFamily :=
--   (definable : ∀ n: ℕ, Set (Set (Fin n → ℝ)))
variable (S : Set (α × β))
def proj_fst : Set α := {x | ∃ y, (x, y) ∈ S}

def OminStrucure (S : (ℕ → Set ℝ)) : Prop :=
  IsBooleanAlgebra S ∧
  ∀ n : ℕ, S n = Set (Set (Fin n → ℝ)) ∧
  A ∈ S n → prod A ℝ ∈ S (n + 1) ∧
  A ∈ S n → prod ℝ A ∈ S (n + 1) ∧
  ∀ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ n {v : Vector ℝ n | v.get i = v.get j} ∈ S n ∧
  A ∈ S (n+1) → proj_fst A ∈ S n ∧
  ∀ r : ℝ, {r} ∈ S 1 ∧
  {v : Vector ℝ 2 | v.get 0 < v.get 1} ∈ S 2

def definableFunction {n m : ℕ} :  Set (Set (Fin n → ℝ)) → Set (Set (Fin m → ℝ)) := sorry


section

variable (a b : ℝ)
variable (f : Set.Ioo a b → ℝ)

--theorem monotonicity_theorem : (∀ x y : Set.Ioo a b, x ⊆ y → f x ≤ f y) ∨ (∀ x y : Set.Ioo a b, x ⊆ y → f x ≥ f y) := sorry
end