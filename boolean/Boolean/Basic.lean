import Mathlib

open Set
open BooleanAlgebra

def seq (n : ℕ) := BooleanAlgebra (Set (Fin n →  ℝ) )

-- #print BooleanAlgebra

variable (s t : Set ℝ)

-- #check (inferInstance : BooleanAlgebra (Set ℝ))

#check inf_compl_eq_bot

example : s ⊓ sᶜ = (⊥ : Set ℝ) := by simpa using (inf_compl_eq_bot s)

universe u

structure DefinableFamily :=
  (definable : ∀ n: ℕ, Set (Set (Fin n → ℝ)))

def IsStrucure (S : DefinableFamily) : Prop :=
  ∀ n : ℕ, /-
    (∀ A : Set (Fin n → ℝ), A ∈ S.definable n →
      (∀ i : Fin n, ∃ U : Set ℝ, U ∈ S.definable 1 ∧
        (∀ x : Fin n → ℝ, x ∈ A → x i ∈ U))) ∧-/
    ((∀ U V : Set (Fin n →  ℝ), U ∈ S.definable n → V ∈ S.definable n → (U ∩ V) ∈ S.definable n) ∧
    (∀ U : Set (Fin n → ℝ), U ∈ S.definable n → (Uᶜ ∈ S.definable n))) → true
