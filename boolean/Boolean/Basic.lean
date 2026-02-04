import Mathlib

open Set
open BooleanAlgebra

def seq (n : ℕ) := BooleanAlgebra (Set (Fin n →  ℝ) )


#print BooleanAlgebra

example s ⊓ sᶜ = (⊥ : Set ℝ) := by
  exact inf_compl_eq_bot
