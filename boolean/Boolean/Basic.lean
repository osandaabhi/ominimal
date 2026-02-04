import Mathlib

-- define a boolean alegbra

inductive BooleanAlgebra where
  | top : BooleanAlgebra
  | bottom : BooleanAlgebra
  | union : BooleanAlgebra → BooleanAlgebra → BooleanAlgebra
  | intersection : BooleanAlgebra → BooleanAlgebra → BooleanAlgebra
  | complement : BooleanAlgebra → BooleanAlgebra


open BooleanAlgebra

#check top
