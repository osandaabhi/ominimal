/-
import Mathlib

--definition of a group structure
namespace group
  variable (G : Type)
  variable (f : G → G → G)

  structure GroupStruct :=
    (mul_assoc : ∀ a b c : G, f (f a b) c = f a (f b c))
    (one : G)
    (one_mul : ∀ a : G, f one a = a)
    (mul_one : ∀ a : G, f a one = a)
    (inv : G → G)
    (mul_left_inv : ∀ a : G, f (inv a) a = one)
end group


open group

example {G : Type} (f : G → G → G) (inv : G → G) (one : G) (a:G) :
  f a (inv a) = one := by exact sorry

open Nat

example (a b : ℕ) : a + b = b + a := by sorry

-/
