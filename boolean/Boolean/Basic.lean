import Mathlib

open Set PFun Equiv

#check Dom


variable (n m : ℕ)
def R (n : ℕ) := Fin n → ℝ

#check Fin n → ℝ

-- A sequence of Boolean algebras of subsets of ℝⁿ, one for each n.
-- S n is a collection of subsets of (Fin n → ℝ).
def BoolAlgSeq : Type := (n : ℕ) → Set (Set (R n))

--example {s} : s ⊓ sᶜ = (⊥ : Set ℝ) := by simp only [inf_compl_eq_bot]

-- Projection onto the first component
def proj_fst {n : ℕ} (A : Set (R (n + 1))) : Set (R n) :=
  {x | ∃ y : ℝ, (fun i => Fin.lastCases y x i) ∈ A}

-- Each S n should be a Boolean subalgebra (closed under ∪, ∩, ᶜ)
def IsBoolAlg {n : ℕ} (Sn : Set (Set (R n))) : Prop :=
  ∅ ∈ Sn ∧ univ ∈ Sn ∧
  (∀ A ∈ Sn, Aᶜ ∈ Sn) ∧
  (∀ A ∈ Sn, ∀ B ∈ Sn, A ∪ B ∈ Sn) ∧
  (∀ A ∈ Sn, ∀ B ∈ Sn, A ∩ B ∈ Sn)

-- Cylinder: embed A ⊆ ℝⁿ into ℝⁿ⁺¹ by adding a free last coordinate
def cylinder {n : ℕ} (A : Set (R n)) : Set (R (n + 1)) :=
  {v | (fun i : Fin n => v (Fin.castSucc i)) ∈ A}

-- Diagonal set: {v ∈ ℝⁿ | v i = v j}
def diagonal {n : ℕ} (i j : Fin n) : Set (R n) :=
  {v | v i = v j}

-- O-minimal structure definition
def OminStructure (S : BoolAlgSeq) : Prop :=
  -- Each S n is a Boolean algebra
  (∀ n : ℕ, IsBoolAlg (S n)) ∧
  -- Closed under cylinders: A ∈ S n → cylinder A ∈ S (n+1)
  (∀ n : ℕ, ∀ A ∈ S n, cylinder A ∈ S (n + 1)) ∧
  -- Diagonal sets are definable
  (∀ n : ℕ, ∀ i j : Fin n, diagonal i j ∈ S n) ∧
  -- Closed under projection
  (∀ n : ℕ, ∀ A ∈ S (n + 1), proj_fst A ∈ S n) ∧
  -- Singletons are definable in S 1
  (∀ r : ℝ, {v : (R 1) | v 0 = r} ∈ S 1) ∧
  -- The order relation is definable in S 2
  ({v : Fin 2 → ℝ | v 0 < v 1} ∈ S 2) ∧
  -- S 1 consists only of finite unions of intervals and points
  (∀ A ∈ S 1, ∃ (intervals : Finset (ℝ × ℝ)), ∃ (points : Finset ℝ),
    A = (⋃ i ∈ intervals, {v : Fin 1 → ℝ | v 0 ∈ Set.Ioo i.1 i.2}) ∪
    (⋃ p ∈ points, {v : Fin 1 → ℝ | v 0 = p}))

--def graph {α β} (f : α → β) : Set (α × β) :=
--{p | f p.1 = p.2}

--def dom {α β} (f : α → β) : Set α :=
--{x | ∃ y, (x,y) ∈ graph f}

-- Graph of a function
def graph (f : (R m) → (R n)) : Set (R (m + n)) :=
{v : (R (m + n)) | ∃ x : (R m), v = Fin.append x (f x)}

-- Graph of a restricted function
def resgraph (f : (R m) → (R n)) (A : Set (R m)) := graph (PFun.res f A)

variable (f : (R m) → (R n)) (A : Set (R m))

#check graph (PFun.res f A)

def producteq (m n : ℕ) : R (m + n) ≃ (R m × R n) where
  toFun := by
    intro f
    exact
      (fun i => f (Fin.castAdd n i),
       fun j => f (Fin.natAdd m j))
  invFun := by
    intro p x
    exact
      Fin.addCases p.1 p.2 x
  left_inv := by
    intro f
    funext x
    simp [Fin.addCases]
  right_inv := by
    intro p
    rcases p with ⟨fm, fn⟩
    simp [Fin.addCases]

#check (R (m + n))
#check ((R m) × (R n))

-- def setProducteq (m n : ℕ) : Set (R (m + n)) ≃ Set (R m × R n) := Equiv.setCongr (producteq m n)
-- def setProducteq (m n : ℕ) : Set (R (m + n)) ≃ Set (R m × R n) where
--   toFun := fun S => {p | (producteq m n).symm p ∈ S}
--   invFun := fun T => {x | producteq m n x ∈ T}
--   left_inv := by
--     intro S
--     ext x
--     simp
--   right_inv := by
--     intro T
--     ext p
--     simp

variable (T : Set (R m × R n))
#check {x | (producteq m n).toFun x ∈ T}

def pullBackSet (m n : ℕ) (T : Set (R m × R n)) : Set (R (m + n)) :=
  {x | (producteq m n).toFun x ∈ T}

variable (f : (R m) → (R n)) (A : Set (R m))
#check pullBackSet m n (resgraph n m f A)

-- Definable sets
def definableset (n : ℕ) (A : Set (R n)) (S : BoolAlgSeq) : Prop :=
A ∈ S n

--Domain of a function
def dom (f : (R m) →. (R n)) : Set (R m) := Dom f

-- Definable funtions
def definablefunction
  (f : (R m) → (R n)) (A : Set (R m)) (S : BoolAlgSeq) : Prop :=
    definableset (m + n) (pullBackSet m n (resgraph n m f A)) S

--f definable → dom (f) definable
theorem definablf_definabledom : (definablefunction n m f A S) → (definableset (dom f) S) := sorry


section

variable (a b : ℝ)
variable (f : Set.Ioo a b → ℝ)

--Key theorem 1 : Monotonicity Theorem
--theorem monotonicity_theorem : (∀ x y : Set.Ioo a b, ∃ Finset Set.Ioo a b,  )
end
