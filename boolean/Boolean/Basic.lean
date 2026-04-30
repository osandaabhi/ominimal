import Mathlib

open Set

def IsFiniteUnionOfPointsAndIntervals (A : Set ℝ) : Prop :=
  ∃ k : ℕ, True

-- An o-minimal structure on `ℝ`.
structure OminStructure where
  S : (n : ℕ) → BooleanSubalgebra (Set (Fin n → ℝ))
  prod_right : ∀ n : ℕ, ∀ A : Set (Fin n → ℝ),
    A ∈ S n →
    {v : Fin (n + 1) → ℝ | (fun i => v (Fin.castSucc i)) ∈ A} ∈ S (n + 1)

  prod_left : ∀ n : ℕ, ∀ A : Set (Fin n → ℝ),
    A ∈ S n →
    {v : Fin (n + 1) → ℝ | (fun i => v (Fin.succ i)) ∈ A} ∈ S (n + 1)

  diagonal : ∀ n : ℕ, ∀ i j : Fin n, i ≠ j →
    {v : Fin n → ℝ | v i = v j} ∈ S n

  projection : ∀ n : ℕ, ∀ A : Set (Fin (n + 1) → ℝ),
    A ∈ S (n + 1) →
    {v : Fin n → ℝ | ∃ x : ℝ, Fin.snoc v x ∈ A} ∈ S n

  singletons : ∀ r : ℝ,
    {v : Fin 1 → ℝ | v 0 = r} ∈ S 1

  order : {v : Fin 2 → ℝ | v 0 < v 1} ∈ S 2

  o_minimal : ∀ A : Set (Fin 1 → ℝ), A ∈ S 1 →
    IsFiniteUnionOfPointsAndIntervals
      {x : ℝ | (fun _ : Fin 1 => x) ∈ A}

namespace OminStructure

-- A subset of `ℝⁿ` is definable in `𝒮`.
def DefinableSet (𝒮 : OminStructure) (n : ℕ)
    (A : Set (Fin n → ℝ)) : Prop :=
  A ∈ 𝒮.S n

-- The graph of a function -
def graph {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {v : Fin (n + m) → ℝ |
    ∃ x : Fin n → ℝ, ∃ y : Fin m → ℝ,
      (∀ i : Fin n, v (Fin.castAdd m i) = x i) ∧
      (∀ j : Fin m, v (Fin.natAdd n j) = y j) ∧
      f x = y}

-- A function is definable if its graph is definable.
def DefinableFunction (𝒮 : OminStructure) {n m : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  𝒮.DefinableSet (n + m) (graph f)

-- Closure under products on the right.
theorem definable_prod_right
    (𝒮 : OminStructure) {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : 𝒮.DefinableSet n A) :
    𝒮.DefinableSet (n + 1)
      {v : Fin (n + 1) → ℝ | (fun i => v (Fin.castSucc i)) ∈ A} :=
  𝒮.prod_right n A hA

-- Closure under products on the left. -
theorem definable_prod_left
    (𝒮 : OminStructure) {n : ℕ} {A : Set (Fin n → ℝ)}
    (hA : 𝒮.DefinableSet n A) :
    𝒮.DefinableSet (n + 1)
      {v : Fin (n + 1) → ℝ | (fun i => v (Fin.succ i)) ∈ A} :=
  𝒮.prod_left n A hA

-- Closure under projection. -
theorem definable_projection
    (𝒮 : OminStructure) {n : ℕ} {A : Set (Fin (n + 1) → ℝ)}
    (hA : 𝒮.DefinableSet (n + 1) A) :
    𝒮.DefinableSet n
      {v : Fin n → ℝ | ∃ x : ℝ, Fin.snoc v x ∈ A} :=
  𝒮.projection n A hA

-- Diagonal sets are definable. -
theorem definable_diagonal
    (𝒮 : OminStructure) {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    𝒮.DefinableSet n {v : Fin n → ℝ | v i = v j} :=
  𝒮.diagonal n i j hij

-- Singletons are definable.
theorem definable_singleton
    (𝒮 : OminStructure) (r : ℝ) :
    𝒮.DefinableSet 1 {v : Fin 1 → ℝ | v 0 = r} :=
  𝒮.singletons r

-- The order relation is definable.
theorem definable_order
    (𝒮 : OminStructure) :
    𝒮.DefinableSet 2 {v : Fin 2 → ℝ | v 0 < v 1} :=
  𝒮.order

-- O-minimality wrapper.
theorem definable_one_dimensional_sets_are_finite_unions
    (𝒮 : OminStructure)
    {A : Set (Fin 1 → ℝ)}
    (hA : 𝒮.DefinableSet 1 A) :
    IsFiniteUnionOfPointsAndIntervals
      {x : ℝ | (fun _ : Fin 1 => x) ∈ A} :=
  𝒮.o_minimal A hA

-- The open interval `(a,b)` encoded as a subset of `Fin 1 → ℝ`.
def openInterval1 (a b : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | a < v 0 ∧ v 0 < b}

-- The closed interval `[a,b]` encoded as a subset of `Fin 1 → ℝ`.
def closedInterval1 (a b : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | a ≤ v 0 ∧ v 0 ≤ b}

-- The ray `(a,∞)` encoded as a subset of `Fin 1 → ℝ`.
def rightRay1 (a : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | a < v 0}

-- The ray `(-∞,b)` encoded as a subset of `Fin 1 → ℝ`.
def leftRay1 (b : ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | v 0 < b}

/-- Definability of open intervals.
theorem definable_open_interval
    (𝒮 : OminStructure) (a b : ℝ) :
    𝒮.DefinableSet 1 (openInterval1 a b) := by
  unfold openInterval1 rightRay1 leftRay1 DefinableSet at *
  change {v : Fin 1 → ℝ | a < v 0 ∧ v 0 < b} ∈ 𝒮.S 1
  exact (𝒮.S 1).inf_mem hRight hLeft -/

theorem definable_open_interval'
    (𝒮 : OminStructure) (a b : ℝ)
    (hRight : 𝒮.DefinableSet 1 (rightRay1 a))
    (hLeft : 𝒮.DefinableSet 1 (leftRay1 b)) :
    𝒮.DefinableSet 1 (openInterval1 a b) := by
  unfold openInterval1 rightRay1 leftRay1 DefinableSet at *
  change {v : Fin 1 → ℝ | a < v 0 ∧ v 0 < b} ∈ 𝒮.S 1
  exact (𝒮.S 1).inf_mem hRight hLeft

-- Definability of right rays.
theorem definable_right_ray
    (𝒮 : OminStructure) (a : ℝ) :
    𝒮.DefinableSet 1 (rightRay1 a) := by
  sorry

-- Definability of left rays.
theorem definable_left_ray
    (𝒮 : OminStructure) (b : ℝ) :
    𝒮.DefinableSet 1 (leftRay1 b) := by
  sorry


def DefinableRealFunction (𝒮 : OminStructure) (f : ℝ → ℝ) : Prop :=
  𝒮.DefinableFunction
    (n := 1) (m := 1)
    (fun v => fun _ : Fin 1 => f (v 0))

def realGraph (f : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {v : Fin 2 → ℝ | f (v 0) = v 1}

theorem definable_realGraph
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    𝒮.DefinableSet 2 (realGraph f) := by
  sorry

def increasingComparison (f : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {v : Fin 2 → ℝ | v 0 < v 1 ∧ f (v 0) < f (v 1)}


def decreasingComparison (f : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {v : Fin 2 → ℝ | v 0 < v 1 ∧ f (v 0) > f (v 1)}

def constantComparison (f : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {v : Fin 2 → ℝ | v 0 < v 1 ∧ f (v 0) = f (v 1)}

theorem definable_increasingComparison
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    𝒮.DefinableSet 2 (increasingComparison f) := by
  sorry

theorem definable_decreasingComparison
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    𝒮.DefinableSet 2 (decreasingComparison f) := by
  sorry

theorem definable_constantComparison
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    𝒮.DefinableSet 2 (constantComparison f) := by
  sorry

def StrictlyIncreasingOnInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x y : ℝ, a < x → x < y → y < b → f x < f y

def StrictlyDecreasingOnInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x y : ℝ, a < x → x < y → y < b → f x > f y

def ConstantOnInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x y : ℝ, a < x → x < b → a < y → y < b → f x = f y

def OminimalMonotoneOnInterval (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  StrictlyIncreasingOnInterval f a b ∨
  StrictlyDecreasingOnInterval f a b ∨
  ConstantOnInterval f a b

def LocallyIncreasingAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ u v : ℝ,
      x - ε < u →
      u < v →
      v < x + ε →
      f u < f v

def LocallyDecreasingAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ u v : ℝ,
      x - ε < u →
      u < v →
      v < x + ε →
      f u > f v

def LocallyConstantAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ u v : ℝ,
      x - ε < u →
      u < x + ε →
      x - ε < v →
      v < x + ε →
      f u = f v

def locallyIncreasingSet (f : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | LocallyIncreasingAt f x}

def locallyDecreasingSet (f : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | LocallyDecreasingAt f x}

def locallyConstantSet (f : ℝ → ℝ) : Set ℝ :=
  {x : ℝ | LocallyConstantAt f x}

def locallyIncreasingSet1 (f : ℝ → ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | LocallyIncreasingAt f (v 0)}

def locallyDecreasingSet1 (f : ℝ → ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | LocallyDecreasingAt f (v 0)}

def locallyConstantSet1 (f : ℝ → ℝ) : Set (Fin 1 → ℝ) :=
  {v : Fin 1 → ℝ | LocallyConstantAt f (v 0)}

theorem definable_locallyIncreasingSet
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    𝒮.DefinableSet 1 (locallyIncreasingSet1 f) := by
  sorry

theorem definable_locallyDecreasingSet
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    𝒮.DefinableSet 1 (locallyDecreasingSet1 f) := by
  sorry

theorem definable_locallyConstantSet
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    𝒮.DefinableSet 1 (locallyConstantSet1 f) := by
  sorry

theorem finite_exceptional_set_for_local_monotonicity
    (𝒮 : OminStructure) {f : ℝ → ℝ}
    (hf : 𝒮.DefinableRealFunction f) :
    ∃ E : Set ℝ,
      E.Finite ∧
      ∀ x : ℝ, x ∉ E →
        LocallyIncreasingAt f x ∨
        LocallyDecreasingAt f x ∨
        LocallyConstantAt f x := by
  sorry

def IsStrictPartition (a b : ℝ) {k : ℕ}
    (pts : Fin (k + 1) → ℝ) : Prop :=
  pts 0 = a ∧
  pts (Fin.last k) = b ∧
  ∀ i : Fin k, pts i.castSucc < pts i.succ

theorem monotonicity_theorem
    (𝒮 : OminStructure)
    (a b : ℝ)
    (hab : a < b)
    (f : ℝ → ℝ)
    (hf : 𝒮.DefinableRealFunction f) :
    ∃ (k : ℕ) (pts : Fin (k + 1) → ℝ),
      IsStrictPartition a b pts ∧
      ∀ i : Fin k,
        OminimalMonotoneOnInterval
          f
          (pts i.castSucc)
          (pts i.succ) := by
  sorry

end OminStructure
