import OAI.Computability.VPVNP.RankQueryStack
import Mathlib.Tactic.DeriveFintype

/-!
# Executing power-entry queries on a scalar stack

Each product in a nontrivial power has one intermediate matrix index and
one degree split. The machine obtains both from its single loop counter by
division and remainder. Exponents and degrees in a saved query are bounded
by their initial limits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

variable {Q R : Type*} [Semiring R]

/-- The two recursive requests at each valid product index of a composite node. -/
inductive Node (Q R : Type*) where
  | leaf (r : R)
  | branch (count : ℕ) (children : Fin count → Q × Q)

/-- The matrix-index and degree loops share a single mixed-radix counter. -/
def Node.box (n m : ℕ) (children : Fin n → Fin m → Q × Q) : Node Q R :=
  .branch (n*m) fun k =>
    let ij := finProdFinEquiv.symm k
    children ij.1 ij.2

namespace Node

/-- Evaluate a leaf as its scalar and a branch as the sum of the products of its paired child
values. -/
def value (v : Q → R) : Node Q R → R
  | .leaf r => r
  | .branch _ f => ∑ i, v (f i).1 * v (f i).2

theorem value_box (v : Q → R) (n m : ℕ) (f : Fin n → Fin m → Q × Q) :
    (box n m f).value v = ∑ i, ∑ j, v (f i j).1 * v (f i j).2 := by
  simp only [box, value]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]

/-- Describe a node by returning its scalar if it is a leaf or its number of product terms if
it branches. -/
def describe : Node Q R → Sum R ℕ
  | .leaf r => .inl r
  | .branch t _ => .inr t

/-- Retrieve the two children of a product term, returning the fallback pair for a leaf or an
out-of-range index. -/
def children (fallback : Q) : Node Q R → ℕ → Q × Q
  | .branch t f, k => if h : k < t then f ⟨k,h⟩ else (fallback,fallback)
  | .leaf _, _ => (fallback,fallback)

/-- Turn a family of query nodes into a stack program with descriptor, left-child, and
right-child operations. -/
def program (nodes : Q → Node Q R) : Program Q R where
  describe q := (nodes q).describe
  left q k := ((nodes q).children q k).1
  right q k := ((nodes q).children q k).2

theorem realizes {nodes : Q → Node Q R} {v : Q → R}
    (h : ∀ q, v q = (nodes q).value v) : (program nodes).Realizes v := by
  intro q
  rw [h q]
  simp only [program]
  cases nodes q with
  | leaf => rfl
  | branch t f =>
    simp only [describe, value]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [children, k.isLt, dite_eq_left]

end Node

/-- The bounded integer registers of one power request. -/
structure PowerKey (n H Z : ℕ) where
  /-- Exponent of the matrix power, bounded by `H`. -/
  exponent : Fin (H + 1)
  /-- Row index of the matrix-power entry whose coefficient is requested. -/
  row : Fin n
  /-- Column index of the matrix-power entry whose coefficient is requested. -/
  col : Fin n
  /-- Degree of the requested polynomial coefficient, bounded by `Z`. -/
  degree : Fin (Z + 1)
  deriving DecidableEq, Fintype

variable {n H Z : ℕ}

namespace PowerKey

/-- Number of balanced exponent splits needed for this power query, bounded by the ceiling of
its base-two logarithm. -/
def depth (q : PowerKey n H Z) := Nat.clog 2 q.exponent.val

/-- Requested coefficient of the specified row and column of the matrix power. -/
def value (entry : Fin n → Fin n → ℕ → R) (q : PowerKey n H Z) : R :=
  powerEntryCoeff entry q.exponent q.row q.col q.degree

/-- Each child holds the lower or upper half of the exponent. -/
def split (q : PowerKey n H Z) (j : Fin n) (d : Fin (q.degree.val + 1)) :
    PowerKey n H Z × PowerKey n H Z :=
  let h := q.exponent.val
  (⟨⟨h / 2, by have := q.exponent.isLt; dsimp [h]; omega⟩, q.row, j,
      ⟨d.val, by have := d.isLt; have := q.degree.isLt; omega⟩⟩,
   ⟨⟨h - h / 2, by have := q.exponent.isLt; dsimp [h]; omega⟩, j, q.col,
      ⟨q.degree.val - d.val, by have := q.degree.isLt; omega⟩⟩)

/-- Describe a power query using the identity matrix at exponent zero, an entry read at
exponent one, and paired subqueries at larger exponents. -/
def node (entry : Fin n → Fin n → ℕ → R) (q : PowerKey n H Z) : Node (PowerKey n H Z) R :=
  if q.exponent.val = 0 then .leaf (if q.row = q.col ∧ q.degree.val = 0 then 1 else 0)
  else if q.exponent.val = 1 then .leaf (entry q.row q.col q.degree)
  else Node.box n (q.degree.val + 1) q.split

theorem value_node (entry : Fin n → Fin n → ℕ → R) (q : PowerKey n H Z) :
    q.value entry = (q.node entry).value (value entry) := by
  rw [value, powerEntryCoeff, node]
  split_ifs <;> try rfl
  rw [Node.value_box]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- Stack program for extracting coefficients of bounded matrix powers by balanced exponent
splitting. -/
def program (entry : Fin n → Fin n → ℕ → R) : Program (PowerKey n H Z) R :=
  Node.program (node entry)

theorem realizes (entry : Fin n → Fin n → ℕ → R) :
    (program (H := H) (Z := Z) entry).Realizes (value entry) :=
  Node.realizes (value_node entry)

theorem descends (entry : Fin n → Fin n → ℕ → R) :
    (program (H := H) (Z := Z) entry).Descends depth := by
  intro q t ht k hk
  change (q.node entry).describe = Sum.inr t at ht
  by_cases h0 : q.exponent.val = 0
  · simp [node, h0, Node.describe] at ht
  by_cases h1 : q.exponent.val = 1
  · simp [node, h1, Node.describe] at ht
  have ht' : n * (q.degree.val + 1) = t := by simpa [node, h0, h1, Node.box, Node.describe] using ht
  subst t
  have hh : 1 < q.exponent.val := by omega
  simp only [program, Node.program, node, ite_eq_right h0, ite_eq_right h1, Node.box, Node.children, dite_eq_left hk, split, depth]
  exact powerQuery_halves hh

theorem arity (entry : Fin n → Fin n → ℕ → R) :
    (program (H := H) (Z := Z) entry).ArityLE (n * (Z + 1)) := by
  intro q t ht
  change (q.node entry).describe = Sum.inr t at ht
  unfold node at ht
  split_ifs at ht <;> simp [Node.describe, Node.box] at ht
  rw [← ht]
  exact Nat.mul_le_mul_left _ q.degree.isLt

/-- Every intermediate continuation has at most `⌈log₂ h⌉` frames. The run
returns the actual scalar coefficient of the polynomial matrix power. -/
theorem run (M : Matrix (Fin n) (Fin n) (Polynomial R)) (entry : Fin n → Fin n → ℕ → R)
    (he : ∀ i j z, entry i j z = (M i j).coeff z) (q : PowerKey n H Z) :
    ∃ t ≤ (5 + 6 * (n * (Z + 1))) ^ (q.depth + 1),
      (program entry).Runs q.depth t (.enter q, [])
        (.returned (((M ^ q.exponent.val) q.row q.col).coeff q.degree.val), []) := by
  have h := Program.run_bounded (program entry) (value entry) depth _ (realizes entry)
    (descends entry) (arity entry) q.depth q le_rfl []
  simpa only [List.length_nil, Nat.zero_add, value, powerEntryCoeff_correct M entry he] using h

end PowerKey

end RankQuery.Stack

end VPVNP
end Computability
end OAI
