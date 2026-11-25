import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Pi

/-! # The bit-wire grid for a bipartite independent-set polynomial

Each crossing propagates both line bits and, at an edge, forbids the occupied
pair. Summing the network over every wire segment gives the weighted
independent-set enumerator over any commutative semiring.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace IndependentSetGrid

open scoped BigOperators Classical

variable {m n : ℕ} {R : Type*} [CommSemiring R]

/-- One occupation bit for each of the two vertex classes. -/
abbrev Bits (m n : ℕ) := (Fin m → Bool) × (Fin n → Bool)

/-- Horizontal and vertical segment labels. Each line has one more segment than crossings. -/
abbrev Wires (m n : ℕ) :=
  (Fin m → Fin (n + 1) → Bool) × (Fin n → Fin (m + 1) → Bool)

/-- The selected vertices contain no edge. -/
def Independent (E : Fin m → Fin n → Prop) (b : Bits m n) : Prop :=
  ∀ i j, E i j → b.1 i = true → b.2 j ≠ true

/-- The local table in left, top, right, bottom order. -/
def crossing (edge : Prop) (l t r b : Bool) : R :=
  if l = r ∧ t = b ∧ (edge → l = true → t ≠ true) then 1 else 0

/-- Contraction with arbitrary unary tables at both ends of every line. -/
def contraction (E : Fin m → Fin n → Prop)
    (left right : Fin m → Bool → R) (top bottom : Fin n → Bool → R) : R :=
  ∑ w : Wires m n,
    ((∏ i, left i (w.1 i 0) * right i (w.1 i (Fin.last n))) *
      ∏ j, top j (w.2 j 0) * bottom j (w.2 j (Fin.last m))) *
    ∏ p : Fin m × Fin n, crossing (E p.1 p.2)
      (w.1 p.1 p.2.castSucc) (w.2 p.2 p.1.castSucc) (w.1 p.1 p.2.succ) (w.2 p.2 p.1.succ)

/-- The independent-set generating sum with a unary weight at each vertex. -/
def generatingSum (E : Fin m → Fin n → Prop)
    (row : Fin m → Bool → R) (col : Fin n → Bool → R) : R :=
  ∑ b : Bits m n, if Independent E b then
    (∏ i, row i (b.1 i)) * ∏ j, col j (b.2 j) else 0

private def fill (b : Bits m n) : Wires m n := (fun i _ => b.1 i, fun j _ => b.2 j)

private def entrance (w : Wires m n) : Bits m n := (fun i => w.1 i 0, fun j => w.2 j 0)

private theorem constant_of_adjacent {k : ℕ} (x : Fin (k + 1) → Bool)
    (h : ∀ t : Fin k, x t.castSucc = x t.succ) (t : Fin (k + 1)) : x 0 = x t :=
  Fin.inductionOn t rfl fun j ih => ih.trans (h j)

/-- Contracting the crossings enforces a single bit on each row and column.
The two endpoint weights multiply on each occupied or unoccupied line. -/
theorem contraction_eq_generatingSum (E : Fin m → Fin n → Prop)
    (left right : Fin m → Bool → R) (top bottom : Fin n → Bool → R) :
    contraction E left right top bottom =
      generatingSum E (fun i b => left i b * right i b) (fun j b => top j b * bottom j b) := by
  classical
  unfold contraction generatingSum
  symm
  apply Fintype.sum_of_injective fill
  · exact Function.LeftInverse.injective (g := entrance) (fun _ => rfl)
  · intro w hw
    have hbad : ¬(∀ (i : Fin m) (j : Fin n),
        w.1 i j.castSucc = w.1 i j.succ ∧ w.2 j i.castSucc = w.2 j i.succ ∧
        (E i j → w.1 i j.castSucc = true → w.2 j i.castSucc ≠ true)) := by
      intro h
      apply hw
      refine ⟨entrance w, Prod.ext ?_ ?_⟩
      · funext i j
        exact constant_of_adjacent (w.1 i) (fun t => (h i t).1) j
      · funext j i
        exact constant_of_adjacent (w.2 j) (fun t => (h t j).2.1) i
    simp only [crossing, Fintype.prod_boole, Prod.forall, hbad, ite_false, mul_zero]
  · intro b
    simp only [crossing, fill, eq_self, true_and, Fintype.prod_boole, Prod.forall]
    unfold Independent
    split_ifs <;> simp

/-- The homogeneous bipartite independent-set polynomial has two variable weights
per graph vertex. -/
def polynomial (E : Fin m → Fin n → Prop) : MvPolynomial ((Fin m ⊕ Fin n) × Bool) R :=
  generatingSum E (fun i b => MvPolynomial.X (Sum.inl i, b))
    (fun j b => MvPolynomial.X (Sum.inr j, b))

/-- With variable entrance tables and all-one exits the grid computes the paper's
polynomial over every coefficient semiring. -/
theorem contraction_eq_polynomial (E : Fin m → Fin n → Prop) :
    contraction E (fun i b => MvPolynomial.X (Sum.inl i, b)) (fun _ _ => 1)
      (fun j b => MvPolynomial.X (Sum.inr j, b)) (fun _ _ => 1) =
      polynomial (R := R) E := by
  simp only [contraction_eq_generatingSum, mul_one, polynomial]

end IndependentSetGrid

end

end SpectralBooks
end LinearAlgebra
end OAI
