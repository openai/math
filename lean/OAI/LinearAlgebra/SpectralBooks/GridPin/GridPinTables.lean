import OAI.LinearAlgebra.SpectralBooks.GridPin.GridPinGeometry
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGrid.IndependentSetGrid

/-! # Local entries of the independent-set grid -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace GridPin

open scoped BigOperators

variable {m n : ℕ} {R : Type*} [CommSemiring R]

/-- The horizontal and vertical wire labels, reindexed by oriented edges. -/
def assignments : IndependentSetGrid.Wires m n ≃ (Edge m n → Bool) where
  toFun w := Sum.elim (Function.uncurry w.1) (Function.uncurry w.2)
  invFun a := (fun i k => a (hor i k), fun j k => a (ver j k))
  left_inv _ := rfl
  right_inv a := funext fun e => by rcases e with ⟨i,k⟩ | ⟨j,k⟩ <;> rfl

/-- Variable tables at the entrances, all-one exits, and crossover
tables testing graph edges at the intersections. -/
def entry (E : Fin m → Fin n → Prop) (left : Fin m → Bool → R) (top : Fin n → Bool → R) :
    (v : Vertex m n) → (Fin (arity v) → Bool) → R
  | .inl (i,false), x => left i (x 0)
  | .inl (_,true), _ => 1
  | .inr (.inl (j,false)), x => top j (x 0)
  | .inr (.inl (_,true)), _ => 1
  | .inr (.inr (i,j)), x => IndependentSetGrid.crossing (E i j) (x 0) (x 1) (x 2) (x 3)

def table (E : Fin m → Fin n → Prop) (left : Fin m → Bool → R) (top : Fin n → Bool → R)
    (v : Vertex m n) (a : (graph m n).Port v → Bool) : R :=
  entry E left top v (fun r => a (ports v r))

/-- The literal port-graph contraction equals the segment-indexed grid sum. -/
theorem contraction_eq_grid (E : Fin m → Fin n → Prop)
    (left : Fin m → Bool → R) (top : Fin n → Bool → R) :
    (graph m n).contraction (A := fun _ => Bool) (table E left top) =
      IndependentSetGrid.contraction E left (fun _ _ => 1) top (fun _ _ => 1) := by
  classical
  unfold PortGraph.contraction IndependentSetGrid.contraction
  symm
  let : DecidableEq (Edge m n) := fun _ _ => Classical.propDecidable _
  refine Fintype.sum_equiv (assignments (m:=m) (n:=n)) _ _ ?_
  intro w
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool, table,
    entry, mul_one, one_mul, PortGraph.atVertex, ports, Equiv.ofBijective_apply,
    dart, assignments,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  ac_rfl

theorem contraction_eq_polynomial (E : Fin m → Fin n → Prop) :
    (graph m n).contraction (A := fun _ => Bool)
      (table E (fun i b => MvPolynomial.X (Sum.inl i,b)) (fun j b => MvPolynomial.X (Sum.inr j,b))) =
    IndependentSetGrid.polynomial (R := R) E :=
  (contraction_eq_grid _ _ _).trans (IndependentSetGrid.contraction_eq_polynomial _)

end GridPin

end

end SpectralBooks
end LinearAlgebra
end OAI
