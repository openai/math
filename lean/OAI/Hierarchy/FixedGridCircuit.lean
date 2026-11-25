import OAI.Hierarchy.FixedCutFamilyForcing
import OAI.Hierarchy.CircuitSlotBorder
import OAI.Hierarchy.GridCircuitTransfer

namespace OAI
/-! # Fixed square grids have unbounded border-circuit exponents -/

namespace Hierarchy

open Computability.VPVNP LinearAlgebra.SpectralBooks
open scoped Classical

/-- In a fixed grid every balanced circuit term faces the same lower bound
on the number of cut edge axes. The fixed generator-count coefficient is
absorbed by raising the test exponent by one. -/
theorem fixed_grid_hard (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure F)) : FixedGridCircuitHardness F := by
  classical
  intro k
  let b := (k+3)^2
  let m := 3*b
  let G := SquareGrid.graph m
  let d := Fintype.card G.V
  have bpos : 0<b := by dsimp [b]; positivity
  have side : 2 ≤ m := by dsimp [m]; omega
  have : Nonempty G.E :=
    ⟨Sum.inl ((⟨0,by omega⟩ : Fin m),(⟨0,by omega⟩ : Fin (m-1)))⟩
  obtain ⟨P⟩ := flats (Fintype.card G.E) Fintype.card_pos
  have dsize : d=m^2 := SquareGrid.card_vertices m
  have hd : 2≤d := by rw [dsize,pow_two]; nlinarith
  have wide (U : Finset G.V) (hU : U ∈ CircuitSlot.balancedFamily G.V) :
      b ≤ (G.boundaryEdges U).card := by
    obtain ⟨lo,hi⟩ := (CircuitSlot.mem_balancedFamily U).mp hU
    have hc := Finset.card_add_card_compl U
    change U.card+Uᶜ.card=d at hc
    change d<3*U.card at lo
    change 3*U.card≤2*d at hi
    have cut := SquareGrid.balanced_cut U (by omega) (by omega)
    change 3*b ≤ 3*(G.boundaryEdges U).card at cut
    omega
  have slope : ((k+1:ℕ):ℝ)+1 < Real.sqrt b := by
    dsimp [b]
    push_cast
    rw [Real.sqrt_sq (by positivity)]
    linarith
  obtain ⟨N, hard⟩ := G.fixed_cut_family_hard (AlgebraicClosure F) P (CircuitSlot.balancedFamily G.V)
    b (k+1) wide slope
  refine ⟨m, max N (4*(d+1)), ?_⟩
  intro n hn host
  have pay : 4*(d+1) ≤ n := (le_max_right ..).trans hn
  have hn1 : 0<n := by omega
  have lower := hard n ((le_max_left ..).trans hn) (balancedCircuitTerms d (n^k))
    (G.border_circuit_wire_cut_sums F hd host)
  have upper : balancedCircuitTerms d (n^k) ≤ n^(k+1) := by
    calc
      _ ≤ (4*n^k)*(d+1) := Nat.mul_le_mul_right _ (by
        have := Nat.pow_pos hn1 (n:=k)
        omega)
      _ = n^k*(4*(d+1)) := by ring
      _ ≤ n^k*n := Nat.mul_le_mul_left _ pay
      _ = _ := (pow_succ n k).symm
  exact (Nat.not_lt_of_ge upper) lower

/-- The grid witness supplies the circuit separation without the uniform
graph-classification implication. -/
theorem grid_witness_of_flats (F : Type*) [Field F]
    (flats : AllHomogeneousFlats (AlgebraicClosure (⊥ : Subfield F))) :
    IsVNP (contractionFamily F SquareGrid.graph) ∧
    ¬ IsVP (contractionFamily F SquareGrid.graph) ∧
    ¬ GraphFamily.PolynomialBorderCircuit SquareGrid.graph F :=
  grid_witness_of_fixed F (fixed_grid_hard (⊥ : Subfield F) flats)

end Hierarchy

end OAI
