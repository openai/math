import OAI.LinearAlgebra.FiniteFourier.CircuitReindex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Two partial transforms on a free rectangle

The source sums over its first coordinate and the transposed destination sums
over its first coordinate. The complementary coordinates on each side encode
the other side's frequency and the common spectator. Thus the intervening map
is a scaled permutation, including when the two sets of representatives differ.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open scoped Classical
variable {K H P S T U : Type*} [CommSemiring K]

/-- A partial transform with fixed second coordinate, in coordinates adapted
to its summation subspace. -/
def endpointPartial (F : Matrix H H K) (S : Type*) : Matrix (H × S) (H × S) K :=
  fun o i => if i.2 = o.2 then F o.1 i.1 else 0

/-- Index change between the transformed source and the transposed destination.
The common spectator is preserved and the two frequency coordinates exchange roles. -/
def endpointBridgeEquiv (s : S ≃ P × U) (t : T ≃ H × U) : P × T ≃ H × S where
  toFun o := ((t o.2).1, s.symm (o.1, (t o.2).2))
  invFun i := ((s i.2).1, t.symm (i.1, (s i.2).2))
  left_inv o := by simp
  right_inv i := by simp

/-- Middle map between the endpoints. Its diagonal includes normalization,
representative changes and the phases of the distinguished digits. -/
def endpointBridge (s : S ≃ P × U) (t : T ≃ H × U) (w : P × T → K) :
    Matrix (P × T) (H × S) K :=
  fun o i => if endpointBridgeEquiv s t o = i then w o else 0

/-- A bridge requires only scaled readouts in the binary linear circuit model. -/
theorem endpointBridge_realizable (s : S ≃ P × U) (t : T ≃ H × U) (w : P × T → K) :
    RealizableAtMost (endpointBridge s t w) 0 := by
  refine ⟨0, le_rfl, ⟨.nil, fun o => .scaled (w o) (.inl (endpointBridgeEquiv s t o))⟩, ?_⟩
  ext o i
  simp [Circuit.matrix, Circuit.eval, Readout.eval, endpointBridge, Pi.single_apply, mul_ite]

/-- The transfer of the two partial transforms and the bridge between them.
The middle map may depend on the query, whereas neither partial transform does. -/
theorem endpointPartial_bridge_partial_apply [Fintype H] [Fintype P] [Fintype S] [Fintype T]
    (F : Matrix H H K) (G : Matrix P P K) (s : S ≃ P × U) (t : T ≃ H × U) (w : P × T → K)
    (o : P × T) (i : H × S) :
    (endpointPartial G T * (endpointBridge s t w * endpointPartial F S)) o i =
      if (s i.2).2 = (t o.2).2 then
        G o.1 (s i.2).1 * (w ((s i.2).1, o.2) * F (t o.2).1 i.1) else 0 := by
  classical
  have inner (v : P × T) :
      (endpointBridge s t w * endpointPartial F S) v i =
        w v * endpointPartial F S (endpointBridgeEquiv s t v) i := by
    simp [Matrix.mul_apply, endpointBridge, ite_mul]
  rw [Matrix.mul_apply]
  simp only [inner, Fintype.sum_prod_type, endpointPartial, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have he (p : P) :
      i.2 = s.symm (p, (t o.2).2) ↔ (s i.2).1 = p ∧ (s i.2).2 = (t o.2).2 := by
    rw [s.eq_symm_apply, Prod.ext_iff]
  simp only [endpointBridgeEquiv, Equiv.coe_fn_mk, he, mul_ite, mul_zero]
  by_cases h : (s i.2).2 = (t o.2).2 <;> simp [h]

end

end FiniteFourier
end LinearAlgebra
end OAI
