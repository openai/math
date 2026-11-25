import OAI.LinearAlgebra.FiniteFourier.ConvolutionPacking
import OAI.LinearAlgebra.FiniteFourier.ConvolutionJetCircuitDescent

/-! # Mixed-radix packing into quadratic coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

open scoped Classical

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra S A]
variable {n e r N : ℕ}

/-- Route the operand to its mixed-radix positions in the first scalar coordinate.
Unoccupied positions and the second scalar coordinate use zero readouts. -/
def quadraticPackingCircuit (he : 0 < e) (hr : 0 < r) (hcap : 8*n ≤ e*r*N) :
    Circuit R (Fin n) ((Fin e × Fin r × Fin N) × Fin 2) 0 where
  program := .nil
  output j := if j.2 = 0 then
    if h : ∃ i, packingInputPosition he hr hcap i = j.1 then
      .scaled 1 (.inl h.choose) else .zero
    else .zero

/-- Decoding the routed coordinates gives the power-basis coefficients of the
packed operand after scalar extension. -/
theorem quadraticPackingCircuit_decode (φ : R →+* S) (η : S)
    (b : Module.Basis (Fin e × Fin r × Fin N) S A)
    (he : 0 < e) (hr : 0 < r) (hcap : 8*n ≤ e*r*N) (x : Fin n → R)
    (j : Fin e × Fin r × Fin N) :
    QuadraticDescent.decode φ η ((quadraticPackingCircuit he hr hcap).eval x) j =
      b.repr (packConvolutionInput b he hr hcap (φ ∘ x)) j := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [QuadraticDescent.decode, quadraticPackingCircuit, Circuit.eval, ite_true,
    ite_eq_right h10, Readout.eval, map_zero, mul_zero, add_zero,
    packConvolutionInput, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, Function.comp_apply]
  by_cases h : ∃ i, packingInputPosition he hr hcap i = j
  · rw [dite_eq_left h, Finset.sum_eq_single h.choose]
    · simp [h.choose_spec]
    · intro i _ hi
      have hn : packingInputPosition he hr hcap i ≠ j := fun hj =>
        hi ((packingInputPosition he hr hcap).injective (hj.trans h.choose_spec.symm))
      simp [hn]
    · simp
  · rw [dite_eq_right h, Finset.sum_eq_zero]
    · simp
    · intro i _
      simp [show packingInputPosition he hr hcap i ≠ j from fun H => h ⟨i,H⟩]

end

end FiniteFourier
end LinearAlgebra
end OAI
