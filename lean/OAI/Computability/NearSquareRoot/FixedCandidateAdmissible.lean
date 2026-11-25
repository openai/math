import OAI.Computability.NearSquareRoot.FixedCandidateArrays

/-! # The admitted working domain of each physical transform call -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Bits DigitPacking FixedPoint ResidueFourier ProductRecovery
noncomputable section

section Prefix

variable {X : Type} [Fintype X] {k : ℕ}

/-- The norm guard needed by the numerical action holds before every physical stage. -/
theorem prefix_workingRange (p : Layers X k) {U} (hp : p.Approximates U) (hk : 1 ≤ k)
    (r : X → Record k) (hr : ‖recordArray r‖ ≤ (2:ℝ)^(12*k)) {j} (hj : j ≤ p.count) :
    ‖recordArray (p.run r j)‖ ≤ (2:ℝ)^(13*k) := by
  let v j := recordArray (p.run r j)
  exact (transformLayerPrecision p.ideal v hk hp.depth hr (fun t ht => hp.localError t ht _) hj).2

end Prefix

variable {n : ℕ} (h : Directory n)

private theorem input_bound (hn : 2 ≤ n) (z : Word) :
    letI := BoxFin.modulus_neZero h
    letI : NeZero (directoryVolume (addressBits n)) := ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
    ‖residueOperand (BoxFin.modulus (box n)) (BoxFin.padding (box n)) (BoxFin.pairwise h) n z‖ ≤
      (2:ℝ)^(4*addressBits n) := by
  let _ := BoxFin.modulus_neZero h
  let _ : NeZero (directoryVolume (addressBits n)) := ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  exact paddedDigit_norm _ _ hn (CRT.scaled _ (BoxFin.pairwise h)) _ (unpackDigits_lt _ _ z) (BoxFin.card_padded h)

/-- The encoded, zero-filled original operands lie inside the transform admission range. -/
theorem input_admissible (hn : 2 ≤ n) (z : Word) : Admissible h (route h (input h z)) := by
  let _ := BoxFin.modulus_neZero h
  let _ : NeZero (directoryVolume (addressBits n)) := ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  change ‖recordArray ((physicalInput h z ∘ (BoxFin.crtSlotPerm h).symm) ∘ BoxFin.recordIndex h)‖ ≤ _
  rw [route_physicalInput, decode_inputRecords _ _ _ hn]
  exact (input_bound h hn z).trans (pow_le_pow_right₀ (by norm_num) (by omega))

/-- The actual rounded pointwise product, after both forward executions, also
fits the initial norm range of the inverse command. -/
theorem spectral_admissible (hn : 2 ≤ n) (p : Plan h) (x y : Word) :
    let fw z := eval h p.forward (route h (input h z))
    Admissible h (pointwise (fw x) (fw y)) := by
  let _ := BoxFin.modulus_neZero h
  let _ : NeZero (directoryVolume (addressBits n)) := ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  let fw z := eval h p.forward (route h (input h z))
  change ‖recordArray (pointwise (fw x) (fw y) ∘ index h)‖ ≤ _
  rw [pointwise_order]
  dsimp only [fw]
  rw [eval_comp_index, eval_comp_index, routed_input, routed_input]
  have hk : 1 ≤ addressBits n := by have := width_pos hn; have := width_le_twice_addressBits hn; omega
  apply productArray_input_bound hk (BoxFin.card_padded h).le (ideal h)
    (residueOperand _ (BoxFin.padding (box n)) (BoxFin.pairwise h) n x)
    (residueOperand _ (BoxFin.padding (box n)) (BoxFin.pairwise h) n y) _ _
    (input_bound h hn x) (input_bound h hn y)
  · exact forwardInput_error _ _ _ hn (BoxFin.card_padded h) p.forward p.fwd_ok x
  · exact forwardInput_error _ _ _ hn (BoxFin.card_padded h) p.forward p.fwd_ok y

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
