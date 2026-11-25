import OAI.LinearAlgebra.FiniteFourier.AtTwoCost.AtTwoCost
import OAI.LinearAlgebra.FiniteFourier.DyadicCoefficientTower.DyadicPrimeWordPacking
import OAI.LinearAlgebra.FiniteFourier.DyadicWordTransport
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.JetOccupiedGridCircuit

/-! # Tensor compilation of the dyadic prime-axis changes of basis

Each prime of the selected list has a square physical register array of length
`p`. The forward and backward changes may use different logical row labels.
The synchronized tensor keeps one shared workspace of relative width thirteen,
and its base-ring gate count is charged to the packed parent length.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace DyadicCoefficientTower

open Real Matrix ConvolutionGrid

variable {η β C : ℝ} {n B : ℕ} {D : DyadicAxisPacking GaussianRationals η n B} {L : Finset ℕ}
    (T : DyadicCoefficientTower D L)

local notation "φ" => algebraMap (protectedRationals L) (protectedGaussian L)
local notation "e" => listCyclotomicDegree GaussianRationals D.pool B
local notation "r" => D.packing.jet
local notation "s" => D.packing.childCutoff 6
local notation "depth" => (6400*(1+Nat.clog 2 (2+B))+8 : ℕ)

/-- Either global prime change of basis costs at most nine times the stage
constant in the parent budget. This bound is uniform in the protected primes. -/
theorem primeGridMatrixCircuit (hn : 0 < n) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (ht : ShearTensorBound (protectedRationals L) β C)
    {I O : D.packing.axes → Type} [∀ i, Fintype (I i)]
    (A : ∀ i, Matrix (O i) (I i) (JetQuotient T.modulus r))
    (rows : ∀ i : D.packing.axes, Fin i.val ≃ O i)
    (cols : ∀ i : D.packing.axes, Fin i.val ≃ I i)
    (words : ∀ i : D.packing.axes,
      OccupiedWord (Fin (13*(i.val-1))) depth ((A i).submatrix (rows i) (cols i))) :
    JetMatrixCircuit φ (protectedGaussianI L) T.modulus e r (columns A)
      (D.packing.widthWork (9*AtTwoCost.wordConstant C β) β s) := by
  classical
  let N := ∏ p ∈ D.packing.axes, p
  have hpr (i : D.packing.axes) : i.val.Prime := (D.axis_properties T.width i.property).1
  have hN : 0 < N := Finset.prod_pos (fun p hp => (hpr ⟨p,hp⟩).pos)
  have hcard : Fintype.card (∀ i : D.packing.axes, Fin i.val) = N := by
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.univ_eq_attach, N]
    exact Finset.prod_attach _ id
  have hr : 0 < r := by
    have := (show 1 ≤ (B:ℝ) by exact_mod_cast (show 1 ≤ B by have := T.width; omega)).trans D.packing.jet_lower
    exact_mod_cast this
  have hc : 2*e*r ≤ s := Nat.mul_le_mul_right r (Nat.mul_le_mul_right e (by decide : 2 ≤ 6))
  have hs : 0 < s := D.packing.childCutoff_pos hn (by decide)
  have w := occupiedGridMatrixCircuit A rows cols (by decide : 0 < 14)
    (fun i => by simpa using (hpr i).two_le)
    (fun i => by
      simp only [Fintype.card_fin]; omega) words
    (T.jets hr) (protectedGaussian_coordinates L) T.monic T.degree_eq degree_pos hr hc ht hβ hC
  rw [hcard] at w
  obtain ⟨t, ht', q, hq⟩ := w
  refine ⟨t, ht'.trans ?_, q, hq⟩
  have hstage := AtTwoCost.stage_le («e» := e) («r» := r) (h := r) («s» := s) (W := 14*N)
    (D := 243*depth) (v := N) hn hs T.width hβ hC D.packing.product_le
    (by positivity) le_rfl (by omega) (by omega)
  have hd : fiberDepthFactor 14 = 243 := by decide
  simp only [occupiedGridJetCost, hd, Nat.cast_mul, Nat.cast_ofNat] at hstage ⊢
  apply hstage.trans
  let rate := AtTwoCost.rate n r s B β
  have hrate : 0 ≤ rate := (zero_le_one.trans (convolutionEnvelope_one_le hs)).trans
    (AtTwoCost.envelope_le_rate hn hs (by exact_mod_cast (show 1 ≤ B by have := T.width; omega)))
  have hV : (N:ℝ)*e*r ≤ 9*n := by exact_mod_cast D.packing.volume_upper
  have hK := AtTwoCost.wordConstant_nonneg (β := β) hC
  calc
    _ ≤ AtTwoCost.wordConstant C β * (9*n)*rate :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV hK) hrate
    _ = _ := by unfold PrimeJetPacking.widthWork rate AtTwoCost.rate; ring

variable [∀ i : D.packing.axes, Fact i.val.Prime] [Nontrivial T.Order]

/-- Both directions on the simultaneous CRT grid of every prime in the list.
The same chosen prime presentations are used for the two operands. -/
theorem primeGrid_circuits (hn : 0 < n) (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (ht : ShearTensorBound (protectedRationals L) β C) :
    let f := algebraMap T.Order (JetQuotient T.modulus r)
    let cost := D.packing.widthWork (9*AtTwoCost.wordConstant C β) β s
    JetMatrixCircuit φ (protectedGaussianI L) T.modulus e r
      (columns fun i : D.packing.axes => (T.primeAxis i.property).forward.map f) cost ∧
    JetMatrixCircuit φ (protectedGaussianI L) T.modulus e r
      (columns fun i : D.packing.axes => (T.primeAxis i.property).backward.map f) cost := by
  classical
  let f := algebraMap T.Order (JetQuotient T.modulus r)
  let cols (i : D.packing.axes) := (ZMod.finEquiv i.val).toEquiv
  let rows (i : D.packing.axes) := (cols i).trans (T.axisOrbit i.property).optionEquiv.symm
  have words (i : D.packing.axes) := T.primeAxis_words i.property (rows i) (cols i)
  constructor
  · exact T.primeGridMatrixCircuit hn hβ hC ht _ rows cols fun i => (words i).1.mapCoefficients f
  · exact T.primeGridMatrixCircuit hn hβ hC ht _ cols rows fun i => (words i).2.mapCoefficients f

end DyadicCoefficientTower

end FiniteFourier
end LinearAlgebra
end OAI
