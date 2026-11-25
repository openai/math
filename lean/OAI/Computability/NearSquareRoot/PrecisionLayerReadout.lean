import OAI.Computability.NearSquareRoot.ProductRecovery
import OAI.Computability.NearSquareRoot.PrecisionMaskedCarry

/-! # Physical output of the scaled adjoint transform

A forward layer program acts on the two encoded input words. The adjoint acts on
their pointwise fixed-point product, and a fixed-point multiplication rescales
its records by the computed dyadic approximation to the square root of the box
volume. On this bank of records the mask, rounding and carry machine writes the
full binary product.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Code Bits DigitPacking ResidueFourier SynchronizedPadding
noncomputable section
set_option maxHeartbeats 1400000

section Records

variable {n l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid (addressBits n) l box)
  [∀ i, NeZero (BoxFin.modulus box i)] [NeZero (∏ i, BoxFin.modulus box i)]

/-- Scaled adjoint records on the tape, before the inverse CRT permutation. -/
def scaledLayerRecords
    (F J : ProductRecovery.Layers (PaddedBox (BoxFin.modulus box) (BoxFin.padding box)) (addressBits n))
    (x y : Word) : Fin (capacity n) → Record (addressBits n) :=
  let k := addressBits n
  let forward z := F.run (ProductRecovery.inputRecords (BoxFin.modulus box) (BoxFin.padding box) (BoxFin.pairwise hb) n z) F.count
  let product := productArray (forward x) (forward y)
  let adj := J.run product J.count
  let scale := sqrtRecord (fractionBits k) (componentBits k) (boxVolume box)
  fun j => multiply k scale (adj ((BoxFin.recordIndex hb).symm j))

/-- The quarter-unit numerical bound holds at every occupied physical residue
slot of the actual scaled, rounded adjoint run. -/
theorem scaledLayerRecords_error (hn : 2 ≤ n)
    (F J : ProductRecovery.Layers (PaddedBox (BoxFin.modulus box) (BoxFin.padding box)) (addressBits n))
    (hf : F.Approximates (paddedIsometry _ _).toLinearIsometry)
    (hj : J.Approximates (paddedIsometry _ _).symm.toLinearIsometry)
    (x y : Word) (hx : x.length = n) (hy : y.length = n) (t : Fin (boxVolume box)) :
    ‖FixedPoint.value (addressBits n) (scaledLayerRecords hb F J x y (BoxFin.residueSlot hb t)) -
      (ordinaryCoefficient (unpackDigits (width n) (boxVolume box) x)
        (unpackDigits (width n) (boxVolume box) y) t : ℂ)‖ ≤ 1/4 := by
  let k := addressBits n
  let forward z := F.run (ProductRecovery.inputRecords (BoxFin.modulus box) (BoxFin.padding box) (BoxFin.pairwise hb) n z) F.count
  let product := productArray (forward x) (forward y)
  have hk : 1 ≤ k := by
    have := width_pos hn
    have := width_le_twice_addressBits hn
    dsimp [k]; omega
  have h := productRecord_error (BoxFin.modulus box) (BoxFin.padding box) (BoxFin.pairwise hb) hn (BoxFin.card_padded hb)
    (BoxFin.capacity hb (capacity_bounds hn).1) x y hx hy (forward x) (forward y)
    (J.run product J.count)
    (ProductRecovery.forwardInput_error (BoxFin.modulus box) (BoxFin.padding box) (BoxFin.pairwise hb) hn (BoxFin.card_padded hb) F hf x)
    (ProductRecovery.forwardInput_error (BoxFin.modulus box) (BoxFin.padding box) (BoxFin.pairwise hb) hn (BoxFin.card_padded hb) F hf y)
    (hj.error hk _) t
  simpa only [scaledLayerRecords, BoxFin.residueSlot, Equiv.symm_apply_apply, forward, product] using h

end Records

/-- One finite tape machine performs the full post-inverse-CRT readout of the
specified layer runs on the given input words. Its time and total visited tape
cells are linear in the input length, uniformly over words and valid boxes. -/
theorem packedLayerToProduct {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hv : ∀ i, ValidDirectory (addressBits (n i))) (x y : I → Word)
    (v : (i : I) → Fin (capacity (n i)) → Record (addressBits (n i)))
    (hx : ∀ i, (x i).length = n i) (hy : ∀ i, (y i).length = n i)
    (layers : ∀ i,
      let box := CoprimeBox.box (addressBits (n i))
      letI := BoxFin.modulus_neZero (hv i)
      letI : NeZero (boxVolume box) := ⟨Finset.prod_ne_zero_iff.mpr fun j _ => NeZero.ne (BoxFin.modulus box j)⟩
      ∃ F J : ProductRecovery.Layers (PaddedBox (BoxFin.modulus box) (BoxFin.padding box)) (addressBits (n i)),
        F.Approximates (paddedIsometry _ _).toLinearIsometry ∧
        J.Approximates (paddedIsometry _ _).symm.toLinearIsometry ∧
        v i = scaledLayerRecords (hv i) F J (x i) (y i)) :
    ∃ z : I → Word, (∀ i, (z i).length = 2*n i ∧ bitValue (z i) = bitValue (x i)*bitValue (y i)) ∧
      Task n (fun i => send (tally (addressBits (n i)), decodePacket (n i) (width (n i))
        (fractionBits (addressBits (n i))) (afterInverseCRT (hv i) (v i)))) (fun i => send (z i)) ∧
      TreeToPlainBits (fun i => send (tally (addressBits (n i)), decodePacket (n i) (width (n i))
        (fractionBits (addressBits (n i))) (afterInverseCRT (hv i) (v i)))) z n := by
  apply packedInverseGridToProduct n hn hv x y v hx hy
  intro i t
  let := BoxFin.modulus_neZero (hv i)
  let : NeZero (directoryVolume (addressBits (n i))) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun j _ => NeZero.ne _⟩
  obtain ⟨F,J,hf,hj,he⟩ := layers i
  rw [he]
  exact (scaledLayerRecords_error (hv i) (hn i) F J hf hj (x i) (y i) (hx i) (hy i) t).trans_lt
    (by norm_num)

end
end FixedPoint

end NearSquareRoot
end Computability
end OAI
