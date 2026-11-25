import OAI.Computability.NearSquareRoot.ProductPhysicalInput

/-! # The physical record arrays before and after the rounded transforms -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open IntegerMultiplication DigitPacking FixedPoint ResidueFourier

noncomputable section
variable {n L : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid (addressBits n) L box)
  [∀ i, NeZero (BoxFin.modulus box i)] [NeZero (∏ i, BoxFin.modulus box i)]

/-- The dense input packet immediately before the forward CRT permutation. -/
def physicalInput (x : Bits.Word) : Fin (2^addressBits n) → Record (addressBits n) :=
  digitRecord (addressBits n) ∘ BoxFin.scatter hb 0
    (unpackDigits (width n) (∏ i, BoxFin.modulus box i) x)

/-- The encoded stack output of the actual parser is the physical input packet. -/
theorem encoded_physicalInput (x : Bits.Word) (hx : 2 ≤ x.length) (h : ValidShape x.length)
    [∀ i, NeZero (BoxFin.modulus (inputBox x) i)] [NeZero (∏ i, BoxFin.modulus (inputBox x) i)] :
    encodedBoxed x = List.ofFn (Dusk.mark ∘ physicalInput h x) :=
  encoded_before_crt x h hx

/-- Identify the full routed record array, including unused cells, at the transform input. -/
theorem route_physicalInput (x : Bits.Word) :
    (physicalInput hb x ∘ (BoxFin.crtSlotPerm hb).symm) ∘ BoxFin.recordIndex hb =
      inputRecords _ (BoxFin.padding box) (BoxFin.pairwise hb) n x := by
  funext i
  have h := congrFun (BoxFin.scatter_after_crt hb (unpackDigits (width n) (∏ j, BoxFin.modulus box j) x))
    (BoxFin.recordIndex hb i)
  change digitRecord _ _ = digitRecord _ _
  apply congrArg (digitRecord _)
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

/-- Evaluate both routed physical arrays, multiply their spectral records, apply the
inverse word, and perform inverse CRT routing, physical compaction, rounding, and carry. -/
def physicalProduct
    (F J : Layers (PaddedBox (BoxFin.modulus box) (BoxFin.padding box)) (addressBits n))
    (x y : Bits.Word) : Bits.Word :=
  let encode z := (physicalInput hb z ∘ (BoxFin.crtSlotPerm hb).symm) ∘ BoxFin.recordIndex hb
  let fw z := F.run (encode z) F.count
  let iw := J.run (productArray (fw x) (fw y)) J.count
  physicalOutput hb (iw ∘ (BoxFin.recordIndex hb).symm)

theorem physicalProduct_eq
    (F J : Layers (PaddedBox (BoxFin.modulus box) (BoxFin.padding box)) (addressBits n))
    (x y : Bits.Word) :
    physicalProduct hb F J x y =
      multiply _ (BoxFin.padding box) (BoxFin.pairwise hb) n F J x y := by
  simp only [physicalProduct, route_physicalInput, physicalOutput_correct_readout, multiply]

end
end ProductRecovery

end NearSquareRoot
end Computability
end OAI
