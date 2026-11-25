import OAI.Computability.NearSquareRoot.ProductPhysicalStream
import OAI.Computability.NearSquareRoot.ProductCanonical
import OAI.Computability.NearSquareRoot.ProductBoxPrimitive
import OAI.Computability.NearSquareRoot.PrecisionFlatWalsh

/-! # Finite-record multiplication for the executable coprime-box shapes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open IntegerMultiplication DigitPacking ResidueFourier ShortFourier SynchronizedBlocks Matrix

/-- Each accepted box admits forward and inverse finite-record programs of the
synchronized Fourier word lengths, using quantized phases and the evaluated
integer butterflies with dyadic normalization at every selected-bit slot. -/
theorem box_products {n L : ℕ} (hn : 2 ≤ n) {box : List (ℕ × ℕ)}
    (hb : BoxShape.Valid (addressBits n) L box)
    [∀ i, NeZero (BoxFin.modulus box i)] [NeZero (∏ i, BoxFin.modulus box i)]
    (hd : 4 ≤ box.length) (hk : 1024 ≤ addressBits n) (hL : L ≤ addressBits n) :
    let a := BoxFin.modulus box
    let b := BoxFin.padding box
    ∃ F J : Layers (PaddedBox a b) (addressBits n),
      F.count = 7560000*(L+2) ∧ J.count = 7560000*(L+2) ∧
      ∀ x y : Bits.Word, x.length = n → y.length = n →
        let z := multiply a b (BoxFin.pairwise hb) n F J x y
        z.length = 2*n ∧ bitValue z = bitValue x * bitValue y := by
  obtain ⟨F,J,hF,hJ,hf,hj⟩ := valid_box_programs hb hd hk hL
    (boxStage_of_flatWalsh hb hd (by omega) (fun bits hu =>
      ⟨FixedPoint.selectedWalshStep bits, FixedPoint.selectedWalshStep_error (by omega) bits hu⟩))
  exact ⟨F,J,hF,hJ,multiply_correct _ _ _ hn (BoxFin.card_padded hb)
    (BoxFin.capacity hb (capacity_bounds hn).1) F J hf hj⟩

/-- The trial-division box and precision are fixed functions of input length.
The two rounded words selected here work for every operand pair of that length. -/
theorem eventually_product_programs :
    ∀ᶠ n in Filter.atTop, let k := addressBits n
      let L := BoxScale.width k
      let box := CoprimeBox.box k
      ∃ hb : BoxShape.Valid k L box,
        let a := BoxFin.modulus box
        let b := BoxFin.padding box
        letI : ∀ i, NeZero (a i) := BoxFin.modulus_neZero hb
        letI : NeZero (∏ i, a i) := ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
        ∃ F J : Layers (PaddedBox a b) k,
          F.count = 7560000*(L+2) ∧ J.count = 7560000*(L+2) ∧
          ∀ x y : Bits.Word, x.length = n → y.length = n →
            physicalProduct hb F J x y = Lea.answer (x,y) := by
  filter_upwards [eventually_valid_multiplication_box, Filter.eventually_ge_atTop 2,
    addressBits_tendsto_atTop.eventually_ge_atTop 1024] with n hb hn hk
  refine ⟨hb, ?_⟩
  let _ := BoxFin.modulus_neZero hb
  let _ : NeZero (∏ i, BoxFin.modulus (CoprimeBox.box (addressBits n)) i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _⟩
  have hwidth := three_width_lt hk
  obtain ⟨F,J,hF,hJ,h⟩ := box_products hn hb (four_le_length hb hwidth) hk (by omega)
  refine ⟨F,J,hF,hJ,fun x y hx hy => ?_⟩
  rw [physicalProduct_eq]
  exact (product_postcondition_iff x y _ hx hy).mp (h x y hx hy)

end ProductRecovery

end NearSquareRoot
end Computability
end OAI
