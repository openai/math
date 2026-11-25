import OAI.Computability.NearSquareRoot.SynchronizedProductWord
import OAI.Computability.NearSquareRoot.PrecisionGridDigits
import OAI.Computability.NearSquareRoot.ProductMatrixLayers
import OAI.Computability.NearSquareRoot.SynchronizedCRTStream
import OAI.Computability.NearSquareRoot.CoprimeBox

/-!
# From input digits through rounded transform layers to output bits

The input and output of each numerical instruction are arrays of finite P192 records.
For a given forward and adjoint layer program, the per-layer Euclidean error bound
implies correctness of the whole multiplication calculation on each accepted box.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open IntegerMultiplication ResidueFourier SynchronizedPadding FixedPoint DigitPacking

noncomputable section
variable {d : ℕ} (a b : Fin d → ℕ) [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
variable (cop : Pairwise fun i j => (a i).Coprime (a j))

/-- Write the input digits in scaled CRT order and fill all unused slots with zero
records at the actual binary precision. -/
def inputRecords (n : ℕ) (x : Bits.Word) : PaddedBox a b → Record (addressBits n) :=
  let e := CRT.scaled a cop
  let f := unpackDigits (width n) (∏ i, a i) x
  fun i => digitRecord (addressBits n) (zeroExtend (fun j => Fin (b j))
    (fun v => f ((ZMod.finEquiv _).symm (e.symm v))) i)

theorem decode_inputRecords {n : ℕ} (hn : 2 ≤ n) (x : Bits.Word) :
    recordArray (inputRecords a b cop n x) = residueOperand a b cop n x := by
  ext i
  change value (addressBits n) (digitRecord _ _) =
    zeroExtend (fun j => Fin (b j)) _ i
  by_cases hi : i ∈ Set.range (occupied (A := fun j => ZMod (a j)) (fun j => Fin (b j)))
  · obtain ⟨v, rfl⟩ := hi
    simp only [zeroExtend_occupied]
    apply value_digit
    apply (unpackDigits_lt _ _ x _).le.trans
    exact Nat.pow_le_pow_right (by decide) (by have := width_le_twice_addressBits hn; omega)
  · rw [zeroExtend_off _ _ hi, zeroExtend_off _ _ hi, value_digit (Nat.zero_le _)]
    simp

omit [∀ i, NeZero (a i)] in
/-- At the CRT address of a valid rank the payload comes from the parsed list of
`count n` digits, extended with zeroes. -/
theorem inputRecords_at_rank {n : ℕ} (hn : 2 ≤ n) (x : Bits.Word) (hx : x.length = n)
    (hm : count n ≤ ∏ i, a i) (t : Fin (∏ i, a i)) :
    inputRecords a b cop n x (occupied (fun j => Fin (b j))
      (CRT.scaled a cop (ZMod.finEquiv _ t))) =
    digitRecord (addressBits n)
      (if hi : t.val < count n then
        Bits.value (Lea.crop (width n) (count n) x.reverse ⟨t.val,hi⟩)
       else 0) := by
  simp only [inputRecords, zeroExtend_occupied, AddEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  rw [unpackDigits_widen x (show x.length ≤ count n * width n by
    simpa [hx, Nat.mul_comm] using (count_mul_width hn).1) hm]

omit [∀ i, NeZero (a i)] in
theorem inputRecords_unused (n : ℕ) (x : Bits.Word) (i : PaddedBox a b)
    (hi : i ∉ Set.range (occupied (A := fun j => ZMod (a j)) (fun j => Fin (b j)))) :
    inputRecords a b cop n x i = digitRecord (addressBits n) 0 := by
  simp only [inputRecords, zeroExtend_off _ _ hi]

/-- The complete finite-record numerical path, starting from the original MSF words. -/
def multiply (n : ℕ) (F J : Layers (PaddedBox a b) (addressBits n)) (x y : Bits.Word) :
    Bits.Word :=
  let forward z := F.run (inputRecords a b cop n z) F.count
  let p := productArray (forward x) (forward y)
  productWord a b cop n (J.run p J.count)

/-- Accumulated forward error for the exact fixed-point encoding of an input word. -/
theorem forwardInput_error {n : ℕ} (hn : 2 ≤ n)
    (hcap : Fintype.card (PaddedBox a b) = capacity n) (F : Layers (PaddedBox a b) (addressBits n))
    (hf : F.Approximates (paddedIsometry a b).toLinearIsometry) (z : Bits.Word) :
    ‖recordArray (F.run (inputRecords a b cop n z) F.count) -
      paddedIsometry a b (residueOperand a b cop n z)‖ ≤ 1 / (2 : ℝ)^(40*addressBits n) := by
  let k := addressBits n
  have hk : 1 ≤ k := by
    have := width_le_twice_addressBits hn
    have := width_pos hn
    dsimp [k]; omega
  rw [← decode_inputRecords a b cop hn]
  apply hf.error hk
  rw [decode_inputRecords a b cop hn]
  apply (paddedDigit_norm a b hn (CRT.scaled a cop) _ (unpackDigits_lt _ _ z) hcap).trans
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Local correctness of a pair of synchronized rounded layer programs suffices for
every coefficient and every output bit. -/
theorem multiply_correct {n : ℕ} (hn : 2 ≤ n) (hcap : Fintype.card (PaddedBox a b) = capacity n)
    (hvol : 2*count n ≤ ∏ i, a i) (F J : Layers (PaddedBox a b) (addressBits n))
    (hf : F.Approximates (paddedIsometry a b).toLinearIsometry)
    (hj : J.Approximates (paddedIsometry a b).symm.toLinearIsometry)
    (x y : Bits.Word) (hx : x.length = n) (hy : y.length = n) :
    let z := multiply a b cop n F J x y
    z.length = 2*n ∧ bitValue z = bitValue x * bitValue y := by
  let k := addressBits n
  have hk : 1 ≤ k := by
    have h := width_le_twice_addressBits hn
    have hp := width_pos hn
    omega
  have he := forwardInput_error a b cop hn hcap F hf
  apply productWord_correct a b cop hn hcap hvol x y hx hy _ _ _ (he x) (he y)
  exact hj.error hk _

section PhysicalOutput

variable {n l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid (addressBits n) l box)
    [∀ i, NeZero (BoxFin.modulus box i)] [NeZero (∏ i, BoxFin.modulus box i)]

/-- Compute the output by applying the inverse balanced CRT routing, compacting the
valid physical stream in rank order, rounding its records, and carrying. -/
def physicalOutput (w : Fin (2^(addressBits n)) → Record (addressBits n)) : Bits.Word :=
  let k := addressBits n
  let S := ∏ i, BoxFin.modulus box i
  let dense := BoxMaskedRecords.compress (digitRecord k 0)
    (BoxOrder.expand (BoxOrder.shape box), List.ofFn (w ∘ BoxFin.crtSlotPerm hb))
  let s := sqrtRecord (fractionBits k) (componentBits k) S
  let words := dense.map (fun z => Bits.sized (3*width n) (recoverWord (FixedPoint.multiply k s z)))
  finishCarry (Code.tally (2*n), words, Lea.scale0 S (width n))

theorem physicalOutput_correct_readout
    (w : PaddedBox (BoxFin.modulus box) (BoxFin.padding box) → Record (addressBits n)) :
    physicalOutput hb (w ∘ (BoxFin.recordIndex hb).symm) =
      productWord _ _ (BoxFin.pairwise hb) n w := by
  dsimp only [physicalOutput]
  rw [BoxFin.compress_after_inverse_crt hb, List.map_ofFn]
  simp [productWord, carryPacket, BoxFin.residueSlot, Function.comp_def]

end PhysicalOutput

/-- Every accepted coprime box supplies all shape and cardinality hypotheses of the
integer calculation. The construction in `CoprimeBox` supplies these boxes eventually. -/
theorem valid_box_correct {n l : ℕ} (hn : 2 ≤ n) {box : List (ℕ × ℕ)}
    (hb : BoxShape.Valid (addressBits n) l box) :
    let a := BoxFin.modulus box
    let b := BoxFin.padding box
    letI : ∀ i, NeZero (a i) := BoxFin.modulus_neZero hb
    letI : NeZero (∏ i, a i) := ⟨Finset.prod_ne_zero_iff.mpr fun _i _ => NeZero.ne _⟩
    ∀ (F J : Layers (PaddedBox a b) (addressBits n)),
      F.Approximates (paddedIsometry a b).toLinearIsometry →
      J.Approximates (paddedIsometry a b).symm.toLinearIsometry →
      ∀ x y : Bits.Word, x.length = n → y.length = n →
      let z := multiply a b (BoxFin.pairwise hb) n F J x y
      z.length = 2*n ∧ bitValue z = bitValue x * bitValue y := by
  dsimp only
  let _ : ∀ i, NeZero (BoxFin.modulus box i) := BoxFin.modulus_neZero hb
  let _ : NeZero (∏ i, BoxFin.modulus box i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun _i _ => NeZero.ne _⟩
  intro F J hf hj x y hx hy
  exact multiply_correct _ _ _ hn (BoxFin.card_padded hb)
    (BoxFin.capacity hb (capacity_bounds hn).1) F J hf hj x y hx hy

theorem eventually_valid_multiplication_box :
    ∀ᶠ n in Filter.atTop, BoxShape.Valid (addressBits n) (BoxScale.width (addressBits n))
      (CoprimeBox.box (addressBits n)) := by
  obtain ⟨K, h⟩ := CoprimeBox.eventually_valid
  filter_upwards [addressBits_tendsto_atTop.eventually_ge_atTop K] with n hn
  exact h _ hn

end
end ProductRecovery

end NearSquareRoot
end Computability
end OAI
