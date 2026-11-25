import OAI.Computability.NearSquareRoot.PrecisionDigitBox
import OAI.Computability.NearSquareRoot.PrecisionGridDigits
import OAI.Computability.NearSquareRoot.SynchronizedCRTStream

/-! # Interpretation of the input records after the balanced CRT permutation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace DigitPacking

open IntegerMultiplication IntegerMultiplication.Bits IntegerMultiplication.Code
open BoxFin SynchronizedPadding FixedPoint

noncomputable section

abbrev inputBox (x : Word) := CoprimeBox.box (addressBits x.length)

/-- The actual initialized real/imaginary record packet at every tape slot. -/
def encodedBoxed (x : Word) : List Dusk.Pair :=
  let k := addressBits x.length
  (boxed x).map fun w => encodeDigit (w, tally (fractionBits k), tally (componentBits k+1))

variable (x : Word) (hb : ValidShape x.length)
variable [∀ i, NeZero (modulus (inputBox x) i)]

private theorem boxed_words :
    boxed x = List.ofFn (BoxFin.scatter hb ([] : Word)
      (Lea.crop (width x.length) (∏ i, modulus (inputBox x) i) x.reverse)) := by
  dsimp only [boxed, BoxMaskProgram.mask]
  rw [BoxOrder.count_shape, ← BoxFin.prod_modulus]
  exact expand_dense hb _ _

private theorem scatter_word_value {a b : ℕ} {box : List (ℕ × ℕ)} (H : BoxShape.Valid a b box)
    [∀ i, NeZero (modulus box i)] (f : Fin (∏ i, modulus box i) → Word) :
    Bits.value ∘ BoxFin.scatter H [] f = BoxFin.scatter H 0 (Bits.value ∘ f) := by
  funext j
  by_cases h : j ∈ Set.range (digitSlot H)
  · obtain ⟨i,rfl⟩ := h
    simp [Function.comp_apply, BoxFin.scatter, (digitSlot_strictMono H).injective.extend_apply]
  · simp [Function.comp_apply, BoxFin.scatter, Function.extend_apply' _ _ _ h]

theorem boxed_values :
    (boxed x).map Bits.value = List.ofFn (BoxFin.scatter hb 0
      (Bits.value ∘ Lea.crop (width x.length) (∏ i, modulus (inputBox x) i) x.reverse)) := by
  rw [boxed_words x hb, List.map_ofFn, scatter_word_value]

private theorem scatter_word_bound (hn : 2 ≤ x.length) (j : Fin (2^addressBits x.length)) :
    let crop := Lea.crop (width x.length) (∏ i, modulus (inputBox x) i) x.reverse
    Bits.value (BoxFin.scatter hb [] crop j) ≤ 2^(13*addressBits x.length) := by
  dsimp only
  by_cases h : j ∈ Set.range (digitSlot hb)
  · obtain ⟨i,rfl⟩ := h
    rw [BoxFin.scatter, (digitSlot_strictMono hb).injective.extend_apply]
    apply (value_lt _).le.trans
    rw [(Lea.crop_ ..).1 i]
    apply Nat.pow_le_pow_right (by decide)
    have hw := width_le_twice_addressBits hn
    omega
  · rw [BoxFin.scatter, Function.extend_apply' _ _ _ h]
    exact Nat.zero_le _

/-- The array passed to the record router, in digit order. -/
def boxedArray : Fin (2^addressBits x.length) → Record (addressBits x.length) :=
  digitRecord (addressBits x.length) ∘ BoxFin.scatter hb 0
    (Bits.value ∘ Lea.crop (width x.length) (∏ i, modulus (inputBox x) i) x.reverse)

/-- The physical stack program emits this complete list in the router's input order. -/
theorem encoded_before_crt (hn : 2 ≤ x.length) :
    encodedBoxed x = List.ofFn (Dusk.mark ∘ boxedArray x hb) := by
  unfold encodedBoxed boxedArray
  rw [boxed_words x hb, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  dsimp only [Function.comp_apply]
  rw [encodeDigit_eq _ (scatter_word_bound x hb hn j)]
  exact congrArg (Dusk.mark ∘ digitRecord _) (congrFun (scatter_word_value hb _) j)

/-- A checked connection between the actual boxed MSF input and the transform's
initial array. Inverse permutation indexing of the physical records yields
the signed fixed-point encoding of the scaled-residue, zero-extended digits. -/
theorem encoded_after_crt (hn : 2 ≤ x.length)
    [NeZero (∏ i, modulus (inputBox x) i)] :
    let k := addressBits x.length
    let a := modulus (inputBox x)
    let b := padding (inputBox x)
    let digits := Bits.value ∘ Lea.crop (width x.length) (∏ i, a i) x.reverse
    let scaled := digits ∘ (ZMod.finEquiv _).symm ∘ (CRT.scaled a (pairwise hb)).symm
    List.ofFn (fun j : Fin (2^k) => ((encodedBoxed x)[((crtSlotPerm hb).symm j).val]?).getD ([],[])) =
      List.ofFn (fun j : Fin (2^k) => Dusk.mark (digitRecord k
        (zeroExtend (fun i => Fin (b i)) scaled ((recordIndex hb).symm j)))) := by
  dsimp only
  apply congrArg List.ofFn
  funext j
  let s := (crtSlotPerm hb).symm j
  let crop := Lea.crop (width x.length) (∏ i, modulus (inputBox x) i) x.reverse
  change ((encodedBoxed x)[s.val]?).getD ([],[]) = _
  unfold encodedBoxed
  rw [boxed_words x hb, List.map_ofFn]
  simp only [List.getElem?_ofFn, s.isLt, dite_true, Option.getD_some, Function.comp_apply]
  rw [encodeDigit_eq _ (scatter_word_bound x hb hn s)]
  congr 2
  have hvalue := congrFun (scatter_word_value hb crop) s
  have hroute := congrFun (scatter_after_crt hb (Bits.value ∘ crop)) j
  exact hvalue.trans hroute

end
end DigitPacking

end NearSquareRoot
end Computability
end OAI
