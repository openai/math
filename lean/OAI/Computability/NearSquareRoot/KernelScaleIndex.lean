import OAI.Computability.NearSquareRoot.KernelScaleStream
import OAI.Computability.IntegerMultiplication.Partial

/-! # Physical address order of a normalized scale pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleStream
open IntegerMultiplication Code

private def digit (b : Bool) : Fin 2 := if b then 1 else 0

private theorem code_bits (xs : List Bool) :
    Adic.code (xs.map digit) = Bits.value xs := by
  induction xs with
  | nil => rfl
  | cons b l ih => cases b <;> simp [digit, Adic.code, ih]

private theorem rank_digits (xs : List Bool) :
    Adic.code (xs.map digit).reverse = bitValue xs := by
  rw [← List.map_reverse, code_bits, endianness]

private theorem word_at (w : Adic.Raw 2) (v : Tally) (hw : w.length = v.length) :
    (Adic.shoots 2 v)[Adic.code w.reverse]? = some w := by
  induction v generalizing w with
  | nil =>
    have e : w = [] := List.length_eq_zero_iff.mp hw
    subst w
    rfl
  | cons t v ih =>
    cases w with
    | nil => simp at hw
    | cons b w =>
      have h : w.length = v.length := Nat.succ.inj hw
      have cap := Adic.limit w.reverse
      simp only [List.length_reverse, h] at cap
      rw [Adic.shoots_cons, Adic.stretch,
        show List.finRange 2 = [0,1] by decide, List.map_cons, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.reverse_cons, Adic.cat, List.length_reverse, h]
      change (_ ++ _)[Adic.code w.reverse + 2 ^ v.length * (b.val + 2 * 0)]? = _
      have len : ((Adic.shoots 2 v).map (List.cons (0 : Fin 2))).length = 2^v.length := by simp
      fin_cases b
      · simp only [Fin.isValue, Nat.mul_zero, Nat.add_zero]
        rw [List.getElem?_append_left (len ▸ cap), List.getElem?_map, ih w h]
        rfl
      · simp only [Fin.isValue, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
        rw [List.getElem?_append_right (by rw [len]; omega), len, Nat.add_sub_cancel,
          List.getElem?_map, ih w h]
        rfl

/-- The position of an encoded rectangular address in the generated table
is exactly the natural number represented by its MSF bit string. -/
theorem addressColumns_get (a : ℕ) (cs : List (KernelSelectorAlign.Column a)) :
    (KernelSelector.addressColumns a cs.length)[bitValue (KernelSelectorAlign.flatBits a cs)]? =
      some cs := by
  let b := KernelSelectorAlign.flatBits a cs
  let w := b.map digit
  have len : w.length = (tally ((a+1)*cs.length)).length := by simp [w,b]
  have atKey := word_at w (tally ((a+1)*cs.length)) len
  rw [rank_digits] at atKey
  change (KernelSelector.addressColumns a cs.length)[bitValue b]? = _
  rw [KernelSelector.addressColumns, List.getElem?_map, atKey]
  simp only [Option.map_some]
  have joinBits : w.map KernelSelector.digitBit = b := by
    simp only [w, List.map_map]
    have iden : KernelSelector.digitBit ∘ digit = id := by funext t; cases t <;> rfl
    simp [iden]
  simp only [joinBits, b, KernelSelectorAlign.decode_flatBits]

private theorem two_per_column {a : ℕ} (s : List (KernelPass.Column (a+1))) :
    (singleColumns s).length = 2*s.length := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [singleColumns, List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons] at *
    omega

/-- Reading the output at the flat MSF key gives exactly the rational diagonal
entry of the corresponding scale instruction in the normalized template. -/
theorem scale_entry_at {a q h : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → KernelPass.Coefficient) (x : KernelPass.Addr (a+1) h) :
    let key := bitValue (KernelSelectorAlign.flatBits a (singleColumns (List.ofFn x)))
    let output := (KernelSelector.addressColumns a (2*h)).map (emit test table)
    (output[key]?).map wordValue = some ((KernelPass.Plan.scale q test table).eval h (0,x) (0,x)) := by
  have atKey := addressColumns_get a (singleColumns (List.ofFn x))
  rw [two_per_column, List.length_ofFn] at atKey
  dsimp only
  rw [List.getElem?_map, atKey, Option.map_some, Option.map_some, emit_correct]

end KernelScaleStream

end NearSquareRoot
end Computability
end OAI
