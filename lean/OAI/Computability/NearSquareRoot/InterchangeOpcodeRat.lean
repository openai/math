import OAI.Computability.MinUncut.Search.RawRationalArithmetic

/-! # Signed rational operands of the address-machine opcodes

The raw arithmetic stores a numerator as the difference of two natural numbers
and a positive denominator by its predecessor. Hence addition, multiplication and
comparison work on primitive-recursively coded triples, without normalization.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Opcode

abbrev Scalar := MinUncut.Preprocess.RawRat

namespace Scalar

open MinUncut.Preprocess

abbrev val := RawRat.value
abbrev zero : Scalar := RawRat.ofNat 0
abbrev one : Scalar := RawRat.ofNat 1
abbrev add := RawRat.add
abbrev mul := RawRat.mul

/-- A zero denominator in a malformed instruction is interpreted as one. -/
def ofRaw (negative : Bool) (num den : ℕ) : Scalar :=
  if negative then (0, num, den - 1) else (num, 0, den - 1)

/-- Equality of the rational values by two natural-number cross comparisons. -/
def eqb (a b : Scalar) : Bool := decide (RawRat.le a b ∧ RawRat.le b a)

@[simp] theorem val_zero : val zero = 0 := by simp [val, zero]
@[simp] theorem val_one : val one = 1 := by simp [val, one]

@[simp] theorem val_add (a b : Scalar) : val (add a b) = val a + val b :=
  RawRat.value_add a b

@[simp] theorem val_mul (a b : Scalar) : val (mul a b) = val a * val b :=
  RawRat.value_mul a b

theorem val_ofRaw (negative : Bool) (num den : ℕ) (h : 0 < den) :
    val (ofRaw negative num den) = (if negative then -1 else 1 : ℚ) * num * (den : ℚ)⁻¹ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  cases negative <;> simp [ofRaw, val, RawRat.value, div_eq_mul_inv]

@[simp] theorem eqb_eq_true (a b : Scalar) : eqb a b = true ↔ val a = val b := by
  rw [eqb, decide_eq_true_eq, RawRat.le_iff, RawRat.le_iff]
  exact le_antisymm_iff.symm

theorem primrec_ofRaw : Primrec fun p : Bool × ℕ × ℕ => ofRaw p.1 p.2.1 p.2.2 := by
  have hn : Primrec fun p : Bool × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hd : Primrec fun p : Bool × ℕ × ℕ => p.2.2 - 1 :=
    Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true))
    ((Primrec.const 0).pair (hn.pair hd)) (hn.pair ((Primrec.const 0).pair hd))

theorem primrec_add : Primrec₂ add := RawRat.primrec_add
theorem primrec_mul : Primrec₂ mul := RawRat.primrec_mul

theorem primrec_eqb : Primrec₂ eqb :=
  ((RawRat.primrec_le.comp Primrec.fst Primrec.snd).and
    (RawRat.primrec_le.comp Primrec.snd Primrec.fst)).decide.to₂

end Scalar
end Opcode

end NearSquareRoot
end Computability
end OAI
