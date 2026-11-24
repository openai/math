import OAI.Computability.VPVNP.LabelEvaluator
import OAI.Computability.VPVNP.SliceArithmeticAdvice

/-!
# Binary advice for the finite-algebra evaluator

The tape begins with a fixed-width prime header. Once the prime is known, the
extension degree is determined by the system's variable and degree bounds.
The following fields contain the low coefficients of the monic modulus, one
pin bit per variable, and one field element per variable. The pin values use
the same power basis as the evaluator's final coordinate query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorAdviceSerialization

open SliceArithmetic LabelEvaluator

/-- The extension degree chosen for characteristic p and the column-count bound on the slice
system in t variables of degree at most d. -/
abbrev degree (p t d : ℕ) := SliceField.extensionDegree p (columnCountBound t d)
/-- Bit width of one power-basis coefficient vector. Each of its e residues occupies the
ceiling of the base-two logarithm of p in bits. -/
abbrev vectorBits (p e : ℕ) := e * Nat.clog 2 p

/-- The length of the advice prefix consisting of the prime header, modulus coefficients, pin
mask and t value vectors. -/
def length (w p e t : ℕ) := w + vectorBits p e + t + t * vectorBits p e

/-- The modulus coefficients, pin mask and specialized field elements in the advice for a slice
over characteristic p. -/
structure Fields (p e t : ℕ) where
  /-- The e lower coefficients of the monic modulus defining the advised power-basis field
  representation. -/
  coefficients : SliceArithmetic.Vector p e
  /-- One bit per system variable identifying the coordinates fixed by the slice. -/
  pins : Fin t → Bool
  /-- The advised power-basis value for each variable, including each coordinate marked by the
  pin mask. -/
  values : Fin t → SliceArithmetic.Vector p e

/-- Serialize all `t` values consecutively, including those at unpinned coordinates. -/
private def valueBits {p e t : ℕ} (a : Fields p e t) (i : Fin (t * vectorBits p e)) : Bool :=
  let ij := finProdFinEquiv.symm i
  SliceArithmetic.encode (a.values ij.1) ij.2

/-- Write the fixed-width prime, the lower modulus coefficients, the pin mask and all
coordinate values consecutively on the binary advice tape. -/
def encode {w p e t : ℕ} (hp : p < 2 ^ w) (a : Fields p e t) : List Bool :=
  List.ofFn (RAMSerialization.wordBits w ⟨p, hp⟩) ++ List.ofFn (SliceArithmetic.encode a.coefficients) ++
    List.ofFn a.pins ++ List.ofFn (valueBits a)

@[simp] theorem length_encode {w p e t : ℕ} (hp : p < 2 ^ w) (a : Fields p e t) :
    (encode hp a).length = length w p e t := by simp [encode, length, vectorBits, Nat.add_assoc]

/-- Read consecutive bits at an absolute address, with zero outside the tape. -/
def readBits (tape : List Bool) (start count : ℕ) (i : Fin count) : Bool :=
  tape[start + i.val]?.getD false

private theorem readBits_at (pre tail : List Bool) {k : ℕ} (bits : Fin k → Bool) :
    readBits (pre ++ (List.ofFn bits ++ tail)) pre.length k = bits := by
  funext i
  rw [readBits, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simp), List.getElem?_eq_getElem (by simp)]
  simp

/-- Decode the prime header as a natural number from the first w bits of the advice tape,
padding missing bits with zero. -/
def readPrime (w : ℕ) (tape : List Bool) : ℕ :=
  ((RAMSerialization.wordBits w).symm (readBits tape 0 w)).val

/-- After the prime header is decoded, all remaining offsets are fixed. -/
def readFields (w p e t : ℕ) [NeZero p] (tape : List Bool) : Fields p e t where
  coefficients := ofBits (readBits tape w (vectorBits p e))
  pins := readBits tape (w + vectorBits p e) t
  values i := ofBits fun j =>
    readBits tape (w + vectorBits p e + t) (t * vectorBits p e) (finProdFinEquiv (i, j))

@[simp] theorem readPrime_encode {w p e t : ℕ} (hp : p < 2 ^ w) (a : Fields p e t) (tail : List Bool) :
    readPrime w (encode hp a ++ tail) = p := by
  let bits := RAMSerialization.wordBits w (⟨p, hp⟩ : BurstRAM.Word w)
  have h := readBits_at [] (List.ofFn (SliceArithmetic.encode a.coefficients) ++
    List.ofFn a.pins ++ List.ofFn (valueBits a) ++ tail) bits
  have h' : readBits (encode hp a ++ tail) 0 w = bits := by
    simpa only [encode, bits, List.nil_append, List.length_nil, List.append_assoc] using h
  simp [readPrime, h', bits]

@[simp] theorem readFields_encode {w p e t : ℕ} [NeZero p] (hp : p < 2 ^ w) (a : Fields p e t)
    (tail : List Bool) : readFields w p e t (encode hp a ++ tail) = a := by
  let header := List.ofFn (RAMSerialization.wordBits w (⟨p, hp⟩ : BurstRAM.Word w))
  let coeff := List.ofFn (SliceArithmetic.encode a.coefficients)
  let mask := List.ofFn a.pins
  have hc : readBits (encode hp a ++ tail) w (vectorBits p e) = SliceArithmetic.encode a.coefficients := by
    simpa only [encode, header, mask, List.length_ofFn, List.append_assoc] using
      readBits_at header (mask ++ List.ofFn (valueBits a) ++ tail) (SliceArithmetic.encode a.coefficients)
  have hm : readBits (encode hp a ++ tail) (w + vectorBits p e) t = a.pins := by
    simpa only [encode, header, coeff, List.length_append, List.length_ofFn, List.append_assoc] using
      readBits_at (header ++ coeff) (List.ofFn (valueBits a) ++ tail) a.pins
  have hv : readBits (encode hp a ++ tail) (w + vectorBits p e + t) (t * vectorBits p e) = valueBits a := by
    simpa only [encode, header, coeff, mask, List.length_append, List.length_ofFn, List.append_assoc, Nat.add_assoc] using
      readBits_at ((header ++ coeff) ++ mask) tail (valueBits a)
  simp [readFields, hc, hm, hv, valueBits]

private def parseAtPrime (w t d p : ℕ) (tape : List Bool) :
    Option ((q : Nat.Primes) × Fields q.val (degree q.val t d) t) :=
  if h : p.Prime then
    haveI : NeZero p := ⟨h.ne_zero⟩
    if length w p (degree p t d) t ≤ tape.length then
      some ⟨⟨p, h⟩, readFields w p (degree p t d) t tape⟩
    else none
  else none

/-- Parse a prime from the tape and use the degree selected in Section 8.2.
The tape may have trailing padding. A composite header or short tape fails. -/
def parse (w t d : ℕ) (tape : List Bool) : Option ((p : Nat.Primes) × Fields p.val (degree p.val t d) t) :=
  parseAtPrime w t d (readPrime w tape) tape

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- A finite enumeration of the slice ground field for representing the advised pin values. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _

theorem parse_encode {w t d : ℕ} (p : Nat.Primes) (hp : p.val < 2 ^ w)
    (a : Fields p.val (degree p.val t d) t) (tail : List Bool) :
    parse w t d (encode hp a ++ tail) = some ⟨p, a⟩ := by
  rw [parse, readPrime_encode]
  simp [parseAtPrime, p.prop]
  rfl

/-- All advised pin values have coefficient vectors in the same quotient
presentation that realizes the evaluator's prime-field coordinate. -/
theorem exists_model_advice {t d w : ℕ} {p : Nat.Primes} {ι : Type*}
    {F : ι → MvPolynomial (Fin t) ℤ} (M : Model p d F) (hp : p.val < 2 ^ w) :
    ∃ tape : List Bool, tape.length = length w p.val (degree p.val t d) t ∧
      ∃ a : Fields p.val (degree p.val t d) t,
        (∀ tail, parse w t d (tape ++ tail) = some ⟨p, a⟩) ∧
        ∃ φ : AdjoinRoot (modulus a.coefficients) ≃ₐ[ZMod p.val] Ground p t d,
          Irreducible (modulus a.coefficients) ∧
          (∀ i, a.pins i = decide (i ∈ M.pins)) ∧
          (∀ i, φ (value (modulus a.coefficients) (a.values i)) = M.values i) ∧
          ∀ v : SliceArithmetic.Vector p.val (degree p.val t d),
            SliceEvaluator.primeCoordinate p.val (Ground p t d)
            (φ (value (modulus a.coefficients) v)) = ((v ⟨0, Nat.succ_pos _⟩).val : ZMod p.val) := by
  obtain ⟨c, φ, _, hirr, hcoord⟩ := exists_compatible_advice p.val (columnCountBound t d)
  have hsurj : Function.Surjective (φ ∘ value (e := degree p.val t d) (modulus c)) := by
    refine ((Nat.bijective_iff_injective_and_card _).mpr ⟨φ.injective.comp
      (value_injective (modulus_monic c) (modulus_natDegree c)), ?_⟩).2
    rw [SliceField.field_card]
    simp [SliceArithmetic.Vector]
  choose values hv using fun i => hsurj (M.values i)
  let a : Fields p.val (degree p.val t d) t := ⟨c, fun i => decide (i ∈ M.pins), values⟩
  exact ⟨encode hp a, length_encode hp a, a, parse_encode p hp a, φ, hirr, fun _ => rfl, hv, hcoord⟩

end EvaluatorAdviceSerialization

end VPVNP
end Computability
end OAI
