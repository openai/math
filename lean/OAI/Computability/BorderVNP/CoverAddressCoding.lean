import OAI.Computability.BorderVNP.CoverDeckBitArithmetic
import OAI.Computability.BorderVNP.StackBooleanFrame

/-! # Canonical bit wires for cover addresses

A deck element is represented by four binary residues in the self-delimiting
record format used by the stack programs. The linear slot budget includes the
entire record, so equality of the padded wires detects equality of tiles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open RationalHitting.StackLanguage BorderVNP.StackFrame

/-- Number of padded bit positions reserved for a four-residue address. -/
abbrev width (l : ℕ) := 30 * (l+1)

/-- Serialized canonical quaternion coordinates. -/
def word (l : ℕ) (x : Address l) : List Bool := code (binaryCoords l x)

/-- One-hot address wires, with an explicit absent-bit symbol in padding. -/
def wires (l : ℕ) (x : Address l) : Slots (width l) → Bool := padded (width l) (word l x)

/-- The wire assignment of an element of the actual deck quotient. -/
def deckWires (l : ℕ) (x : Deck l) : Slots (width l) → Bool := wires l (deckAddress l x).val

/-- The binary modulus takes at most three bits per level and one additional bit. -/
theorem modulus_length (l : ℕ) : (7^l).bits.length ≤ 3*l+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
  have h := Nat.pow_le_pow_left (show 7 ≤ 2^3 by decide) l
  rw [← pow_mul] at h
  have hp : 0 < 2^(3*l) := by positivity
  omega

/-- All four coordinate records and their delimiters fit in the reserved space. -/
theorem word_length (l : ℕ) (x : Address l) : (word l x).length ≤ width l := by
  have bits (z : ZMod (7^l)) : z.val.bits.length ≤ 3*l := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact residue_lt_bit_bound _ _
  simp only [word,binaryCoords,prod_code_length,nat_code_length,width]
  have h1 := bits x.re
  have h2 := bits x.imI
  have h3 := bits x.imJ
  have h4 := bits x.imK
  omega

private theorem record_unique (x x' y y' : List Bool)
    (h : codeWord x ++ y = codeWord x' ++ y') : x = x' ∧ y = y' := by
  induction x generalizing x' with
  | nil => cases x' <;> simp_all [codeWord]
  | cons b x ih =>
    cases x' with
    | nil => simp [codeWord] at h
    | cons b' x' =>
      simp only [codeWord,List.cons_append,List.cons.injEq, true_and] at h
      obtain ⟨e,r⟩ := ih x' h.2
      simp [h.1,e,r]

private theorem pair_injective {A B : Type} [Coding A] [Coding B]
    (hA : Function.Injective (code : A → _)) (hB : Function.Injective (code : B → _)) :
    Function.Injective (code : A × B → _) := by
  intro x y h
  obtain ⟨u,v⟩ := record_unique _ _ _ _ h
  exact Prod.ext (hA u) (hB v)

/-- Serialized quaternion addresses are faithful. -/
theorem word_injective (l : ℕ) : Function.Injective (word l) := by
  have hn : Function.Injective (code : ℕ → _) := fun a b h => by
    simpa only [wordValue_bits] using congrArg wordValue (show a.bits = b.bits from h)
  intro x y h
  have he := (pair_injective hn (pair_injective hn (pair_injective hn hn))) h
  exact QuaternionAlgebra.ext
    (ZMod.val_injective _ (congrArg Prod.fst he))
    (ZMod.val_injective _ (congrArg (fun z => z.2.1) he))
    (ZMod.val_injective _ (congrArg (fun z => z.2.2.1) he))
    (ZMod.val_injective _ (congrArg (fun z => z.2.2.2) he))

/-- Equality on all three one-hot wires recovers every bit of each address. -/
theorem wires_injective (l : ℕ) : Function.Injective (wires l) := by
  intro x y h
  apply word_injective l
  apply List.ext_getElem?'
  intro i hi
  have hlt : i < width l := hi.trans_le (max_le (word_length l x) (word_length l y))
  have he := congrFun h (⟨i,hlt⟩, (word l x)[i]?)
  change decide ((word l x)[i]? = (word l x)[i]?) = decide ((word l y)[i]? = (word l x)[i]?) at he
  simpa [eq_comm] using he

/-- The bit wires distinguish all tiles of the deck quotient. -/
theorem deckWires_injective (l : ℕ) : Function.Injective (deckWires l) :=
  (wires_injective l).comp (Units.val_injective.comp (deckAddress_injective l))

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
