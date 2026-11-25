import OAI.Computability.BorderVNP.ParseBatchRecordsPacked
import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Data.Fin.VecNotation

/-! # Bit encodings of preorder records, with canonical fixed-width padding -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP

/-- Two single-bit fields and the bit positions of the six word fields. -/
abbrev BitSlot (w : ℕ) := Bool ⊕ (Fin 6 × Fin w)

/-- The parse verifier guesses this many bits per node. -/
theorem card_bitSlot (w : ℕ) : Fintype.card (BitSlot w) = 2+6*w := by simp [BitSlot]

/-- Read the unsigned fields in their fixed physical order. -/
def Fields.word (a : Fields) : Fin 6 → ℕ := ![a.parent, a.layer, a.split, a.left, a.right, a.pos]

/-- All indexed numerical fields of a canonical record fit the common word. -/
theorem word_lt {m g n : ℕ} (t : GrammarLabel (Fin m × Bool) (Fin g) n) (i : Fin 6) :
    (pack t).word i < 2 ^ recordWidth m g n := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := fields_fit t
  fin_cases i <;> first | exact ha | exact hb | exact hc | exact hd | exact he | exact hf

/-- All bits of the canonical representation, least significant word bit first. -/
def packBits {m g n : ℕ} (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    BitSlot (recordWidth m g n) → Bool
  | .inl false => (pack t).binary
  | .inl true => (pack t).bit
  | .inr (i,j) => RAMSerialization.wordBits _ ⟨(pack t).word i, word_lt t i⟩ j

/-- Decode each fixed-width unsigned word from its bit positions. -/
def fieldsOfBits {w : ℕ} (bs : BitSlot w → Bool) : Fields :=
  let val := fun i => ((RAMSerialization.wordBits w).symm (fun j => bs (.inr (i,j)))).val
  ⟨bs (.inl false), val 0, val 1, val 2, val 3, val 4, val 5, bs (.inl true)⟩

/-- Parsing the words of a canonical bit assignment recovers all of its fields. -/
theorem fieldsOfBits_packBits {m g n : ℕ} (t : GrammarLabel (Fin m × Bool) (Fin g) n) :
    fieldsOfBits (packBits t) = pack t := by
  simp only [fieldsOfBits, packBits, Equiv.symm_apply_apply]
  rfl

/-- Reading an indexed numerical field recovers its word value. -/
theorem word_fieldsOfBits {w : ℕ} (bs : BitSlot w → Bool) (i : Fin 6) :
    (fieldsOfBits bs).word i =
      ((RAMSerialization.wordBits w).symm (fun j => bs (.inr (i,j)))).val := by
  fin_cases i <;> rfl

/-- A guessed bit assignment is accepted as the given label precisely when it equals
that label's one canonical encoding. Thus guessing the padding adds no multiplicity. -/
theorem unpack_bits_iff {m g n : ℕ} {t : GrammarLabel (Fin m × Bool) (Fin g) n}
    {bs : BitSlot (recordWidth m g n) → Bool} :
    unpack m g n (fieldsOfBits bs) = some t ↔ bs = packBits t := by
  rw [unpack_eq_some_iff]
  constructor
  · intro h
    funext s
    rcases s with tag | ⟨i,j⟩
    · cases tag with
      | false => exact congrArg Fields.binary h
      | true => exact congrArg Fields.bit h
    · have e : (RAMSerialization.wordBits _).symm (fun j => bs (.inr (i,j))) =
          (⟨(pack t).word i, word_lt t i⟩ : Fin (2^recordWidth m g n)) :=
        Fin.ext ((word_fieldsOfBits bs i).symm.trans (congrArg (fun a : Fields => a.word i) h))
      exact ((congrFun ((RAMSerialization.wordBits _).apply_symm_apply
        (fun j => bs (.inr (i,j)))) j).symm).trans (congrFun (congrArg (RAMSerialization.wordBits _) e) j)
  · rintro rfl
    exact fieldsOfBits_packBits t

/-- Distinct table labels have distinct fixed-width bit patterns. -/
theorem packBits_injective {m g n : ℕ} : Function.Injective (packBits (m := m) (g := g) (n := n)) := by
  intro a b he
  have ha := (unpack_bits_iff (t := a) (bs := packBits a)).mpr rfl
  have hb := (unpack_bits_iff (t := b) (bs := packBits a)).mpr he
  exact Option.some.inj (ha.symm.trans hb)

end ParseRecords

end BorderVNP
end Computability
end OAI
