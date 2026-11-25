import OAI.ThreeFlat.Diagonal.TraceSlotOrder
import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Canonical bit serialization for sorting-network slots -/

namespace ThreeFlat.Diagonal.TraceSlots

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization Computability.VPVNP.RAMMemory

variable {w : ℕ}

/-- Seven words in comparison order. Decoding checks every field, including
the initialization flag and all the padding payload, by re-encoding. -/
def slotFormat (hw : 2 ≤ w) : Format w 7 (Option (WordRecord w)) where
  words := fields hw
  parse a :=
    if (a 0).val = 0 then
      let kind := match (a 5).val with
        | 0 => Kind.init
        | 1 => Kind.read
        | _ => Kind.write
      some ⟨kind, a 1, a 6, a 3, a 4⟩
    else none
  parse_words r := by
    cases r with
    | none => rfl
    | some r => cases r with | mk k a v t o => cases k <;> rfl

@[simp] theorem slotFormat_words (hw : 2 ≤ w) (r : Option (WordRecord w)) :
    (slotFormat hw).words r = fields hw r := rfl

@[simp] theorem slotFormat_parse_fields (hw : 2 ≤ w) (r : Option (WordRecord w)) :
    (slotFormat hw).parse (fields hw r) = r := (slotFormat hw).parse_words r

theorem slotFormat_decode_iff (hw : 2 ≤ w) (z : Fin (7*w) → Bool) (r : Option (WordRecord w)) :
    (slotFormat hw).decode z = some r ↔ z = (slotFormat hw).encode r :=
  Format.decode_iff ..

/-- The bit accessed by the Boolean verifier at word offset `j` and bit
offset `i` is the corresponding little-endian bit of the sorting key. -/
theorem slotFormat_encode_at (hw : 2 ≤ w) (r : Option (WordRecord w)) (j : Fin 7) (i : Fin w) :
    (slotFormat hw).encode r (finProdFinEquiv (j,i)) = TraceWords.bits (fields hw r j) i :=
  (arrayBits_at (fields hw r) j i).trans (Computability.VPVNP.LiveHeader.testBit_wordBits _ _).symm

end ThreeFlat.Diagonal.TraceSlots

end OAI
