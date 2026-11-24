import OAI.Computability.VPVNP.RAMTapeSortDecision
import OAI.Computability.VPVNP.RAMTapeSortRowAddress
import OAI.Computability.VPVNP.RAMSortCost

/-! # The decoded value and validity of an addressed sorting record

The physical comparator works on five arbitrary words, while the word-work
replay uses the checked bit decoder. Re-encoding the parsed slot characterizes
precisely when that decoder returns a record, including the all-zero empty slot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortReplay

open BurstRAM RAMMemory RAMSort RAMSerialization RAMBoundary

variable {h d w : ℕ}

/-- Parsing a raw five-word slot and re-encoding it reproduces every word, including the
all-zero encoding of an empty slot. -/
abbrev Canonical (hw : 2 ≤ w) (a : RawSlot w) := (recordFormat hw).words ((recordFormat hw).parse a) = a

theorem canonical_iff (hw : 2 ≤ w) (a : RawSlot w) :
    Canonical hw a ↔ ∃ r, (recordFormat hw).words r = a := by
  constructor
  · exact fun h => ⟨_,h⟩
  · rintro ⟨r, rfl⟩
    simp [Canonical, Format.parse_words]

theorem canonical_observed (hw : 2 ≤ w) (a : RawSlot w) :
    Sorter.canonical (fun i ↦ SuccessorTags.Tag.ofNat (a i).val) = true ↔ Canonical hw a :=
  (Sorter.canonical_iff hw a).trans (canonical_iff hw a).symm

theorem parsed_eq_iff (hw : 2 ≤ w) {a b : RawSlot w} (ha : Canonical hw a) (hb : Canonical hw b) :
    parsedSlot hw a = parsedSlot hw b ↔ a = b := by
  refine ⟨?_, fun h => h ▸ rfl⟩
  intro he
  have hh := congrArg OrderedSlot.record he
  change ((recordFormat hw).parse a).map WordRecord.record =
    ((recordFormat hw).parse b).map WordRecord.record at hh
  have inj : Function.Injective (Option.map (WordRecord.record (w := w))) := by
    intro r t ht
    cases r <;> cases t <;> simp_all [WordRecord.record_injective.eq_iff]
  exact ha.symm.trans ((congrArg (recordFormat hw).words (inj hh)).trans hb)

/-- The raw five words at the exact bit address used by the checked RAM scan. -/
def fieldWords (w : ℕ) (incident : ℕ → Bool) (s : Stage (h+d)) (dir : Fin 2) (i : Fin (2^h)) :
    RawSlot w :=
  (arrayBits 5 w).symm (fun bit => incident ((fieldStart h w s.phase s.stride dir.val i.val).eval + bit.val))

theorem readSlot_eq (hw : 2 ≤ w) (incident : ℕ → Bool) (s : Stage (h+d)) (dir : Fin 2)
    (i : Fin (2^h)) :
    (readSlot hw incident s dir i).1 =
      if Canonical hw (fieldWords w incident s dir i) then some (parsedSlot hw (fieldWords w incident s dir i))
      else none := by
  let bits := fun bit : Fin (5*w) => incident ((fieldStart h w s.phase s.stride dir.val i.val).eval + bit.val)
  let a := (arrayBits 5 w).symm bits
  have he : (recordFormat hw).encode ((recordFormat hw).parse a) = bits ↔ Canonical hw a :=
    ((arrayBits 5 w).eq_symm_apply).symm
  simp only [readSlot, decodeSlot_eq, Format.decode]
  change (if (recordFormat hw).encode ((recordFormat hw).parse a) = bits then some ((recordFormat hw).parse a)
      else none).map _ = if Canonical hw a then some (parsedSlot hw a) else none
  simp only [he]
  split <;> rfl

/-- The integer address comparison and phase-direction test in the checked
replay give the same bit as the finite row-address routine. -/
theorem orientation (g a j : ℕ) :
    (decide (g < partner j g) == phaseDirection a g) = (g.testBit j == g.testBit a) := by
  have he : phaseDirection a g = !(g.testBit a) := by
    simp only [phaseDirection, Nat.testBit_eq_decide_div_mod_eq, ← decide_not, decide_eq_decide]
    have := Nat.mod_lt (g / 2^a) (by decide : 0 < 2)
    omega
  have hd : decide (g < partner j g) = decide (g.testBit j = false) := decide_eq_decide.mpr (SortRowAddress.lt_partner_iff g j)
  rw [he, hd]
  cases g.testBit j <;> cases g.testBit a <;> decide

end RAMTape.SortReplay

end VPVNP
end Computability
end OAI
