import OAI.Computability.BorderVNP.TeamTapeSortingRecords
import OAI.Computability.VPVNP.RAMTapeSitePostClock
import OAI.Computability.VPVNP.RAMTapeRoutineTotalPorts
import OAI.Computability.VPVNP.EvaluatorRoutineFrame

/-! # Raw exchange assignments for the team memory sort

One five-word message crosses each list boundary. On every sorting layer one binary
block travels from each source to its XOR partner. The old parser's three auxiliary
control words are filled with a fixed bit pattern and are absent from the assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeSorting

open VPVNP BurstRAM RAMLayout RAMMemory RAMSerialization RAMSort RAMTape RAMBoundary

/-- Raw shared link assignments. A raw slot is five fixed-width words, equivalently
`5*w` independently supplied bits via `RAMSerialization.arrayBits`. -/
abbrev Fields (d e w : ℕ) :=
  (Fin (2^d - 1) → RawSlot w) × (Layer d → Word d → Fin (blockBits (2^e) w) → Bool)

variable {d e w : ℕ}

/-- Fixed-width input array read by the existing named-stack post-pass. -/
def embedFields (a : Fields d e w) : SendArrays d (2^e) w :=
  (fun i => arrayBits 8 w (Fin.append (fun _ : Fin 3 => 0) (a.1 i)), a.2)

/-- Predecessor payload, clamped to zero before the first block. -/
def incoming (a : Fields d e w) (v : Word d) : RawSlot w :=
  if h : 0 < v.val then a.1 ⟨v.val-1, by have := v.isLt; omega⟩ else fun _ => 0

/-- Outgoing last-slot payload, clamped to zero after the last block. -/
def outgoing (a : Fields d e w) (v : Word d) : RawSlot w :=
  if h : v.val+1 < 2^d then a.1 ⟨v.val, by omega⟩ else fun _ => 0

/-- Parsed memory links at the physical sorting and boundary positions. -/
def memory (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : Fields d e w) :=
  (unpackMessages (parseMessages hw hc (embedFields a))).memory

private theorem parseBoundary (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : Fields d e w)
    (i : Fin (2^d-1)) :
    (memory hw hc a).lastRecords i = (parsedSlot hw (a.1 i)).record := by
  change ((successorFormat hw hc).parse ((arrayBits 8 w).symm ((embedFields a).1 i))).lastRecord.map _ = _
  simp [embedFields, successorFormat, parsedSlot]

/-- Raw boundary positions decode to the successor and predecessor in the shared assignment. -/
theorem parsed_edges (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : Fields d e w) (v : Word d) :
    (parsedSlot hw (incoming a v)).record = RAMBoundary.receive (memory hw hc a).lastRecords v ∧
    (parsedSlot hw (outgoing a v)).record = RAMBoundary.outgoing (memory hw hc a).lastRecords v := by
  constructor
  · rcases v with ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ i =>
      change _ = (memory hw hc a).lastRecords ⟨i, by omega⟩
      rw [parseBoundary]
      simp [incoming]
  · by_cases hv : v.val+1 < 2^d
    · simp [outgoing, RAMBoundary.outgoing, hv, parseBoundary]
    · simp [outgoing, RAMBoundary.outgoing, hv]; rfl

/-- A raw assignment passes all format checks at this site. The two endpoint checks
include empty records with nonzero payload or unrecognized tags. -/
def FormatAt (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : Fields d e w) (v : Word d) : Prop :=
  SortReplay.Canonical hw (incoming a v) ∧ SortReplay.Canonical hw (outgoing a v) ∧
    SortCanonical hw hc (embedFields a) v

/-- Encode all typed messages, using the exact format of a boundary record and of a
sorting block, with every empty slot canonically zero. -/
def encodeFields (hw : 2 ≤ w) (m : MemoryMessages (2+e) d w) (hf : m.FitsWord) : Fields d e w :=
  (fun i => (recordFormat hw).words (narrowSlot (m.lastRecords i) (hf.2 i)),
   fun l v => (blockFormat (2^e) hw).encode (fun i =>
     narrowSlot (m.sortSends l v ((recordPosition e).symm i)).record (hf.1 l v _)))

/-- Packing and parsing recover both families of messages exactly. -/
theorem memory_encode (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (m : MemoryMessages (2+e) d w) (hf : m.FitsWord) :
    memory hw hc (encodeFields hw m hf) = m := by
  apply MemoryMessages.ext
  · funext l v i
    apply congrArg OrderedSlot.mk
    change (((blockFormat (2^e) hw).parse ((arrayBits _ w).symm
      ((encodeFields hw m hf).2 l v))) (recordPosition e i)).map _ = _
    simp only [encodeFields, Format.encode, Equiv.symm_apply_apply, Format.parse_words,
      Equiv.symm_apply_apply, widen_narrowSlot]
  · funext i
    rw [parseBoundary]
    simp only [parsedSlot, encodeFields, Format.parse_words, widen_narrowSlot]

/-- Every true typed exchange has a well-formed encoding at every owner and peer. -/
theorem format_encode (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (m : MemoryMessages (2+e) d w) (hf : m.FitsWord) (v : Word d) :
    FormatAt hw hc (encodeFields hw m hf) v := by
  constructor
  · by_cases hv : 0 < v.val
    · simp [SortReplay.Canonical, incoming, hv, encodeFields, Format.parse_words]
    · simp only [incoming, dite_eq_right hv]; rfl
  constructor
  · by_cases hv : v.val+1 < 2^d
    · simp [SortReplay.Canonical, outgoing, hv, encodeFields, Format.parse_words]
    · simp only [outgoing, dite_eq_right hv]; rfl
  · intro l
    simp only [messageBits, parseMessages, embedFields, encodeFields, Format.encode,
      Equiv.symm_apply_apply, Format.parse_words]
    exact ⟨rfl, rfl⟩

/-- Sender canonicality and equality of the parsed data determine every individual link
bit. In particular a malformed last-slot message cannot create a second transcript. -/
theorem fields_eq_encode (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (a : Fields d e w) (m : MemoryMessages (2+e) d w) (hf : m.FitsWord)
    (ha : ∀ v, FormatAt hw hc a v) (hm : memory hw hc a = m) : a = encodeFields hw m hf := by
  subst m
  apply Prod.ext
  · funext i
    have hi := i.isLt
    let v : Word d := ⟨i.val, by omega⟩
    have ho : outgoing a v = a.1 i := by simp [outgoing, v, show i.val+1 < 2^d by omega]
    have hcan := (ha v).2.1
    rw [ho] at hcan
    have hword := parseBoundary hw hc a i
    let parsed := (recordFormat hw).parse (a.1 i)
    have hparsed : narrowSlot ((memory hw hc a).lastRecords i) (hf.2 i) = parsed := by
      have he := widen_narrowSlot ((memory hw hc a).lastRecords i) (hf.2 i)
      exact (Option.map_injective WordRecord.record_injective) (he.trans hword)
    change a.1 i = (recordFormat hw).words _
    exact hcan.symm.trans (congrArg (recordFormat hw).words hparsed.symm)
  · funext l v
    have hcan := ((ha v).2.2 l).1
    change a.2 l v = (blockFormat (2^e) hw).encode _ at hcan ⊢
    rw [hcan]
    apply congrArg (blockFormat (2^e) hw).encode
    funext i
    apply Option.map_injective WordRecord.record_injective
    rw [widen_narrowSlot]
    simp [memory, unpackMessages]

end TeamTapeSorting

end BorderVNP
end Computability
end OAI
