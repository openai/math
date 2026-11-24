import OAI.Computability.VPVNP.RAMMessageBounds
import OAI.Computability.VPVNP.RAMSerialization
import OAI.Computability.VPVNP.RAMSharedFields
import OAI.Computability.VPVNP.RAMTranscript

/-!
# Parsimonious transcripts over individual shared bits

Lemma 10.1 sums over bits on existing links. Each site parses its received
fields, checks its outgoing fields for canonical encoding, and validates its
local call reports. All accepted typed messages are representable, so replacing
whole messages by their individual shared bits preserves the path count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMMemory RAMLayout RAMSerialization

variable {d e w : ℕ} {C : Type*}

/-- An assignment of one Boolean to every sending endpoint of an existing transcript link. -/
abbrev RawAssignment (d e w : ℕ) := SharedBit d (2 ^ e) w → Bool

/-- The sorting proof numbers each site block by its logarithmic length. -/
def recordPosition (e : ℕ) : Fin (2 ^ (2 + e)) ≃ Fin (4 * 2 ^ e) :=
  finCongr (by rw [pow_add]; rfl)

/-- Word-bounded messages with exactly the fields present in the bit layout. -/
abbrev PackedMessages (d e w : ℕ) :=
  (Fin (2 ^ d - 1) → Successor w (2 ^ d * 2 ^ e)) ×
    (Layer d → Fin (2 ^ d) → Fin (4 * 2 ^ e) → Option (WordRecord w))

/-- Convert packed successor words and sorting blocks to chain and memory messages, widening
each present record and retaining its position. -/
def unpackMessages (p : PackedMessages d e w) : Messages d e w where
  chain i := ⟨(p.1 i).cost.val, (p.1 i).state⟩
  memory := ⟨fun l v j ↦ ⟨(p.2 l v (recordPosition e j)).map WordRecord.record⟩,
    fun i ↦ (p.1 i).lastRecord.map WordRecord.record⟩

/-- Each successor cost fits the total site budget, and every record carried by the sorting and
successor links fits the chosen word width. -/
def Messages.FitsWord (m : Messages d e w) : Prop :=
  (∀ j, (m.chain j).cost ≤ 2 ^ d * 2 ^ e) ∧ m.memory.FitsWord

/-- Pack bounded chain costs, states, last records and sorting blocks into the fixed successor
and sorting message formats. -/
def packMessages (m : Messages d e w) (h : m.FitsWord) : PackedMessages d e w :=
  (fun i ↦ ⟨(m.chain i).state, ⟨(m.chain i).cost, Nat.lt_succ_of_le (h.1 i)⟩,
    narrowSlot (m.memory.lastRecords i) (h.2.2 i)⟩,
    fun l v j ↦ narrowSlot (m.memory.sortSends l v ((recordPosition e).symm j)).record (h.2.1 l v _))

theorem unpack_pack (m : Messages d e w) (h : m.FitsWord) :
    unpackMessages (packMessages m h) = m := by
  apply Messages.ext
  · rfl
  · apply MemoryMessages.ext
    · funext l v j
      apply congrArg OrderedSlot.mk
      simp [packMessages]
    · funext j
      exact widen_narrowSlot _ _

private theorem narrow_widen (r : Option (WordRecord w)) (h) :
    narrowSlot (r.map WordRecord.record) h = r := by
  cases r with
  | none => rfl
  | some r => cases r; rfl

private theorem pack_unpack (p : PackedMessages d e w) (h) :
    packMessages (unpackMessages p) h = p := by
  apply Prod.ext
  · funext i
    change Successor.mk (p.1 i).state (p.1 i).cost _ = p.1 i
    rw [show narrowSlot ((unpackMessages p).memory.lastRecords i) (h.2.2 i) =
      (p.1 i).lastRecord from narrow_widen _ _]
  · funext l v j
    simp [packMessages, unpackMessages, narrow_widen]

theorem validators_fitWord (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    {m : Messages d e w} {reports : Fin (2 ^ d) → List (Report w)} (hword : 2 ^ d * 2 ^ e < 2 ^ w)
    (h : ∀ v, Validator P fuel initial header m v (reports v)) : m.FitsWord := by
  obtain ⟨hs, hm, _⟩ := (validators_iff ..).mp h
  exact ⟨sitesPass_wire_cost hs, hm ▸ actualMemoryMessages_fitsWord header
    (successor_sound (Nat.two_pow_pos d) hs).2.2.1 hword⟩

/-- Encode each outgoing message independently. -/
def messageBits (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (p : PackedMessages d e w) :
    SendArrays d (2 ^ e) w :=
  (fun i ↦ (successorFormat hw hc).encode (p.1 i),
    fun l v ↦ (blockFormat (2 ^ e) hw).encode (p.2 l v))

/-- Parsing uses the fixed length of each field. Malformed patterns have a
candidate parse but fail the sender's canonicality check below. -/
def parseMessages (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (b : SendArrays d (2 ^ e) w) :
    PackedMessages d e w :=
  (fun i ↦ (successorFormat hw hc).parse ((arrayBits 8 w).symm (b.1 i)),
    fun l v ↦ (blockFormat (2 ^ e) hw).parse ((arrayBits _ w).symm (b.2 l v)))

@[simp] theorem parse_messageBits (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w)
    (p : PackedMessages d e w) : parseMessages hw hc (messageBits hw hc p) = p := by
  simp [parseMessages, messageBits, Format.encode, Format.parse_words]

/-- One successor-send check when that edge exists, and one send check for
each cross-site layer. Both sides inspect only the fields at the specified site. -/
def OutgoingOK (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (b : SendArrays d (2 ^ e) w)
    (v : Fin (2 ^ d)) : Prop :=
  let a := messageBits hw hc (parseMessages hw hc b)
  (if h : v.val + 1 < 2 ^ d then
    b.1 ⟨v.val, by omega⟩ = a.1 ⟨v.val, by omega⟩ else True) ∧ ∀ l, b.2 l v = a.2 l v

private theorem outgoingOK_iff (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (b : SendArrays d (2 ^ e) w) :
    (∀ v, OutgoingOK hw hc b v) ↔ b = messageBits hw hc (parseMessages hw hc b) := by
  constructor
  · intro h
    apply Prod.ext
    · funext j
      have hj := j.isLt
      let v : Fin (2 ^ d) := ⟨j.val, by omega⟩
      have he := (h v).1
      simpa [v, show j.val + 1 < 2 ^ d by omega] using he
    · funext l v
      exact (h v).2 l
  · intro h v
    unfold OutgoingOK
    constructor
    · split
      · exact congrFun (congrArg Prod.fst h) _
      · trivial
    · intro l
      exact congrFun (congrFun (congrArg Prod.snd h) l) v

/-- Check the incoming predecessor field when present and the incoming
sorting blocks at their XOR partners. These checks reject malformed receives
even when evaluating a single site on an arbitrary incident bit pattern. -/
def IncomingOK (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (b : SendArrays d (2 ^ e) w)
    (v : Fin (2 ^ d)) : Prop :=
  let a := messageBits hw hc (parseMessages hw hc b)
  (if h : 0 < v.val then
    b.1 ⟨v.val - 1, by have := v.isLt; omega⟩ = a.1 ⟨v.val - 1, by have := v.isLt; omega⟩
   else True) ∧ ∀ l, b.2 l (l.partner v) = a.2 l (l.partner v)

theorem incomingOK_messageBits (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w)
    (p : PackedMessages d e w) (v : Fin (2 ^ d)) : IncomingOK hw hc (messageBits hw hc p) v := by
  simp [IncomingOK]

/-- The site validator applied to raw link bits. Missing end fields carry
zero by construction of the layout, and genuine fields use their unique source. -/
def BitValidator (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (bits : RawAssignment d e w)
    (v : Fin (2 ^ d)) (rs : List (Report w)) : Prop :=
  let arrays := sendArraysEquiv d (2 ^ e) w bits
  (OutgoingOK hw hc arrays v ∧ IncomingOK hw hc arrays v) ∧
    Validator P fuel initial header (unpackMessages (parseMessages hw hc arrays)) v rs

/-- Shared-bit assignments together with a list of local call reports at each site, subject to
every site's bit validator. -/
abbrev BitJointPaths (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) :=
  {t : RawAssignment d e w × (Fin (2 ^ d) → List (Report w)) //
    ∀ v, BitValidator P fuel initial header hw hc t.1 v (t.2 v)}

/-- The exact bijection between accepted joint transcripts in their typed and
bit-level forms. In particular padding and clamped fields add no choices. -/
def jointBitEquiv (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) :
    TypedJointPaths P fuel initial header d e ≃ BitJointPaths P fuel initial header hw hc where
  toFun t :=
    let h := validators_fitWord P fuel initial header hc t.property
    let a := messageBits hw hc (packMessages t.val.1 h)
    ⟨⟨(sendArraysEquiv d (2 ^ e) w).symm a, t.val.2⟩, by
      intro v
      simp only [BitValidator, Equiv.apply_symm_apply, a, parse_messageBits, unpack_pack]
      exact ⟨⟨(outgoingOK_iff ..).mpr (by simp) v, incomingOK_messageBits ..⟩, t.property v⟩⟩
  invFun t := ⟨⟨unpackMessages (parseMessages hw hc (sendArraysEquiv d (2 ^ e) w t.val.1)),
    t.val.2⟩, fun v ↦ (t.property v).2⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · simp [unpack_pack]
    · rfl
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · apply (sendArraysEquiv d (2 ^ e) w).injective
      have hout := (outgoingOK_iff hw hc _).mp (fun v ↦ (t.property v).1.1)
      simpa [pack_unpack] using hout.symm
    · rfl

/-- Lemma 10.1's parsimonious correspondence for the exact shared-bit layout. -/
noncomputable def bitTranscriptEquiv (P : Program w C) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) :
    ActualPaths P fuel initial (initialMemory (2^d) header) (withinCaps (2^d) (2^e)) ≃
      BitJointPaths P fuel initial header hw hc :=
  (transcriptEquiv ..).trans (jointBitEquiv ..)

end BurstRAM

end VPVNP
end Computability
end OAI
