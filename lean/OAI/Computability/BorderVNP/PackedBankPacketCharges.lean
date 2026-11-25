import OAI.Computability.BorderVNP.PackedBankCharges
import OAI.Computability.BorderVNP.PackedBankPacketBox
import OAI.Computability.BorderVNP.PackedBankPacketProfiles

/-! # Static word counts of the emitted seed-site packets

The shapes used here are the actual frozen record emitters. Their operand
values may vary with the history, multiplicity, and relocation, while their
numbers of words are fixed. A paid site's private factor explicitly includes
all entries of its little-endian truth-table directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCharges

open Crossing CellSparse BankPacket BankCircuit Shortening Shortening.StaticRows Shortening.CombiningStep
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The concrete record-emitting tape and its operand type at each seed site. -/
noncomputable def format (first : Fin D × Bool) : TemplateSite e → Σ I : Type, List (RecordCode I)
  | .inl _ => ⟨SiteInput D e.count,origin m first⟩
  | .inr (.inl _) => ⟨SiteInput D e.count,terminal m⟩
  | .inr (.inr ⟨i,v⟩) =>
    let w := PaidBox.widths (e.net i) v
    ⟨Paid.Input (Fintype.card (PaidBox.Bundle (e.net i) v)) (∑ r,w r), Paid.rows w⟩

/-- Actual one-copy private box-directory fragment. -/
noncomputable def metadata (position : e.Entry → ℕ) : TemplateSite e → List (List Factor)
  | .inl _ | .inr (.inl _) => []
  | .inr (.inr ⟨i,v⟩) => [[PaidBox.tableFactor e position i v]]

/-- The single factor contains its tag, two lengths, the lane addresses, and all
two-to-the-arity gadget positions. Its length is independent of the IDs' values. -/
theorem factor_length (position : e.Entry → ℕ) (i : Fin e.count) (v : (e.net i).Site) :
    (Packet.factor (PaidBox.tableFactor e position i v)).length =
      3 + PaidBox.arity e i v + 2^(PaidBox.arity e i v) := by
  simp [PaidBox.tableFactor,CellBox.factor,CellBox.rows,Packet.factor,Packet.vector,PaidBox.arity]
  omega

private noncomputable def metadataSize : TemplateSite e → ℕ
  | .inl _ | .inr (.inl _) => 1
  | .inr (.inr ⟨i,v⟩) => 2 + (3 + PaidBox.arity e i v + 2^(PaidBox.arity e i v))

/-- Length-prefixed public records and one-copy box metadata at a single site. -/
noncomputable def wordCount (first : Fin D × Bool) (v : TemplateSite e) : ℕ :=
  (tape (format e first v).2).length + metadataSize e v

/-- Equality with the two length-prefixed parts of the private packet wire format,
for every possible setting of the public arithmetic operands. -/
theorem encoded_words (position : e.Entry → ℕ) (first : Fin D × Bool) (v : TemplateSite e)
    (x : (format e first v).1 → ℕ) :
    (Packet.fieldList Packet.record ((format e first v).2.map (RecordCode.read x))).length +
      (Packet.fieldList (Packet.fieldList Packet.factor) (metadata e position v)).length =
        wordCount e first v := by
  rw [← tape_eval, List.length_map,wordCount]
  congr 1
  rcases v with _ | _ | ⟨i,v⟩
  · rfl
  · rfl
  · simp [metadata,metadataSize,Packet.fieldList,factor_length]
    omega

/-- The three frozen record emitters have the exact counts used by the sparse
per-tile estimate, including one whole-cable tie for each fixed incident bundle. -/
theorem row_count (first : Fin D × Bool) (v : TemplateSite e) :
    (format e first v).2.length = sparse e v := by
  rcases v with _ | u | ⟨i,v⟩
  · let x : SiteInput D e.count → ℕ := fun _ => 0
    have h := congrArg List.length (origin_read m x first)
    simpa [format,sparse,allRows,originList_length] using h.trans (by
      simp [allRows,originList_length]; omega)
  · let x : SiteInput D e.count → ℕ := fun _ => 0
    have h := congrArg List.length (terminal_read m x)
    simpa [format,sparse,terminalList_length] using h
  · simp [format,sparse,Paid.rows,PaidBox.arity]
    omega

variable [NeZero D] {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

/-- In any physical output tile, the complete frozen public packets and their
full private one-copy gadget tables use at most a fixed number of words per
physical public record, with no factor from the matched multiplicities. -/
theorem packet_tile_le (prior payload : (output e p bin perm positive first q).layout.Site → ℕ)
    (test : (output e p bin perm positive first q).layout.Site → Prop) :
    testedWidth (Sum.elim (fun _ : p.layout.Site => 0)
      (fun z : Σ _ : A, TemplateSite e => wordCount e first z.2)) test ≤
      (∑ v, wordCount e first v) * localRecords (output e p bin perm positive first q).layout
        false prior payload test :=
  static_tile_le e p bin perm positive first q (wordCount e first) false prior payload test

end Packing.BankCharges

end BorderVNP
end Computability
end OAI
