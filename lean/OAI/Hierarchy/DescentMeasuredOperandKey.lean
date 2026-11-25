import OAI.Hierarchy.DescentResetStemHostRender
import OAI.Hierarchy.DescentFallbackItemSelect
import OAI.Hierarchy.DescentPhysicalRotorEntries

namespace OAI
/-! # The chronological source coordinate in a public operand row -/
namespace Hierarchy.DescentMeasuredOperandKey
open DescentSIMDLookup DescentFallbackItemSelect DescentResetStemCompactOrder DescentResetStemWord
open DescentSixParty DescentCompiler DescentColonies DescentGL DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open scoped Classical Fin.CommRing
noncomputable section

/-- All three coordinates use words stored in the original signed packet, the
host's charged roster correction, and the two old donor digits. -/
def key {field : ℕ} (degree cap fineBits : ℕ) (side : Bool) (original host group fine : Cell field) : Key :=
  let chip:=DescentSignedCableCodec.decode degree cap (original.val:Cell (DescentSignedCableCodec.width degree cap))
  let actor:=effective degree cap side original host
  ⟨(group.val*(degree+2)+actor)*2^fineBits+fine.val,
    chip.elim 0 (fun z=>z.sourceWire.val),chip.elim 0 (fun z=>z.within.val)⟩

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
    {groups d k m c i field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε (Fin groups) V k) (S : AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (basis : Layout m) (fits : c≤ m)
    (native : W.graph.Edge↪ℕ) (grp : Fin groups↪ℕ) (vertex : V↪Fin (Fintype.card V))
set_option quotPrecheck false in
local notation "chipAt" => fun (s : Bool) (e : Grain A) => GroupStage.cableChip A S ready native grp vertex s e
set_option quotPrecheck false in
local notation "siteAt" => fun (s : Bool) (e : Grain A) => (A.pos (endSite A s e)).2
set_option quotPrecheck false in
local notation "sourceAt" => fun (e : Grain A) => W.graph.src (e : Grain A).1

/-- At an occupied end, the saved signed fields recover the original outgoing
cable and grain; reversing the end uses its real compact neighbor rank. -/
theorem key_at (side : Bool) (e : Grain A) (v : V) (hi : Block c)
    (original host group fine : Cell field) (located : siteAt side e=v)
    (stored : original.val=(DescentSignedCableCodec.encode (some (chipAt side e))).val)
    (heard : host.val=hostCode (compress (hostDomain A vertex v) (vertex v).val) (decide (v∉A.near v)))
    (numbered : group.val=compress (groupDomain digits basis fits v hi) (A.pos (sourceAt e)).1.val)
    (subcell : fine.val=(A.block (sourceAt e)).val) :
    key A.degree A.cap k side original host group fine=
      ⟨sourceDigit A digits basis fits vertex v hi e,
        (outgoing A native S ready ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩).val,e.2.val⟩ := by
  subst v
  have castWord : (original.val:Cell (DescentSignedCableCodec.width A.degree A.cap))=
      DescentSignedCableCodec.encode (some (chipAt side e)) := by
    rw [stored]
    exact Fin.ext (Nat.mod_eq_of_lt (DescentSignedCableCodec.encode (some (chipAt side e))).isLt)
  have actor:=(effective_read A.degree A.cap side (chipAt side e) original host _ _ stored heard).trans
    (source_halo A native S ready grp vertex side e)
  obtain ⟨cable,grain⟩:=GroupStage.chip_source A S ready native grp vertex e side
  simp only [key,castWord,DescentSignedCableCodec.decode_encode,Option.elim_some,actor,numbered,subcell,cable,grain,
    sourceDigit]

set_option quotPrecheck false in
local notation "location" => fun (s : Bool) (e : Grain A) => localAddress A native S ready digits basis (c:=c) s e
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank grp (vertex.trans Fin.valEmbedding))

/-- Locate the old signed chip using the old donor row and the elected signed slot. -/
theorem signed_at (side : Bool) (e : Grain A) (v : V) (hi : Block c)
    (located : Located A digits basis v hi side e) :
    signedPanel A native S ready names (donor digits basis fits v hi (location side e).1)
      (location side e).2=some (chipAt side e) := by
  have lv : (port A side e).1.1.2=v := by rw [port_fst];exact located.1
  have lh : group c (rearrange basis (oldBlock digits (port A side e).1))=hi.val := by
    rw [port_fst];exact located.2
  apply GroupStage.chip_at
  apply (atSlot_iff A native S ready ..).mpr
  simp only [localAddress,DescentIssuedFallbackPanel.address,donor_locates digits basis fits _ v hi lv lh]

/-- The signs in the two prepared packets use the original cable codec. Coarser
or padded host identifiers do not affect the measured chronological key. -/
theorem key_in_packet {H n r : ℕ} (name : V↪Fin H) (own : Fin H→Block c→Fin (2^(m-c))→ℕ)
    (roster : Fin H→Fin A.degree→Option (Fin H)) (marks : Fin H→Block c→Fin (2^(m-c))→
      Fin (2*A.cap)→Option (Live A.degree A.cap)) (ranks : Fin H→Fin (DescentSharedBookScan.width r (2^n) A.degree)→ℕ)
    (reached : ∀v hi x j,marks (name v) hi x j=signedPanel A native S ready names (donor digits basis fits v hi x) j)
    (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)
    (side : Bool) (e : Grain A) (v : V) (hi : Block c) (located : Located A digits basis v hi side e)
    (host groupWord fine : Cell field)
    (heard : host.val=hostCode (compress (hostDomain A vertex v) (vertex v).val) (decide (v∉A.near v)))
    (numbered : groupWord.val=compress (groupDomain digits basis fits v hi) (A.pos (sourceAt e)).1.val)
    (subcell : fine.val=(A.block (sourceAt e)).val) :
    key A.degree A.cap k side
      (DescentFallbackPeriod.inputs (n:=n) (r:=r) (field:=field) own roster marks ranks (name v) hi
        (.inr (.inl (location side e)))) host groupWord fine=
      ⟨sourceDigit A digits basis fits vertex v hi e,
        (outgoing A native S ready ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩).val,e.2.val⟩ := by
  apply key_at A S ready digits basis fits native grp vertex side e v hi _ _ _ _ located.1 _ heard numbered subcell
  change (((DescentSignedCableCodec.encode (marks (name v) hi (location side e).1 (location side e).2)).val:Cell field)).val=_
  rw [reached,signed_at A S ready digits basis fits native grp vertex side e v hi located]
  exact Fin.val_cast_of_lt ((DescentSignedCableCodec.encode (some (chipAt side e))).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) signBits))

end
end Hierarchy.DescentMeasuredOperandKey

end OAI
