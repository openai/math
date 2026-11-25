import OAI.Hierarchy.DescentTerminalSuffixFits
import OAI.Hierarchy.DescentTerminalCompiledAdmission
import OAI.Hierarchy.DescentTerminalPacketSlotRAM

namespace OAI
/-! # Stable original and relative ordinals in the compiled terminal prefix -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open Computability.BorderVNP.FragmentBucket
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (S : Shape) (L : Layout)
attribute [local irreducible] Procedure.Exec CheapCode
set_option quotPrecheck false
local notation "counter_" => DescentPackedTerminalExponent.program L.count L.exponent w S.nodes S.batch S.piece
local notation "plan_" => DescentTerminalRowPlan.program (w:=w) L.row S.sites S.terminal.rows
local notation "offsets_" => DescentTerminalSiteOffsets.program L.offset w S.sites
local notation "publish_" => DescentTerminalPacketSlotRAM.program L.homes L.order w S.packets S.sites
local notation "sortFee" => (4+S.packets*(2*(DescentTerminalExteriorPackets.guard L.homes S.sites).work+4))+
  ProtocolRAMEndpointSort.cost S.packets S.sites

def slotted (m : Memory w) := DescentTerminalPacketSlotRAM.after L.order S.packets S.sites (ordered S L m)

def slottedPrefix := (((counter_).seq plan_).seq offsets_).seq publish_

def slottedClocks :=
  DescentPackedPrivateSum.Layout.billed 1 S.nodes S.batch+DescentPrivateExponentRAM.steps L.exponent S.piece+
    DescentTerminalRowPlan.time L.row S.sites S.terminal.rows+DescentTerminalSiteOffsets.time L.offset S.sites+
    (sortFee+(4+S.packets*80))

/-- The packed counter, public offset plan and stable sort are executed once.
Only the final row scan adds a new tariff to the original ordered prefix. -/
theorem slotted_run (m : Memory w) (room : Room S L w) (positive : 0 < w)
    (allocation : L.row.mark.Fixed S.sites (DescentTerminalRowPlan.header L.row S.sites (counted S L m)))
    (slotRoom : slotBase S L+S.packets < 2^w) :
    (slottedPrefix (w:=w) S L).Exec m (slotted S L m) (slottedClocks S L) ∧
      CheapCode (slottedPrefix (w:=w) S L) := by
  have a : (counter_).Exec m (counted S L m)
      (DescentPackedPrivateSum.Layout.billed 1 S.nodes S.batch+DescentPrivateExponentRAM.steps L.exponent S.piece) ∧
      CheapCode counter_ :=
    ⟨@DescentPackedTerminalExponent.run w L.count L.exponent S.nodes S.batch S.piece m room.packed room.scalar,
      @DescentPackedTerminalExponent.cheap L.count L.exponent w S.nodes S.batch S.piece⟩
  have b:=DescentTerminalRowPlan.run L.row S.sites S.terminal.rows (counted S L m) room.plan positive allocation
  have c:=DescentTerminalSiteOffsets.run L.offset S.sites (allocated S L m) room.offset
  have d:=DescentTerminalPacketSlotRAM.run L.homes L.order (rowed S L m) S.sites_pos room.ordering slotRoom
  exact exec_cheap_seq (exec_cheap_seq (exec_cheap_seq a b) c) d

theorem slotted_tariff :
    slottedClocks S L+(4+S.terminal.pool*(2*(DescentTerminalSiteShelves.gather L.directory).work+4))+
      DescentTerminalEmitter.time S.terminal L.emit=clocks S L+(4+80*S.packets) := by
  unfold slottedClocks clocks
  omega

theorem slot_before (m : Memory w) {a : ℕ} (early : a < slotBase S L) : slotted S L m a=ordered S L m a :=
  DescentTerminalPacketSlotRAM.retained L.order S.packets S.sites (ordered S L m) a (Or.inl early)

theorem sorted_before (i : Fin S.packets) : L.order.sorted+i.val < slotBase S L := by
  have hi:=i.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) S.packets)
  change L.order.sorted+i.val < L.order.sorted+2^Nat.clog 2 S.packets+2^Nat.clog 2 S.sites
  exact (Nat.add_lt_add_left hi L.order.sorted).trans_le (Nat.le_add_right _ _)

theorem slotted_reads (m : Memory w) (room : Room S L w) (home : Fin S.packets→Fin S.sites)
    (issued : ∀i,L.homes.read m (i.val:Word w)=((home i).val:Word w))
    (keep : ∀i : Fin S.packets,Protected L (L.homes.base+(i.val:Word w).val%L.homes.size))
    (i : Fin S.packets) :
    let u:=(dest home).symm i
    let s:=home u
    slotted S L m (L.order.sorted+i.val)=(u.val:Word w) ∧
    slotted S L m (slotBase S L+i.val)=(prior home u.val s:Word w) ∧
    (slotted S L m (slotBase S L+i.val)).val < (slotted S L m (L.order.counts+s.val)).val := by
  let u:=(dest home).symm i
  let s:=home u
  have keys (q : Fin S.packets) : L.homes.read (rowed S L m) (q.val:Word w)=((home q).val:Word w) := by
    change rowed S L m _=_
    rw [rowed_preserved S L m room (keep q)]
    exact issued q
  have posted:=DescentTerminalPacketSlotRAM.truthful_slot L.homes L.order (rowed S L m) S.sites_pos
    room.ordering home keys i
  have early : L.order.counts+s.val < slotBase S L := by
    have a:=room.ordering.fits.count_safe;have b:=room.ordering.fits.prefix_safe;have c:=s.isLt
    have tail_ : L.order.sorted ≤ slotBase S L:=by unfold slotBase DescentTerminalPacketSlotRAM.out;omega
    omega
  refine ⟨(slot_before S L m (sorted_before S L i)).trans (ordered_port S L m room home issued keep i),posted.1,?_⟩
  rw [slot_before S L m early]
  exact posted.2

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
