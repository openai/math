import OAI.Hierarchy.DescentPhysicalSheetEntryFrame
import OAI.Hierarchy.DescentPhysicalMixedCapture
import OAI.Hierarchy.DescentPhysicalVenuePredecessor
import OAI.Hierarchy.DescentRecordedPostedPlanes

namespace OAI
/-! # Raw peer values on the original pre-funding operand memory -/
open private Hierarchy.DescentDatedAddressBook.PhysicalReset.peer_page
  Hierarchy.DescentDatedAddressBook.PhysicalReset.peer_end
  from OAI.Hierarchy.DescentPhysicalVenuePredecessor

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedExchange DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "fr" => (v).front
local notation "p" => (fr).peer
local notation "next" => (v).actorEnd b
local notation "old" => (v).issuedScene b u.earlier
local notation "start" => (v).sheetsStart b
local notation "snap" m:arg => ((fr).trunkScene next old u.sceneFits).image m
local notation "inputs" => FinalInputs.predecessor u

theorem captured_operand_peer (ok : u.Ready) {N : ℕ} (R : u.MeasuredChannels N)
    (m : Memory w) (seen : CaptureRoom R m) (h : Fin (p).hosts) (j : Fin 3) :
    u.sheetsResult ok m (((inputs).ranks.neighbor j).base+h.val)=
      (target (R.near h j):Word w) :=by
  let z:=((inputs).ranks.neighbor j).base+h.val
  have small : h.val<2^Nat.clog 2 (p).hosts:=h.isLt.trans_le (Nat.le_pow_clog (by decide) _)
  have page:=Hierarchy.DescentDatedAddressBook.PhysicalReset.peer_page (p) ((fr).peers next) j
  have tip:=Hierarchy.DescentDatedAddressBook.PhysicalReset.peer_end (fr) next
  have below : z<(v).trunkEnd b:=(Nat.add_lt_add_left small _).trans_le (page.trans tip)
  obtain ⟨_,_,_,ab,bc,cd,de,ef,_⟩:=ok.ordered
  have before:=below.trans_le (ab.trans (bc.trans (cd.trans (de.trans ef))))
  have shapes:=(v).sheets_any u.sectors start u.operand b u.degree u.bank u.laws (u.sheetsEntry ok m)
    ok.matched ok.full ok.header ok.original ok.rows ok.width ok.nodes ok.slots ok.rankPorts ok.ranks
    ok.controls ok.placed ok.fields
  have mass:=(v).contactShape.actual ((fr).donorStart next) ((v).trunkEnd b) (old).donor
    u.sceneFits.donor ok.donors ok.mass ok.projectionLanes ok.projectionBlocks (snap m)
  exact (shapes.2.1 z (.inl before)).trans ((u.from_trunk_frame ok m z below).trans
    ((mass.2.2 z (.inl below)).symm.trans (seen.three h j)))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSortedRoster
/-- The three raw entries count a loop exactly when the emitted physical neighborhood includes its source. -/
theorem emitted_self_flag {V : Type} [Fintype V] [DecidableEq V] {H D : ℕ}
    (e : V↪Fin H) (f : Fin H→Fin D→Option (Fin H)) (near : V→Finset V)
    (published : ∀v,present f (e v)=(near v).map e) (v : V) :
    (∀j,f (e v) j≠some (e v)) ↔ v∉near v :=by
  classical
  have found : e v∈present f (e v) ↔ v∈near v:=by rw [published,Finset.mem_map']
  simpa [present] using not_congr found
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
