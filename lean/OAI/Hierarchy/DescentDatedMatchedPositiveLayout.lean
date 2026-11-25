import OAI.Hierarchy.DescentDatedObservationAccepted
import OAI.Hierarchy.DescentPackedOrdinaryRotation
import OAI.Hierarchy.DescentDatedObservedWords

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
open DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch
open DescentSixParty DescentSIMDLookup DescentColonies DescentPackedColony DescentKernelHistory.BitDescription
open DescentTerminalEpochDecoder DescentPackedProfileWindow DescentTerminalEpochChart DescentPackedProfileArchive
open DescentPackedProfileWide DescentGroupPeerOrder DescentStageEdgeReceipt
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentSixParty.StarKeys
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (input : Dated.Operands) (floor : ℕ)
local notation "r" => v.prior
local notation "A" => v.prior.placement
local notation "a" => v.area
local notation "H" => 2^v.level
local notation "J" => v.schedule.groupCount v.age
local notation "c" => (a).chooser input.roster floor
local notation "rom" => (a).prepareAt input.roster floor
local notation "plan" => (a).matcher input.roster floor
local notation "M" => (a).lanesAt
local notation "e" => (Equiv.refl (Fin J))
local notation "sh" => (a).shapeAt
local notation "native" => (r).order.trans Fin.valEmbedding
local notation "measure" => (⟨(A).wire,(A).z,(A).hist⟩ : Dated.Measures)

variable (hv : Fintype.card v.prior.V ≤ 2^v.level)
local notation "names" => GroupStage.plane v.hostNumbers hv
local notation "rank" => groupRank ((e).toEmbedding.trans Fin.valEmbedding) ((names).trans Fin.valEmbedding)
local notation "rs" => (fun (h : Fin H) (j : Fin (A).degree)=>(r).venueRoster hv h (Fin.cast (r).branch j))
local notation "old" => input.ports (A).degree
local notation "top" => (plan).layout.topology
local notation "sel" => (a).selected v.gadget (A).fieldBits input measure
local notation "time_" => (a).selectedTicks v.gadget (A).fieldBits input measure
local notation "home" => scanHomeAt v.nonnegative (A).stage
local notation "color" => scanColorAt v.nonnegative (A).stage
variable {w : ℕ} {Pin : Type} (m : Memory w) (choice : (v.prior.placement.stage.result v.nonnegative).Choice)
    (entry : Source Pin) (z : Pin→Bool) (ext : DescentTerminalEpochBits.width entry.C ≤ v.area.shapeAt.digit)

local notation "nRows" => (a).batch
local notation "tag" => (c).shelves (A).degree v.k v.bitsPerField M
local notation "firstTable" => LayoutSum.Finish.first (plan).layout.topology (plan).layout.out nRows
local notation "flagEnd" => (a).flagEnd input.roster floor
local notation "rotEnd" => (a).rotationEnd input.roster floor
local notation "saved" => fun n : ℕ=>((n<floor ∨ (plan).endAddr≤n) ∧
  (n<firstTable ∨ flagEnd≤n)) ∧ (n<flagEnd ∨ rotEnd≤n)
local notation "cpu" => (a).nativePhase v.gadget (A).fieldBits input measure w floor

theorem matcher_selectors_before : max (tag).mu (tag).paint<firstTable :=by
  have before : max (tag).mu (tag).paint<(a).winnerEnd input.roster floor:=by
    change max (Phase.Arena.seedWork (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth+3*(c).chart.page+
      (2^v.k-1-1)) (Phase.Arena.colorWork (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth+
      3*(c).chart.page+(2^(v.k+1)-1))<Phase.Arena.endAt (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth+_
    unfold Phase.Arena.endAt Phase.Arena.colorWork Phase.Arena.selected
    have positive := Nat.two_pow_pos v.k
    omega
  have order := (a).subphase_order input floor
  have pads : nRows≤ (SixBirths.tapeBank (plan).layout.out nRows).size:=Nat.le_pow_clog (by decide) _
  have stop : (plan).endAddr≤ firstTable:=(Nat.add_le_add_left pads _).trans (le_max_right ..)
  exact before.trans_le (order.2.1.trans (order.2.2.1.trans stop))

/-- The accepted original profile and the three successive executable programs
determine the post-rotation layout on the actual native matcher's output. -/
theorem matched_layout_of_observation (safe : (a).Space input w floor)
    (seen : v.reachedReport input floor hv m choice entry z ext)
    (hit : ∀i,(wideCell entry.pin z (sh).digit ext i).val=
      profileAt (inputNumber v.nonnegative A (e).toEmbedding names)
        ((scannedRows v.nonnegative (A).stage).profile choice) i)
    (named : (A).SiteNamed rank)
    (budget : Fintype.card (NativePair v.world.graph v.world.core home color (A).cap)*
      (v.gadget.C+8+8*v.gadget.k)<2^w) :
    LayoutReportAt A native v.schedule (r).valid v.nonnegative e v.hostNumbers hv c v.bitsPerField
      v.payload v.unit v.profile v.seats rom old choice rs m (cpu safe).program (cpu safe).ticks
      saved ((cpu safe).image m) :=by
  have early:=v.matcher_selectors_before input floor
  have accepted:=reachedReport.accept v input floor hv m choice entry z ext seen hit
  have width : SixBirths.width sh M≤w:=
    (LayoutSum.Finish.width_le sh M v.unit v.payload safe.birthWidth
      (by
        change v.unit * lanes v.payload v.unit ≤ v.payload / 2
        rw [Nat.mul_comm]
        exact lanes_fit v.payload v.unit)).trans
      ((Nat.div_le_self ..).trans safe.embed)
  have fromTable : firstTable≤flagEnd:=by
    let born:=LayoutSum.Finish.births sh M (plan).layout.topology (plan).layout.out nRows
    let area:=LayoutSum.Finish.base sh M (plan).layout.topology (plan).layout.out nRows
    have h₀:firstTable≤born:=Nat.le_add_right ..
    have h₁:born≤area:=Nat.le_add_right ..
    have h₂:area≤flagEnd:=by change _≤area+2*_+4*nRows+2+1; omega
    exact h₀.trans (h₁.trans h₂)
  have roof : flagEnd≤rotEnd:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have laid:=OrdinaryReport.layout A native v.schedule (r).valid v.nonnegative e v.hostNumbers hv c v.bitsPerField
    v.payload v.unit v.profile v.seats rom old choice rs m _ _ _ accepted named early width
    (roof.trans_lt safe.endAddress) budget
  obtain ⟨out,report,_⟩:=LayoutReport.rotation A native v.schedule (r).valid v.nonnegative e v.hostNumbers hv
    c v.bitsPerField v.payload v.unit v.profile v.seats rom old choice rs m _ _ _ laid
    (early.trans_le fromTable) safe.endAddress
  have execution : ((a).program v.gadget (A).fieldBits input measure w floor).Exec m out (cpu safe).ticks:=by
    obtain ⟨_,_,_,run,_⟩:=report
    exact run
  rw [(a).nativePhase_issued v.gadget (A).fieldBits input measure w floor safe m out execution]
  exact report

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
