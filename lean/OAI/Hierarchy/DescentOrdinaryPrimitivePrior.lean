import OAI.Hierarchy.DescentOrdinaryArgumentClippedFrame
import OAI.Hierarchy.DescentOrdinaryInletControls
import OAI.Hierarchy.DescentPhysicalOrdinaryReturn
import OAI.Hierarchy.DescentDatedOrdinaryFinal

namespace OAI
/-! Carry the issued prior role and donor chip banks to the actual ordinary primitive input. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentDatedPriorOperand DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentOrdinaryVenueIngress ProtocolRAM DescentOrdinaryReferenceInputs DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

set_option quotPrecheck false
variable {w} (floor : ℕ) (A : ArgumentEntry v)
    (match_ : A.Match v floor) (src : OriginSources v) (prepare : NativePhase w)
    (donorFit : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (inlet : A.Room v floor w) (gather : (A.directory v floor match_).refs.Room w (v.vectorStart floor))
    (bounds : ∀j f,(src j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (cpu : ∀m,prepare.Runs m ∧ ∀i,i<v.routedStart floor ∨ v.origin.grainBase (v.routedStart floor)≤ i → prepare.image m i=m i)
    (paid : NativePhase w) (charge : Span paid (v.endAddress floor) (v.rasterEnd floor))
    (columns : StageVenueTail.Sources) (survivors : v.ResultRoom floor columns w) (m : Memory w)
local notation "inlet_" => (A.inlet v floor w).image m
local notation "args_" => (v.argumentPhaseAfterSigned floor A match_ src prepare donorFit shape fit wide).image m
local notation "later_" => (v.returnPhase floor columns w survivors).image (paid.image args_)

include gather bounds cpu charge in
theorem primitive_inlet_frame (u : ℕ) (early : u<v.refsStart floor) : later_ u=inlet_ u:=by
  have checked:=v.resolved_any floor (A.directory v floor match_) src prepare (A.chipBank v floor)
    donorFit gather shape fit wide bounds cpu inlet_
  obtain ⟨low,up⟩:=v.mount_order floor
  have «until»:=early.trans_le (low.trans (up.trans ((v.vector_before floor).trans
    ((v.routed_le floor).trans (v.resolver.floor_le _)))))
  have final_:=(v.returnPhase_run floor columns w survivors (paid.image args_)).2 u (.inl («until».trans_le charge.1))
  exact final_.trans (((charge.2 args_).2 u (.inl «until»)).trans (checked.2.1 u (.inl early)))

include gather bounds cpu charge inlet in
theorem primitive_prior (x : Fin A.previous.blocks)
    (value : Fin A.previous.hosts→Fin A.clip.venue.groups→Cell (A.roleLayout v).bits)
    (pos : 0<A.rolePitch) (before : (A.role x).base+(A.role x).size≤v.signedEnd floor)
    (size : A.previous.hosts*chunks A.clip.venue.groups A.rolePitch≤(A.role x).size)
    (actual : Reads (A.role x) value A.rolePitch m) :
    Reads (A.labels v floor x) (DescentOrdinaryHostPad.extend A.clip.venue.hosts value) A.clip.working later_:=by
  obtain ⟨_,_,_,ab,bc⟩:=A.inlet_order v floor
  have cap:=(A.roleLayout v).placed (A.roleStart v floor) (ab.trans_lt (bc.trans_lt inlet.ceiling)) x
  have old:=A.role_before_count v floor m inlet x value pos before size actual
  have frames:=A.inlet_frames v floor m inlet
  apply ArgumentEntry.reads_through old cap.1.2.2 cap.2
  intro u lt
  have atCount:=lt.trans_le ab
  have atRefs : u<v.refsStart floor:=match_.atRefs ▸ atCount.trans_le bc
  have late:=v.primitive_inlet_frame floor A match_ src prepare donorFit shape fit wide gather bounds cpu paid
    charge columns survivors m u atRefs
  exact late.trans (frames.count u atCount)

include gather bounds cpu charge inlet in
theorem primitive_donor (positive : 0<A.clip.panelPitch)
    (parts : Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DescentRawCablePanel.DepotRAM.Parts A.clip.venue.socket)
    (held : Reads A.venue.panel (fun h g=>DescentRawCablePanel.DepotRAM.combine A.clip.venue.socket (parts h g))
      A.clip.panelPitch m) :
    Reads (A.chipBank v floor) (fun h g=>DescentRawCablePanel.DepotRAM.chip A.clip.venue.socket A.clip.venue.socket.cap
      A.clip.venue.profile v.gadget.b A.clip.venue.slots (parts h g)) A.clip.working later_:=by
  have issued:=A.chip_final v floor m inlet positive parts held
  have size : (A.chip v).rows≤(A.chipBank v floor).size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  apply ArgumentEntry.reads_through issued donorFit.2.2 size
  intro u early
  exact v.primitive_inlet_frame floor A match_ src prepare donorFit shape fit wide gather bounds cpu paid charge columns survivors m u early

open DescentPackedColony
include gather bounds cpu charge inlet in
theorem primitive_halo (roster : Fin A.clip.venue.hosts→Fin A.clip.venue.paths→Option (Fin A.clip.venue.hosts))
    (incoming : Mounted (A.ports v floor) roster (A.clippedTape v floor m) A.clip.venue.groups A.clip.working)
    (addresses : Accessible (A.ports v floor) (A.clip.fieldBank (v.signedEnd floor))
      A.clip.venue.hosts A.clip.venue.groups A.clip.working w (A.priorStart v floor)) :
    Mounted (A.ports v floor) roster later_ A.clip.venue.groups A.clip.working:=by
  obtain ⟨_,old,roles,chip,pop⟩:=A.inlet_order v floor
  let f:=A.inlet_frames v floor m inlet
  apply RoleControl.Layout.previous_mounted addresses roster _ incoming
  intro u low
  have toPop:=low.trans_le (old.trans (roles.trans chip))
  have safe : u<v.refsStart floor:=match_.atRefs ▸ toPop.trans_le pop
  have copy:=v.primitive_inlet_frame floor A match_ src prepare donorFit shape fit wide gather bounds cpu paid
    charge columns survivors m u safe
  exact copy.trans ((f.count u toPop).trans (A.clipped_before_count v floor m inlet u low))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
