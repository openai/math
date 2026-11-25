import OAI.Hierarchy.DescentDatePortActorRoom
import OAI.Hierarchy.DescentDatePortHeaderRoom
import OAI.Hierarchy.DescentSeedRosterAccess

namespace OAI
/-! The finite public range of all three rank and chunk directories at each date. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentPackedColony DescentDatedAddressBook DescentInitialHost DescentCompiler DescentDatedSeedStartup
open DescentDatedSeedStartup.Input DescentColonies DescentSIMDLookup ProtocolRAM
noncomputable section

structure PortRoom (p:DatePorts) (w floor:ℕ) : Prop where
  ids : ∀i:Fin p.venue.degree,(p.io.ids i.val).Fits w floor
  idRows : ∀i:Fin p.venue.degree,p.venue.hosts*chunks p.venue.groups p.venue.lanes≤(p.io.ids i.val).size
  offsets : p.io.offsets.Fits w floor
  hosts : p.venue.hosts≤p.io.offsets.size
  chunksFit : p.io.chunks.Fits w floor
  chunkRows : p.venue.hosts*chunks p.venue.groups p.venue.lanes≤p.io.chunks.size

theorem PortRoom.mono {p:DatePorts} {w a b:ℕ} (orig:p.PortRoom w a) (step:a≤b) : p.PortRoom w b:=by
  have extend (B:Bank) (h:B.Fits w a) : B.Fits w b:=⟨h.1,h.2.1,h.2.2.trans step⟩
  exact ⟨fun i=>extend _ (orig.ids i),orig.idRows,extend _ orig.offsets,orig.hosts,
    extend _ orig.chunksFit,orig.chunkRows⟩

theorem PortRoom.accessible {p:DatePorts} {w floor:ℕ} (r:p.PortRoom w floor) (header:p.HeaderRoom w floor)
    (actors:p.ActorRoom w floor) :
    Accessible (p.io.ports p.venue.degree) p.io.actors p.venue.hosts p.venue.groups p.venue.lanes w floor :=
  ⟨r.ids,r.idRows,header.roster,header.peers,r.offsets,r.hosts,r.chunksFit,r.chunkRows,actors.fits,actors.rows⟩

theorem initial_port_room {F:Type} [Field F] {c p:ℕ} (G:PoweredGadget F) (op:RotorSpec)
    (X:Catalyst.Approximation F c p) (R:ℕ) (l:DescentDatedSeedStartup.Layout) (k H groups payload Z roof w:ℕ)
    (later:DescentDatedSeedStartup.endAddress X l H groups k≤roof) (space:roof<2^w) :
    (DatePorts.initial G op X R l k H groups payload Z).PortRoom w roof:=by
  let start:=DescentDatedSeedStartup.directoryBase X l H groups k
  have all_:=DescentSeedInitialTable.accessible start H groups l.packedLanes 3 w roof later space
  exact ⟨all_.ids,all_.idsRoom,all_.offsets,all_.offRoom,all_.chunks,all_.chunkRoom⟩

private theorem from_date (d:StageVenueTail.Date) (B:StageVenueTail.Sources) (base w roof:ℕ)
    (later:d.endAddress base≤roof) (space:roof<2^w) {p:DatePorts}
    (stage:p.venue=d) (input:p.io=d.operands B base) : p.PortRoom w roof:=by
  let pos:=StageVenueTail.area (d.thirdEnd base) d.k d.hosts d.groups d.lanes
  have cells:=DescentScalarHaloPortROM.statics d.hosts d.groups d.lanes d.degree pos roof
    (d.transported B base).roster later space
  constructor
  · rw [stage,input];exact fun j=>(cells.1 j).1
  · rw [stage,input];exact fun j=>(cells.1 j).2
  · rw [input];exact cells.2.1.1
  · rw [stage,input];exact cells.2.1.2
  · rw [input];exact cells.2.2.1.1
  · rw [stage,input];exact cells.2.2.1.2

theorem ordinary_port_room {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor w : ℕ)
    (space:v.returnedEnd floor<2^w) :
    (DatePorts.ordinary v floor).PortRoom w (v.returnedEnd floor):=by
  have «meta»:v.metaStart floor≤v.metaEnd floor:=by
    rw [PhysicalOrdinary.metaEnd,v.metadata.ordinary_translate];omega
  have op:v.metaEnd floor≤v.operandEnd floor:=by rw [PhysicalOrdinary.operandEnd,v.operandBook.affine];omega
  have tags : v.operandEnd floor≤v.primitiveEnd floor:=(v.primitive_spent _).2
  have end_ : v.primitiveEnd floor≤v.returnedEnd floor:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have later: v.venue.endAddress (v.rasterEnd floor)≤v.returnedEnd floor:=«meta».trans (op.trans (tags.trans end_))
  exact from_date _ _ _ _ _ later space rfl rfl

theorem reset_port_room {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w)
    (space:a.endAddress floor<2^w) :
    (DatePorts.reset a floor u).PortRoom w (a.endAddress floor):=by
  let v:=a.successor
  let entry:=v.fundedEnd (a.rebased floor)
  let bank:=v.venue.sources (PhysicalReset.FinalInputs.predecessor u) entry
  have later : v.venue.next.endAddress (v.venue.venueStart entry)≤a.endAddress floor:=
    v.venue_before_metadata (a.rebased floor)
  exact from_date _ _ _ _ _ later space rfl rfl


end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
