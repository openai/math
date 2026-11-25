import OAI.Hierarchy.DescentFundedPreviousBank
import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentStageVenueWireRoom
import OAI.Hierarchy.DescentResetVenueEnd

namespace OAI
/-! # The physical actor register available before every ordinary step -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentFundedCensus DescentDatedAddressBook DescentInitialHost DescentCompiler DescentDatedSeedStartup
open DescentDatedSeedStartup.Input DescentColonies DescentSIMDLookup ProtocolRAM
noncomputable section

structure ActorRoom (p : DatePorts) (w floor : ℕ) : Prop where
  fits : p.io.actors.Fits w floor
  rows : p.venue.hosts*chunks p.venue.groups p.venue.lanes≤p.io.actors.size

theorem ActorRoom.mono {p : DatePorts} {w first last : ℕ} (r : p.ActorRoom w first) (later : first≤last) :
    p.ActorRoom w last:=⟨⟨r.fits.1,r.fits.2.1,r.fits.2.2.trans later⟩,r.rows⟩

private theorem from_date (d : StageVenueTail.Date) (B : StageVenueTail.Sources) (base w roof : ℕ)
    (later : d.endAddress base≤roof) (space : roof<2^w) :
    ((d.operands B base).actors.Fits w roof) ∧
    d.hosts*chunks d.groups d.lanes≤(d.operands B base).actors.size:=by
  let bank:=(d.operands B base).actors
  have within : bank.base+bank.size≤roof:=by
    apply le_trans _ later
    change StageVenueTail.area (d.thirdEnd base) d.k d.hosts d.groups d.lanes≤
      DescentScalarHaloPortROM.stop d.hosts d.groups d.lanes d.degree _
    unfold DescentScalarHaloPortROM.stop
    omega
  have positive : 0<bank.size:=Nat.two_pow_pos _
  refine ⟨⟨positive,?_,within⟩,?_⟩
  · change bank.size<2^w
    omega
  · exact Nat.le_pow_clog (by decide) _

theorem initial_actor_room {F:Type} [Field F] {c p:ℕ} (G:PoweredGadget F) (op:RotorSpec)
    (X:Catalyst.Approximation F c p) (R:ℕ) (l:DescentDatedSeedStartup.Layout) (k H groups payload Z roof w:ℕ)
    (later:DescentDatedSeedStartup.endAddress X l H groups k≤roof) (space:roof<2^w) :
    (DatePorts.initial G op X R l k H groups payload Z).ActorRoom w roof:=by
  let start:=DescentDatedSeedStartup.directoryBase X l H groups k
  have done : DescentSeedInitialTable.endAddress start H groups l.packedLanes 3≤roof:=later
  have f:=DescentSeedInitialTable.bank_fits (base:=start) (H:=H) (G:=groups) (M:=l.packedLanes) (D:=3)
    (c:=3) (by decide) (done.trans_lt space)
  exact ⟨⟨f.1,f.2.1,f.2.2.trans done⟩,(DescentSeedInitialTable.capacities H groups l.packedLanes 3).2.2⟩

theorem ordinary_actor_room {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor w : ℕ)
    (space:v.returnedEnd floor<2^w) :
    (DatePorts.ordinary v floor).ActorRoom w (v.returnedEnd floor):=by
  have «meta»:v.metaStart floor≤v.metaEnd floor:=by
    rw [PhysicalOrdinary.metaEnd,v.metadata.ordinary_translate];omega
  have op:v.metaEnd floor≤v.operandEnd floor:=by rw [PhysicalOrdinary.operandEnd,v.operandBook.affine];omega
  have tags : v.operandEnd floor≤v.primitiveEnd floor:=(v.primitive_spent _).2
  have end_ : v.primitiveEnd floor≤v.returnedEnd floor:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have later: v.venue.endAddress (v.rasterEnd floor)≤v.returnedEnd floor:=«meta».trans (op.trans (tags.trans end_))
  obtain ⟨fit,rows⟩:=from_date v.venue (v.reachedSources floor) (v.rasterEnd floor) w _ later space
  exact ⟨fit,rows⟩

theorem reset_actor_room {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w)
    (space:a.endAddress floor<2^w) :
    (DatePorts.reset a floor u).ActorRoom w (a.endAddress floor):=by
  let v:=a.successor
  let entry:=v.fundedEnd (a.rebased floor)
  let bank:=v.venue.sources (PhysicalReset.FinalInputs.predecessor u) entry
  have later : v.venue.next.endAddress (v.venue.venueStart entry)≤a.endAddress floor:=
    v.venue_before_metadata (a.rebased floor)
  obtain ⟨fit,rows⟩:=from_date v.venue.next bank (v.venue.venueStart entry) w _ later space
  exact ⟨fit,rows⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
