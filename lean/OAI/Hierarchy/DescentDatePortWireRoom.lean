import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentStageVenueWireRoom
import OAI.Hierarchy.DescentResetVenueEnd

namespace OAI
/-! # The original signed bank available at each calendar cut -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentInitialHost DescentCompiler DescentDatedSeedStartup
open DescentDatedSeedStartup.Input DescentColonies DescentSIMDLookup ProtocolRAM
noncomputable section

def WireRoom (p : DatePorts) (w roof : ℕ) : Prop :=
  ∀(x:Block p.venue.k)(j:Fin (2*p.venue.cap)),(p.io.wire x.val j.val).Fits w roof ∧
    p.venue.hosts*chunks p.venue.groups p.venue.lanes≤(p.io.wire x.val j.val).size

theorem WireRoom.mono {p : DatePorts} {w first last : ℕ} (fit:p.WireRoom w first) (later:first≤last) :
    p.WireRoom w last:=by
  intro x j
  obtain ⟨bank,rows⟩:=fit x j
  exact ⟨⟨bank.1,bank.2.1,bank.2.2.trans later⟩,rows⟩

theorem initial_wire_room {F : Type} [Field F] {c p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F c p) (R : ℕ) (l : DescentDatedSeedStartup.Layout) (k H groups payload Z roof w : ℕ)
    (later:DescentDatedSeedStartup.endAddress X l H groups k≤roof) (space:roof<2^w) :
    (DatePorts.initial G op X R l k H groups payload Z).WireRoom w roof:=by
  intro x j
  exact DescentDatedSeedStartup.wire_room X l roof later space x.val j.val

theorem ordinary_wire_room {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor w : ℕ)
    (space:v.returnedEnd floor<2^w) :
    (DatePorts.ordinary v floor).WireRoom w (v.returnedEnd floor):=by
  have «meta»:v.metaStart floor≤v.metaEnd floor:=by
    rw [PhysicalOrdinary.metaEnd,v.metadata.ordinary_translate];omega
  have op:v.metaEnd floor≤v.operandEnd floor:=by rw [PhysicalOrdinary.operandEnd,v.operandBook.affine];omega
  have tags : v.operandEnd floor≤v.primitiveEnd floor:=(v.primitive_spent _).2
  have end_ : v.primitiveEnd floor≤v.returnedEnd floor:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have later: v.venue.endAddress (v.rasterEnd floor)≤v.returnedEnd floor:=«meta».trans (op.trans (tags.trans end_))
  intro x j
  obtain ⟨fit,rows⟩:=v.venue.wire_room (v.reachedSources floor) (v.rasterEnd floor) w x j (later.trans_lt space)
  exact ⟨⟨fit.1,fit.2.1,fit.2.2.trans later⟩,rows⟩

theorem reset_wire_room {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w)
    (space:a.endAddress floor<2^w) :
    (DatePorts.reset a floor u).WireRoom w (a.endAddress floor):=by
  let v:=a.successor
  let entry:=v.fundedEnd (a.rebased floor)
  let bank:=v.venue.sources (PhysicalReset.FinalInputs.predecessor u) entry
  have later : v.venue.next.endAddress (v.venue.venueStart entry)≤a.endAddress floor:=
    v.venue_before_metadata (a.rebased floor)
  intro x j
  obtain ⟨fit,rows⟩:=v.venue.next.wire_room bank (v.venue.venueStart entry) w x j (later.trans_lt space)
  exact ⟨⟨fit.1,fit.2.1,fit.2.2.trans later⟩,rows⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
