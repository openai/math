import OAI.Hierarchy.DescentFundedPreviousBank
import OAI.Hierarchy.DescentDatedRegisterState
import OAI.Hierarchy.DescentStageVenueWireRoom
import OAI.Hierarchy.DescentResetVenueEnd

namespace OAI
/-! # The original funded banks available at each calendar cut -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentFundedCensus DescentDatedAddressBook DescentInitialHost DescentCompiler DescentDatedSeedStartup
open DescentDatedSeedStartup.Input DescentColonies DescentSIMDLookup ProtocolRAM
noncomputable section

structure PaidRoom (p : DatePorts) (w floor : ℕ) : Prop where
  issued : IssuedBanks p.io p.venue.hosts p.venue.groups p.venue.lanes
  stock : ∀x,(p.io.atoms x).Fits w floor

theorem PaidRoom.mono {p : DatePorts} {w first last : ℕ} (room : p.PaidRoom w first) (later : first≤last) :
    p.PaidRoom w last:=⟨room.issued,fun x=>ProtocolRAMGeneratedWrite.fits_mono _ later (room.stock x)⟩

private theorem from_date (d : StageVenueTail.Date) (B : StageVenueTail.Sources) (base w roof : ℕ)
    (later : d.endAddress base≤roof) (space : roof<2^w) :
    ∀x,((d.operands B base).atoms x).Fits w roof:=by
  intro x
  obtain ⟨_,_,bc,cd⟩:=d.order base
  have limit:=bc.trans (cd.trans later)
  let j:Fin d.paidShape.pages:=⟨if x<2^d.k then x else 0,by
    change (if x<2^d.k then x else 0)<2^d.k
    split <;> first | assumption | exact Nat.two_pow_pos _⟩
  have f:=(DescentVenueSlabs.page_room d.paidShape (d.firstEnd base) w j (limit.trans_lt space)).1
  exact ⟨⟨f.1,f.2.1,f.2.2.trans limit⟩,trivial⟩

theorem initial_paid_room {F : Type} [Field F] {c p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F c p) (R : ℕ) (l : DescentDatedSeedStartup.Layout) (k H groups payload Z roof w : ℕ)
    (later:DescentDatedSeedStartup.endAddress X l H groups k≤roof) (space:roof<2^w) :
    (DatePorts.initial G op X R l k H groups payload Z).PaidRoom w roof:=by
  refine ⟨from_seed X l k H groups,?_⟩
  intro x
  let db:=DescentDatedSeedStartup.directoryBase X l H groups k
  have bound : DescentSeedInitialTable.endAddress db H groups l.packedLanes 3≤roof:=later
  have f:=DescentSeedInitialTable.bank_fits (c:=5) (D:=3) (by decide) (bound.trans_lt space)
  exact ⟨⟨f.1,f.2.1,f.2.2.trans bound⟩,trivial⟩

theorem ordinary_paid_room {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor w : ℕ)
    (space:v.returnedEnd floor<2^w) :
    (DatePorts.ordinary v floor).PaidRoom w (v.returnedEnd floor):=by
  have «meta»:v.metaStart floor≤v.metaEnd floor:=by
    rw [PhysicalOrdinary.metaEnd,v.metadata.ordinary_translate];omega
  have op:v.metaEnd floor≤v.operandEnd floor:=by rw [PhysicalOrdinary.operandEnd,v.operandBook.affine];omega
  have tags : v.operandEnd floor≤v.primitiveEnd floor:=(v.primitive_spent _).2
  have end_ : v.primitiveEnd floor≤v.returnedEnd floor:=((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have later: v.venue.endAddress (v.rasterEnd floor)≤v.returnedEnd floor:=«meta».trans (op.trans (tags.trans end_))
  exact ⟨from_venue ..,from_date _ _ _ _ _ later space⟩

theorem reset_paid_room {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w)
    (space:a.endAddress floor<2^w) :
    (DatePorts.reset a floor u).PaidRoom w (a.endAddress floor):=by
  let v:=a.successor
  let entry:=v.fundedEnd (a.rebased floor)
  let bank:=v.venue.sources (PhysicalReset.FinalInputs.predecessor u) entry
  have later : v.venue.next.endAddress (v.venue.venueStart entry)≤a.endAddress floor:=
    v.venue_before_metadata (a.rebased floor)
  exact ⟨from_venue ..,from_date _ _ _ _ _ later space⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
