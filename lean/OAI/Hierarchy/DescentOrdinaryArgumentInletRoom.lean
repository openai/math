import OAI.Hierarchy.DescentOrdinaryArgumentGatherRoom
import OAI.Hierarchy.DescentOrdinaryPriorGatherPorts

namespace OAI
/-! The ordinary inlet hardware from the preceding date's actual three input families. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOrdinaryAtomFieldRAM DescentRawCablePanel DescentSIMDLookup
open DescentOrdinaryVenueIngress DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
variable (floor : ℕ)
local notation "c₀" => A.clip
local notation "v₀" => A.clip.core
local notation "base₀" => v.signedEnd floor
local notation "L₀" => A.population v floor

private theorem expand {B : Bank} {w l t : ℕ} (fit : B.Fits w l) (le : l≤t) : B.Fits w t :=
  ⟨fit.1,fit.2.1,fit.2.2.trans le⟩

theorem inlet_room {w} (venue : (c₀).Room A.venue base₀ w)
    (previous : ∀x p,(previousBank A.previous A.previousBase x p).Fits w base₀)
    (role : ∀x,(A.role x).Fits w base₀)
    (chipWidth : (c₀).working*max (DepotRAM.totalBits (c₀).venue.socket)
      (DepotRAM.outputBits (c₀).venue.socket)≤w/2) (ceiling : A.finish v floor<2^w) :
    A.Room v floor w :=by
  obtain ⟨front,oldEnd,roleEnd,chipEnd,popEnd⟩:=A.inlet_order v floor
  obtain ⟨_,actor,setup⟩:=(c₀).bounds base₀
  have panel:=Overlap.output_fits base₀ (c₀).venue.hosts (c₀).venue.groups (c₀).panelPitch
    (c₀).working (c₀).peerBits w ((actor.trans setup).trans_lt venue.space)
  have cap : (L₀).outBase≤A.finish v floor:=Nat.le_add_right ..
  have after : A.populationBase v floor ≤ (L₀).outBase:=Nat.le_add_right ..
  refine ⟨venue,fun x p=>expand (previous x p) front,fun x=>expand (role x) (front.trans oldEnd),
    panel.1.2.2.trans (actor.trans (setup.trans (oldEnd.trans roleEnd))),panel.2.1,chipWidth,?_,ceiling⟩
  intro x
  have label:=(A.roleLayout v).placed (A.roleStart v floor) ((chipEnd.trans popEnd).trans_lt ceiling) x
  have bankFit:=expand label.1 (chipEnd.trans after)
  let start:=(c₀).setupStart base₀
  obtain ⟨_,_,_,raster,_⟩:=(v₀).ceilings start
  have halo : (v₀).rasterBase start≤(c₀).fullEnd base₀:=
    raster.trans (Nat.le_add_right ..)
  have bound:=halo.trans (oldEnd.trans (roleEnd.trans (chipEnd.trans after)))
  exact DescentScalarHaloProgram.later_bank (v₀).hosts (v₀).groups (v₀).lanes (v₀).socket.degree
    ((v₀).haloBase start) (L₀).outBase w (A.labels v floor x) bound (cap.trans_lt ceiling) bankFit label.2

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
