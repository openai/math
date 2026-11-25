import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentFundedRasterSpace
import OAI.Hierarchy.DescentRegisteredOrdinaryGeometry
import OAI.Hierarchy.DescentRegisteredVenuePitchBounds
import OAI.Hierarchy.DescentDonorCensusFloor

namespace OAI
/-! # Uniform raster room on the actual registered offer of every ordinary date -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentResetInvoice DescentInitialHost Chronology Chronology.RegisterTimeline
open DescentDatedAddressBook StageVenueTail DescentPacking.PackedMatch.Local.Stage DescentMixedRouter Filter
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "date_" h:arg x:arg => DonorDate.atDate G (S_ h x) g (k_ h) (x:idx h).slot.age (x:idx h).slot.p
local notation "area_" h:arg x:arg => Dated.forAge (S_ h x) G.b g (k_ h) (x:idx h).slot.age
    (Nat.clog 2 ((S_ h x).hostSize (x:idx h).slot.age)) ((S_ h x).censusBits (x:idx h).slot.p) h (date_ h x).amount
    (DescentTerminalEpochBits.width G.C) ((x:idx h).slot.menu.seats (x:idx h).slot.age)

theorem raster_room (den : 0<B) :
    OrdinaryRaster.ScalarRoom (fun h (x : idx h)=>x.model.area) (fun h (x : idx h)=>x.model.venue)
       (fun h (x : idx h)=>x.model.rasterLanes) :=by
  let sites (h) (x : idx h):=x.slot.sites
  let age (h) (x : idx h):=x.slot.age
  let grain (h) (x : idx h):=x.slot.p
  have source : Bounded sites := ⟨2,Eventually.of_forall fun h x=>by
    simpa only [sites,←pow_mul,Nat.mul_comm h 2] using x.slot.siteLimit⟩
  have grid:=PhysicalOrdinary.ordinary_geometry G t f g reset τ B sites age grain source (fun h x=>x.slot.active.le)
  have area (h) (x : idx h) : x.model.area=area_ h x :=congrArg PhysicalOrdinary.StaticCore.area x.core
  let socket (h) (x : idx h):=x.base.ticket.depotShape x.base.short
  let donor (h) (x : idx h):=x.base.fundedPanelUnit
  let extra (h) (x : idx h):=x.base.argumentUnitFrom x.slot.position.ports x.stageFloor
  apply OrdinaryRaster.funded_room (fun h (x : idx h)=>x.model.area) (fun h (x : idx h)=>x.model.venue) socket donor extra
  · intro h x
    rw [area]
    rfl
  · intro h x
    rfl
  · filter_upwards [census_fits_donor G t f g reset B den] with h fit
    intro x
    rw [area]
    exact fit x.slot.sites (tail τ (J_ h)) x.slot.p x.slot.age g x.slot.grainLimit
  · apply grid.degree.of_le
    intro h x
    rw [area]
    exact le_rfl
  · apply grid.blocks.of_le
    intro h x
    rw [area]
    exact le_rfl
  · apply grid.axis.oldHost.padded.of_le
    intro h x
    rw [area]
    exact le_rfl
  · apply grid.axis.newHost.padded.of_le
    intro h x
    exact (NativePitch.hosts_bounds (S_ h x) (x.slot.age+1) x.slot.active).2
  · apply grid.axis.oldGroup.of_le
    intro h x
    rw [area]
    exact le_rfl
  · apply grid.axis.newGroup.of_le
    intro h x
    rfl

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
