import OAI.Hierarchy.DescentProfiledOfferInvoice
import OAI.Hierarchy.DescentFundedRasterRowFeeProfile
import OAI.Hierarchy.DescentNamedRegisteredSuffix
import OAI.Hierarchy.DescentDateAtomColumns

namespace OAI
/-! # The full paid and alive update executed by the profiled ordinary register -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentSIMDLookup Filter
open DescentInitialHost DescentMixedRouter DescentResetInvoice ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B driftR ratio saving : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "tb_" h:arg => tail τ (J_ h)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tb_ h)
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "prior_" x:arg => (x).slot.position.ports
local notation "seats_" x:arg => (x).slot.menu.seats (x).slot.age
local notation "args_" x:arg => x.base.registeredEntry (prior_ x) x.stageFloor
local notation "ext_" x:arg => x.base.argumentUnitFrom (prior_ x) x.stageFloor
local notation "room_" h:arg x:arg => (prior_ x).OrdinaryCodeRoom x.cut.ticket op g (tb_ h) x.slot.p f drift x.slot.degree h (seats_ x) x.slot.position.floor x.slot.menu.ordinary


local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose
local notation "fundingRate" => 44*argumentDigitRate G t f g reset driftR baseRate
theorem profiled_funded_raster_charge {h : ℕ} (x : idx h) (room : x.CodeRoom)
    (grant : ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h)
    (resources : ReturnCalendar G t f g reset driftR fundingRate τ B ratio h)
    (dr : drift+1 ≤ scale (J_ h) driftR) (positive : 0<(S_ h x).hostSize x.slot.age)
    (grain : 0 < x.slot.p) (bus : x.slot.bus ≤ ratio*h) :
    let p:=x.slot.position.ports
    let e:=x.base.registeredEntry p x.stageFloor
    let B₀:=x.model.fundedFromEntry x.stageFloor e room.paths
    (x.model.fundedRaster x.stageFloor B₀ p.io x.slot.bus room.funded).wordInvoice ≤ ratio*scale (J_ h) (fundedRasterExponent G t f g reset driftR)*x.model.rowVolume h :=by
  intro p e B₀
  let S:=S_ h x
  let J:=J_ h
  let c:=x.cut
  let z:=x.slot
  let ext:=x.base.argumentUnitFrom p x.stageFloor
  have width:=Branch.registered_base_width c.original G S c.branch c.ticket c.before c.after c.joined op
    (tail τ J) drift z.degree h (z.menu.seats z.age) p.venue.lanes p p.io.roster z.menu.ordinary grant rfl rfl z.grainLimit
  have caps:=Branch.registered_row_funding c.original G S c.branch c.ticket c.before c.after c.joined op
    (tail τ J) drift z.degree h (z.menu.seats z.age) p.venue.lanes p p.io.roster z.menu.ordinary x.stageFloor
    grant resources rfl rfl rfl dr width z.degreeLimit z.grainLimit x.firstWidth z.geometry.room.archive z.geometry.room.args grain
  have rowWork (j : ℕ) (hj : j<2^x.model.area.k) : (p.io.atoms j).work ≤ 7 := by
    exact ((z.geometry.room.paid.atom_columns (k_ h)).work ⟨j,hj⟩).le
  have native:=x.model.funded_caps_bill x.stageFloor B₀ p.io z.bus room.funded h (4*x.base.area.unit)
    (x.base.fundedWorkingUnit ext) (2^(k_ h)*x.base.fundedWorkingUnit ext) 7 ratio rowWork bus caps.1
  exact native.trans (funded_raster_rows G board op t f g reset τ drift degreeMax B x driftR ratio grant dr positive)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
