import OAI.Hierarchy.DescentNamedPrimitiveCharge
import OAI.Hierarchy.DescentProfiledOfferInvoice

namespace OAI
/-! Exact primitive invoice at a concrete profiled ordinary offer. -/
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
local notation "args_" x:arg => (x).base.registeredEntry (prior_ x) (x).stageFloor
local notation "ext_" x:arg => (x).base.argumentUnitFrom (prior_ x) (x).stageFloor
local notation "room_" h:arg x:arg => (prior_ x).OrdinaryCodeRoom (x).cut.ticket op g (tb_ h) (x).slot.p f drift (x).slot.degree h (seats_ x) (x).slot.position.floor (x).slot.menu.ordinary

theorem profiled_primitive_charge {h : ℕ} (x : idx h) (room : x.CodeRoom)
    (grant : ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ B drift degreeMax driftR h)
    (driftOk : drift+1 ≤ scale (J_ h) driftR) (sitesPos : 0<x.slot.sites) (grainPos : 0<x.slot.p)
    (bus : x.slot.bus≤ratio*h) :
    let slots : (prior_ x).argumentsPerNode≤x.base.vector.operands:=Nat.le_max_left ..
    let mat:=x.base.registered_match (prior_ x) x.stageFloor slots
    (x.model.primitiveUpdate x.stageFloor (args_ x) mat room.radix x.slot.bus).wordInvoice≤
      ratio*scale (J_ h) (OrdinaryBooks.primitiveChargeRate G t f g reset driftR)*x.model.rowVolume h:=by
  intro slots mat
  have hosts : 0<(S_ h x).hostSize x.slot.age:=
    Nat.mul_pos sitesPos (Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)))
  exact Branch.registered_primitive_charge x.cut.original G (S_ h x) x.cut.branch x.cut.ticket x.cut.before
    x.cut.after x.cut.joined op (tb_ h) drift x.slot.degree h (seats_ x) (prior_ x).venue.lanes (prior_ x)
    (prior_ x).io.roster x.slot.menu.ordinary x.stageFloor (copies:=x.slot.sites) grant cost rfl rfl rfl driftOk
    x.slot.degreeLimit x.slot.grainLimit x.firstWidth grainPos x.slot.geometry.room.archive x.slot.geometry.room.args
    x.slot.active hosts x.slot.bus ratio bus

/-- The same acquired calendar checks the primitive addresses and row capacities
before constructing the execution room for this exact physical offer. -/
theorem profiled_primitive_room {h w : ℕ} (x : idx h)
    (grant : ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ B drift degreeMax driftR h)
    (driftOk : drift+1 ≤ scale (J_ h) driftR) (grainPos : 0<x.slot.p)
    (entryFits : (args_ x).Room x.model x.stageFloor w)
    (last : x.model.primitiveRoof (x.model.operandEnd x.stageFloor)<2^w) :
    let mat:=x.base.registered_match (prior_ x) x.stageFloor (Nat.le_max_left ..)
    x.model.PrimitiveRoom x.stageFloor (args_ x) w ∧
      x.model.paletteShape.Capacity (x.model.primitiveSources x.stageFloor (args_ x) mat rfl):=by
  intro mat
  have ready:=Branch.registered_primitive_purchase x.cut.original G (S_ h x) x.cut.branch x.cut.ticket
    x.cut.before x.cut.after x.cut.joined op (tb_ h) drift x.slot.degree h (seats_ x) (prior_ x).venue.lanes
    (prior_ x) (prior_ x).io.roster x.slot.menu.ordinary x.stageFloor (copies:=x.slot.sites)
    grant cost rfl rfl rfl driftOk x.slot.degreeLimit x.slot.grainLimit x.firstWidth grainPos
    x.slot.geometry.room.archive x.slot.geometry.room.args
  exact Branch.registered_primitive_rooms (radix:=x.cut.radix) (X:=x.cut.original) (G:=G) (S:=S_ h x) (ticket:=x.cut.ticket)
    (op:=op) (frozen:=tb_ h) (drift:=drift) (degree:=x.slot.degree) (payload:=h) (seats:=seats_ x)
    (hostLanes:=(prior_ x).venue.lanes) (ports:=prior_ x) (old:=(prior_ x).io.roster)
    (ordinary:=x.slot.menu.ordinary) (stageFloor:=x.stageFloor) x.slot.active (Nat.le_max_left ..) entryFits ready.1 last

theorem eventual_profiled_primitive_charge (margin : OrdinaryBooks.primitiveLaneRate G t f g reset driftR+2≤B) :
    ∀ᶠ h : ℕ in atTop,∀(x : idx h) (room : x.CodeRoom),
    ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h → drift+1 ≤ scale (J_ h) driftR →
    0<x.slot.sites → 0<x.slot.p → x.slot.bus≤ratio*h →
    let mat:=x.base.registered_match (prior_ x) x.stageFloor (Nat.le_max_left ..)
    (x.model.primitiveUpdate x.stageFloor (args_ x) mat room.radix x.slot.bus).wordInvoice≤
      ratio*scale (J_ h) (OrdinaryBooks.primitiveChargeRate G t f g reset driftR)*x.model.rowVolume h:=by
  filter_upwards [OrdinaryBooks.eventual_primitive_calendar G op t f g reset τ B drift degreeMax driftR margin]
    with h acquired
  intro x room grant dr live pos bus
  exact profiled_primitive_charge G board op t f g reset τ drift degreeMax B driftR ratio x room grant acquired dr live pos bus

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
