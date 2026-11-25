import OAI.Hierarchy.DescentProfiledOrdinaryUniformAxes
import OAI.Hierarchy.DescentFundedRasterUniformSpace
import OAI.Hierarchy.DescentRegisteredOrdinaryGeometry
import OAI.Hierarchy.DescentRegisteredVenuePitchBounds
import OAI.Hierarchy.DescentDonorCensusFloor

namespace OAI
/-! # The ordinary raster address exponent is fixed before the two cofinality parameters -/
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

/-- Six scalar caps suffice at a genuine ordinary date, independently of the
stage floor, the retained paid census and the number of functional arguments. -/
theorem raster_at_limits {h : ℕ} (x : idx h)
    (degree : (date_ h x).degree≤2^h) (radix : 2^(k_ h)≤2^h)
    (oldHost : (S_ h x).hostSize x.slot.age≤2^(4*h))
    (newHost : (S_ h x).hostSize (x.slot.age+1)≤2^(4*h))
    (oldGroup : (S_ h x).groupCount x.slot.age≤2^h)
    (newGroup : (S_ h x).groupCount (x.slot.age+1)≤2^h) :
    OrdinaryRaster.ScalarCaps x.model.area x.model.venue h 4 :=by
  have area : x.model.area=area_ h x:=congrArg PhysicalOrdinary.StaticCore.area x.core
  have more : 2^h≤2^(4*h):=Nat.pow_le_pow_right (by decide) (by omega)
  have pad {m : ℕ} (bound : m≤2^(4*h)) : hostRows m≤2^(4*h):=
    Nat.pow_le_pow_right (by decide) ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr bound)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [area]
    exact degree.trans more
  · rw [area]
    exact radix.trans more
  · rw [area]
    exact pad oldHost
  · exact (NativePitch.hosts_bounds (S_ h x) (x.slot.age+1) x.slot.active).2.trans (pad newHost)
  · rw [area]
    exact oldGroup.trans more
  · exact newGroup.trans more

local notation "offer" τ:arg B:arg h:arg =>ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h

theorem uniform_raster_of_caps
    (limits : ∀τ B,0<B→∀ᶠ h : ℕ in atTop,∀x : offer τ B h,
      OrdinaryRaster.ScalarCaps x.model.area x.model.venue h 4) :
    ∃C : ℕ,∀τ B,0<B→∀ᶠ h : ℕ in atTop,∀x : offer τ B h,
      OrdinaryRaster.roof x.model.area x.model.venue x.model.rasterLanes 0≤(2^h)^C :=by
  obtain ⟨C,receipt⟩:=OrdinaryRaster.uniform_space 4
  refine ⟨C,?_⟩
  intro τ B den
  filter_upwards [receipt,limits τ B den,census_fits_donor G t f g reset B den] with h trueRoof caps census
  intro x
  have original:=congrArg PhysicalOrdinary.StaticCore.area x.core
  change x.model.area = _ at original
  apply trueRoof x.model.area x.model.venue (x.base.ticket.depotShape x.base.short) x.base.fundedPanelUnit
    (x.base.argumentUnitFrom x.slot.position.ports x.stageFloor)
  · rw [original]
    rfl
  · rfl
  · rw [original]
    exact census x.slot.sites (tail τ (Nat.log 2 h/(2*B))) x.slot.p x.slot.age g x.slot.grainLimit
  · exact caps x

theorem uniform_raster : ∃C : ℕ,∀τ B,0<B→∀ᶠ h : ℕ in atTop,∀x : offer τ B h,
    OrdinaryRaster.roof x.model.area x.model.venue x.model.rasterLanes 0≤(2^h)^C :=by
  apply uniform_raster_of_caps G board op t f g reset drift degreeMax
  intro τ B _
  filter_upwards [raw_limits G board op t f g reset τ drift degreeMax B] with h ready
  intro x
  have hs:=ready x
  exact raster_at_limits G board op t f g reset τ drift degreeMax B x hs.degree hs.blocks hs.oldHost hs.newHost
    hs.oldGroup hs.newGroup

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
