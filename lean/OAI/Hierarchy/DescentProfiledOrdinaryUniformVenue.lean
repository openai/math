import OAI.Hierarchy.DescentProfiledOrdinaryUniformAxes
import OAI.Hierarchy.DescentDatedVenueUniformSpace
import OAI.Hierarchy.DescentPurchasedOrdinaryVenueRoom

namespace OAI
/-! # One exponent for every registered successor venue before choosing the cutoff and logarithmic denominator -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentResetInvoice DescentInitialHost Chronology Chronology.RegisterTimeline
open DescentDatedAddressBook StageVenueTail DescentPacking.PackedMatch.Local.Stage DescentMixedRouter Filter
open DescentSIMDLookup
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "date_" h:arg x:arg => DonorDate.atDate G (S_ h x) g (k_ h) (x:idx h).slot.age x.slot.p
local notation "area_" h:arg x:arg => Dated.forAge (S_ h x) G.b g (k_ h) (x:idx h).slot.age
    (Nat.clog 2 ((S_ h x).hostSize x.slot.age)) ((S_ h x).censusBits x.slot.p) h (date_ h x).amount
    (DescentTerminalEpochBits.width G.C) (x.slot.menu.seats x.slot.age)

local notation "q_" h:arg x:arg =>SignedStage.atDate G (S_ h x) g (k_ h) (x:idx h).slot.age
  (NativePitch.incomingHosts (S_ h x) ((x).slot.age+1))
local notation "post" x:arg =>((x).base.fundedClip ((x).base.argumentUnitFrom (x).slot.position.ports (x).stageFloor)).postPitch

theorem final_venue_caps (slack : SignedStage.unitRate G t f g reset<B) (tailRoom : τ≤B) :
    ∀ᶠ h : ℕ in atTop,∀x : idx h,StageVenueTail.Date.NativeCaps x.model.venue h :=by
  have masks:=ResetOutput.normalized_mask_rate G t f g reset τ B (fun h (x : idx h)=>x.slot.sites)
    (fun h x=>x.slot.age) (fun h x=>x.slot.p) (fun h x=>x.model.venue.lanes)
    (fun h x=>x.slot.menu.ordinary) (fun _ _ _=>rfl) (by omega) tailRoom
  filter_upwards [masks,raw_limits G board op t f g reset τ drift degreeMax B,SignedStage.unitRate_cofinal G t f g reset B slack]
    with h paidMask dims free
  intro x
  let q:=q_ h x
  have paid : 2*q.unit≤h:=free _ _ _ _ x.slot.active.le
  have sizes:=StageVenueTail.Date.atOrdinary_signed_caps G (S_ h x) g (k_ h) (tail τ (J_ h)) x.slot.p f h
    x.slot.menu.ordinary x.slot.age (post x) paid
  have clip:=PhysicalOrdinary.fundedClipAt_paid_pitch x.base.area (x.base.ticket.depotShape x.base.short)
    x.base.fundedPanelUnit x.model.venue.paidBits (x.base.argumentUnitFrom x.slot.position.ports x.stageFloor)
  change (post x)≤x.base.area.payload ∧ x.model.venue.paidBits*(post x)≤x.base.area.payload/4 at clip
  have height : x.base.area.payload=h:=rfl
  rw [height] at clip
  have units : q.fieldBits≤h :=by
    have smaller : q.fieldBits≤q.unit:=(show q.fieldBits≤q.fieldBits*2^q.k+q.fieldBits from Nat.le_add_left ..).trans (Nat.le_max_right ..)
    omega
  have alphabet:=Nat.pow_le_pow_right (by decide : 0<2) units
  have receipt:=dims x
  have width : x.model.venue.degree≤2^q.fieldBits :=
    (Nat.le_succ _).trans ((Nat.le_max_left ..).trans_lt q.field_room.2.1).le
  have host:=((NativePitch.hosts_bounds (S_ h x) _ x.slot.active).2).trans
    (Nat.pow_le_pow_right (by decide : 0<2) ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr receipt.newHost))
  refine ⟨receipt.blocks,host,receipt.newGroup,width.trans alphabet,q.alphabet_dims.2.2.2.1.trans alphabet,
    ?_,sizes.2.2.1.trans (Nat.div_le_self ..),clip.1,clip.1,sizes.2.2.2.trans (Nat.div_le_self ..),
    clip.2.trans (Nat.div_le_self ..)⟩
  simpa only [Nat.one_mul] using paidMask x rfl

local notation "offer" τ:arg B:arg h:arg =>ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h

theorem uniform_final_venue : ∃C : ℕ,∀τ B,SignedStage.unitRate G t f g reset<B→τ≤B→
    ∀ᶠ h : ℕ in atTop,∀x : offer τ B h,x.model.venue.endAddress 0≤(2^h)^C :=by
  obtain ⟨C,actual⟩:=StageVenueTail.Date.uniform_space
  refine ⟨C,?_⟩
  intro τ B slack tailRoom
  filter_upwards [actual,final_venue_caps G board op t f g reset τ drift degreeMax B slack tailRoom] with h bound caps
  exact fun x=>bound x.model.venue (caps x)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
