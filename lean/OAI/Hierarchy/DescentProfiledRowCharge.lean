import OAI.Hierarchy.DescentProfiledOfferInvoice
import OAI.Hierarchy.DescentArgumentGeometryReceipt
import OAI.Hierarchy.DescentRegisteredSectionPopulation
import OAI.Hierarchy.DescentTerminalScheduleScale

namespace OAI
/-! # One shared calendar charge for all the local ordinary phases -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentResetInvoice Chronology
open Chronology.RegisterTimeline DescentPacking.PackedMatch.Local.Stage DescentDatedAddressBook DescentPackedProfileInstall
open DescentMixedRouter Filter
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
  (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg=>ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg=>Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg=>stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg=>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "shelf_" x:arg=>(x).slot.menu.profile (x).slot.age
local notation "seats_" x:arg=>(x).slot.menu.seats (x).slot.age


def rowLead (t reset ratio : ℕ) :=(5+4*2^(hostRate t reset))*ratio

theorem charged_offer_rows (ratio exponent saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(x : idx h) (cost : ℕ),
      2^h ≤ x.slot.sites → 0<(S_ h x).hostSize x.slot.age →
      cost ≤ ratio*scale (J_ h) exponent*x.model.rowVolume h →
      cost ≤ x.Price (rowLead t reset ratio) (exponent+groupRate G t f g reset) 1 saving :=by
  filter_upwards [PhysicalOrdinary.SectionPopulation.shared_control_all (F:=F) ratio exponent saving]
    with h control
  intro x cost native positive fee
  let S:=S_ h x
  let J:=J_ h
  let p:=x.slot.position.ports
  let l:=x.slot
  let c:=x.cut
  let e:=x.base.registeredEntry p x.stageFloor
  have pop:=p.registered_section_population c.ticket op g (tail τ J) l.p f drift l.degree h
    (l.menu.seats l.age) p.venue.lanes p.io.roster l.menu.ordinary x.stageFloor (t:=t) (J:=J) (reset:=reset)
    (M:=l.sites) rfl positive c.radix
  have observed:=control _ x.model e S l.age J l.sites cost pop positive (Nat.div_le_self ..) native
    (by rw [Nat.mul_comm (scale J exponent) ratio]; exact fee)
  let U:=scale J (groupRate G t f g reset)
  have rlo : 0 < S.radix:=by rw [c.radix];positivity
  have rhi : S.radix ≤ U:=by rw [c.radix];exact Nat.pow_le_pow_right (by decide) (groupBits_linear ..)
  have pg : 1 ≤ U:=Nat.one_le_two_pow
  have fixed : 2^S.hostGain = 2^(hostRate t reset):=rfl
  have growth : 5+2*2^S.hostGain*(S.radix+1) ≤ (5+4*2^(hostRate t reset))*U:=by
    rw [fixed]
    have nr : S.radix+1 ≤ 2*U:=by omega
    calc
      _ ≤ 5*U+2*2^(hostRate t reset)*(2*U):=by
        gcongr
        omega
      _ = _:=by ring
  have paid : scale J exponent*ratio*(5+2*2^S.hostGain*(S.radix+1)) ≤ rowLead t reset ratio*scale J (exponent+groupRate G t f g reset) :=by
    calc
      _ ≤ scale J exponent*ratio*((5+4*2^(hostRate t reset))*U):=Nat.mul_le_mul_left _ growth
      _=_:=by rw [←scale_mul];dsimp only [rowLead,U];ring
  have slots : S.groupCount l.age ≤ S.groupCount l.age*S.radix:=Nat.le_mul_of_pos_right _ rlo
  unfold Price
  dsimp only at observed ⊢
  rw [one_mul]
  exact observed.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left _ paid)
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ slots) paid)) _)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
