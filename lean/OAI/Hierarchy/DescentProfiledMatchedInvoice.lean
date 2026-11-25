import OAI.Hierarchy.DescentProfiledMatcherCharge
import OAI.Hierarchy.DescentProfiledOrdinaryCharges

namespace OAI
/-! # The measured matcher summand in the original offer's exact price decomposition -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler TerminalScale Chronology DescentInitialHost DescentResetInvoice
open DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local.Stage.Dated Filter
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
    {op : RotorSpec} {t f g reset τ drift degreeMax B h : ℕ}
local notation "idx" H:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B H
local notation "J_" H:arg => Nat.log 2 H/(2*B)
local notation "k_" H:arg =>groupBits t (J_ H) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "S_" H:arg x:arg => stageNumbers G t (J_ H) f g reset (x:idx H).slot.sites (tail τ (J_ H))

theorem match_invoice_eq (x : idx h) (live : 0<(k_ h)) : x.matchInvoice live=x.matcherFee x.slot.bus :=by
  have measured : (⟨x.cut.source.placement.wire,x.cut.source.placement.z,x.cut.source.placement.hist⟩ : Measures)=
      measuresAt (S_ h x) G.b x.slot.p x.slot.age := congrArg PhysicalOrdinary.StaticCore.measures x.core
  unfold matchInvoice
  dsimp only
  rw [measured]
  rfl

variable (G board op t f g reset τ drift degreeMax B)
theorem chosen_match_invoice (positive : 0<B)
    (large : 2*((2+hostRate t reset*(t+1)+
      ((donorRates G t f g reset).amount+(donorRates G t f g reset).work)+1+1)+5)≤B) :
    ∀ᶠ h : ℕ in atTop, ∀x : idx h, ∀ratio saving, 2^h≤2*x.slot.sites →
      h≤x.slot.bus → x.slot.bus≤ratio*h →
      max x.endAt (x.model.signedGuard x.stageFloor)<2^x.slot.bus →
      ∀live : 0<(k_ h), x.matchInvoice live≤x.Price ratio (matcherChargeRate G t f g reset) 0 saving :=by
  filter_upwards [calibrated_matcher_charge G board op t f g reset τ drift degreeMax B positive large]
    with h grant
  intro x ratio saving stock embed width ready live
  rw [x.match_invoice_eq live]
  simpa only [Price,Nat.zero_mul,Nat.add_zero,Nat.add_mul] using grant x ratio stock embed width ready

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
