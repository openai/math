import OAI.Hierarchy.DescentNamedProfiledCalendarRate
import OAI.Hierarchy.DescentProfiledUniformCeilingSum

namespace OAI
/-! The maximum of the two native address exponents can be taken before
choosing the epoch tail, the logarithmic height divisor or the CPU width. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledRate
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentDatedAddressBook.PhysicalReset Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset drift bound : ℕ)
local notation "x_" τ:arg B:arg h:arg =>ProfiledOrdinaryOffer G f g board op t reset τ drift bound B h
local notation "z_" τ:arg B:arg h:arg =>ProfiledPosition G board op t f g reset τ drift bound B h
local notation "safety" => 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)
local notation "receiver" => 2*degreeRate G board op t f g reset (maximumDegree (t+1))

def UniformAddresses (driftR slots addr : ℕ) : Prop :=
  ∀τ B,threshold G board op t f g reset τ drift driftR bound slots ≤ B →
    ∀ᶠ h:ℕ in atTop,Covers G board op t f g reset τ drift bound B h addr

theorem uniform_addresses_of
    (ordinary : ProfiledOrdinaryOffer.UniformRoof G board op t f g reset drift bound
      (fun τ B h (x:x_ τ B h)=>max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor))
    (resets : ∃K:ℕ,∀τ B,0 < B → G.b ≤ 2^(capRate G t g) → safety ≤ B → receiver ≤ B → τ ≤ B →
      ∀ᶠ h:ℕ in atTop,∀x:z_ τ B h,x.IsReset → x.resetEnd-x.position.floor ≤ 2^(K*h)) :
    ∃addr:ℕ,∀driftR slots,UniformAddresses G board op t f g reset drift bound driftR slots addr :=by
  obtain ⟨A,old⟩:=ordinary
  obtain ⟨R,next⟩:=resets
  refine ⟨max A R,?_⟩
  intro driftR slots τ B funded
  have calibrated:=funded
  unfold threshold at calibrated
  have pitch : PitchCalendar.threshold G board op t f g reset drift driftR bound slots τ ≤ B:=by omega
  have fare : SignedStage.unitRate G t f g reset < B:=by omega
  have geometry : safety ≤ B:=by omega
  unfold PitchCalendar.threshold at pitch
  have short : τ ≤ B:=by omega
  have span : receiver ≤ B:=by omega
  have pos : 0 < B:=by omega
  have fan : G.b ≤ 2^(capRate G t g):=(show G.b ≤ capRate G t g by unfold capRate;omega).trans Nat.lt_two_pow_self.le
  filter_upwards [old τ B pos fare short,next τ B pos fan geometry span short] with h today after
  exact ⟨fun x=>(today x).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (le_max_left A R))),
    fun x atReset=>(after x atReset).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (le_max_right A R)))⟩

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledRate

end OAI
