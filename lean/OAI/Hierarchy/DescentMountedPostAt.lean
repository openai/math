import OAI.Hierarchy.DescentNamedCountedPostPrice
import OAI.Hierarchy.DescentMountedCountedPostPrice
import OAI.Hierarchy.DescentOriginalRoleReelCharge

namespace OAI
/-! Two exact single-height invoices for the mounted original terminal replay. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
variable (t f g reset τ B drift : ℕ)
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "limit_" => localSocketRate G t g
local notation "scan_" => PreflightCalendar.scanExponent G t f g reset
local notation "slice_" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)+groupRate G t f g reset+4

structure MountedCountedPostAt (h : ℕ) : Prop where
  counted : CountedPostAt G op t f g reset τ B drift h
  installed : RoleReelAt G op drift t f g reset τ B h

/-- Both parts of the literal mounted schedule use the same calibration and height. -/
theorem mounted_counted_post_at (big : 20≤B) (pad : 2*limit_≤τ)
    (funded : limit_+max scan_ slice_≤τ)
    (budget : 2*(limit_+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤B)
    (branch : G.b≤2^(capRate G t g))
    (ageFit : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19)) ≤ B) :
    ∀ᶠ h : ℕ in atTop, MountedCountedPostAt G op t f g reset τ B drift h :=by
  filter_upwards [counted_post_preflight_price G op t f g reset τ B drift big pad funded budget,
    original_role_reel_price G op drift t f g reset τ B branch (by omega) ageFit] with h counted installed
  exact ⟨counted,installed⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
