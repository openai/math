import OAI.Hierarchy.DescentNamedSeedPosition
import OAI.Hierarchy.DescentNamedSeedHeadRate
import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentRegisteredSeedGeometry
import OAI.Hierarchy.DescentRegisteredProfileSeed

namespace OAI
/-! # The same selected seed as the first position of the dated native calendar -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedSeedStartup DescentDatedAddressBook
open Chronology RegisterTimeline DescentInitialHost DescentTerminalEpochChart DescentWideSeedFlags Catalyst
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g rate drift J M θ h H degree wire hist bins raw : ℕ)
    {cp pins : ℕ} (X : Approximation F cp pins) {P : Type} (steps : List (Source P))
local notation "S" => stageNumbers G t J f g rate M θ
local notation "k" => groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "p" => headGrain G S k h
local notation "V" => originalSeedHead G op drift X steps S k θ h H degree wire hist bins raw
local notation "lo" => selectorBase X (S).copies ((S).firstWidth G.b p) h steps.length
local notation "menu" => fromProfiles G S board op k θ p f g drift degree h lo ((V).base G h-1) steps

/-- The initial position uses the address immediately following the issued role token
transposition. Its sole numerical ceiling comes from the chosen seed address exponent. -/
theorem original_head_geometry (w headRate : ℕ) (epochs : 0<J) (branch : G.b≤2^(capRate G t g))
    (sites : ∃i,M=2^i) (hosts : M≤H) (layout : H≤hostRows M)
    (initial : (V).floor G op t f g drift h ≤ 2^(headRate*h)) (machine : headRate*h<w) :
    Geometry G S menu k w 0 ((V).position G op t f g drift h) :=by
  exact profiled_seed_geometry G S board op k θ p f g drift degree h lo ((V).base G h-1) steps X
    (S).copies ((V).base G h) wire hist H w epochs branch
    rfl sites ⟨t,rate,J,M,rfl⟩ (by simpa only [AtomSchedule.hostSize,pow_zero,Nat.mul_one,stageNumbers] using hosts)
    (by simpa only [AtomSchedule.hostSize,pow_zero,Nat.mul_one,stageNumbers] using layout)
    (initial.trans_lt (Nat.pow_lt_pow_right (by decide) machine))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
