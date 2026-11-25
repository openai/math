import OAI.Hierarchy.DescentSeedCompleteAfterAt
import OAI.Hierarchy.DescentNamedSeedPosition
import OAI.Hierarchy.DescentNamedSeedHeadData

namespace OAI
/-! # Startup cost at the original registered position of the dyadic machine -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSixParty.SeedNamed
open DescentSixParty.Chronology DescentInitialHost DescentTerminalEpochChart DescentDyadicSpan Catalyst
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (op next : RotorSpec)
variable (t f g reset drift degreeMax τ B factor h M H degree wire hist bins raw : ℕ)
variable {cp pins : ℕ} (X : Approximation F cp pins) {A : Type} (steps : List (Source A))
local notation "J_" => Nat.log 2 h/(2*B)
local notation "θ_" => DescentCompiler.TerminalScale.tail τ J_
local notation "S_" => stageNumbers G t J_ f g reset M θ_
local notation "k_" => groupBits t J_ (S_).hostGain (S_).capGain (cutRate t f g)
local notation "V_" => originalSeedHead G next drift X steps S_ k_ θ_ h H degree wire hist bins raw
local notation "L_" => (V_).layout G t f g drift h
local notation "z_" => (S_).grainAt G.b (V_).p 0
local notation "b_" => (V_).base G h-1
local notation "ds_" => (S_).initialDigits (k:=k_) rfl
local notation "flags" w:arg => DescentWideSeedFlags.check X (S_).copies ((V_).width G) h w
local notation "boot" rotor:arg live:arg w:arg => DescentDatedSeedStartup.Input.completeAfter G rotor X ds_ live L_ b_ h z_ w
local notation "time" rotor:arg live:arg w:arg => DescentDatedSeedStartup.Input.completeTicks G rotor X live L_ h z_ w (k:=k_) (S:=S_)

/-- All archive banks here are the ones installed by the original program charged below. -/
theorem complete_position_at :
    ((V_).position G next t f g drift h).ports=
      DatePorts.initial G next X (S_).copies L_ k_ H ((S_).groupCount 0) h z_ :=rfl

theorem complete_invoice_at (w budget E : ℕ)
    (paid : CompleteAfterAt G op t f g reset drift degreeMax (quota t) τ B factor h)
    (dimension : next.n=op.n) (hosts : H=span M) (live : Fintype.card (DescentSeedRoot.Vertex X)≤H)
    (ambient : 2^h≤M) (degrees : degree≤degreeMax) (width : w+1≤factor*h) (budgetWidth : budget≤w) :
    let n:=DescentPackedSeed.rows X (S_).copies ((V_).width G) h
    ((4+(n+1)*66+7*DescentStaticWordColumn.names (flags w))+
      (time next live w+7*DescentStaticWordColumn.names (boot next live w)))*(budget+1)*2^J_ ≤
        4*((S_).copies*(V_).width G)*(M+2^J_*E) :=by
  have wide : Fintype.card (DescentSeedRoot.Vertex X)≤ span M:=live.trans_eq hosts
  dsimp only
  have fixed:=paid M degree w ((V_).base G h) ((S_).censusBits (V_).p) wire hist b_
    ambient degrees width X wide ds_ budget E budgetWidth
  have same:=DescentDatedSeedStartup.Input.boot_dimension G op X ds_ live L_ b_ h z_ w next dimension
  rw [same.1,same.2]
  subst H
  exact fixed

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
