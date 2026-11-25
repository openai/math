import OAI.Hierarchy.DescentTerminalSiteLoads
import OAI.Hierarchy.DescentOccupiedActorLoads
import OAI.Hierarchy.DescentTrunkReadout

namespace OAI
/-! # Physical local balances carried with each chosen reset placement -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentChosenRouter DescentMixedRouter DescentGL DescentFineTerminals
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht)
variable (T : Terminals Z) (old : A.graph.Site→List H) (wire hist f g B : ℕ)
local notation "P₀" => Z.placement
local notation "whole" => bin T.home (A.siteUnits Z.hub old wire 256 hist)

structure ActorBudget : Prop where
  reserve : (wire:ℝ)*Z.pay≤((2^f*B:ℕ):ℝ)
  ordinary : ∀t,T.hub t=false→(whole t:ℝ)≤3*((2^f*B:ℕ):ℝ)/(2^Z.n:ℕ)
  hub : ∀t,T.hub t=true→whole t=2^g*B
  good : ∀s base,(wire:ℝ)*terminalWeight Z.unit (P₀).contact (P₀).owner s (.inl base)≤2*((2^f*B:ℕ):ℝ)
  reserve_exact : (wire:ℝ)*Z.pay=((2^f*B:ℕ):ℝ)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
