import OAI.Hierarchy.DescentOrderedMixedRouter
import OAI.Hierarchy.DescentOrderedResetTrunks
import OAI.Hierarchy.DescentTrunkReadout

namespace OAI
/-! # Reenter the realized reset with ordered signed scalar tables -/

namespace Hierarchy.DescentResetTrunks.Ordered
open DescentSixParty DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P H Q : Type} [Field F] [Fintype H] [Fintype Q] {n d L : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
  (legacy sorted : R.Tables F) (key : A.graph.Edge↪Fin L)
local notation "W" => DescentResetTrunks.install A home group hub same R legacy

def installedTables : (W).graph.Tables F := by
  subst w
  exact tables A.graph home group R key A.tables sorted

omit [Fintype Q] in
theorem installed_value (bank : ∀p,R.value sorted p=
    if DescentOrderedReset.words key (group false) w (fun r=>p (false,r)) =
       DescentOrderedReset.words key (group true) w (fun r=>p (true,r)) then 1 else 0)
    (pins : Ports bits) :
    (W).graph.value (installedTables A home group hub same R legacy sorted key) pins=A.value pins := by
  subst w
  exact value A.graph home group R key A.tables sorted bank pins

end
end Hierarchy.DescentResetTrunks.Ordered

namespace Hierarchy.DescentSixParty.ResetInput
open DescentChosenRouter DescentResetTrunks DescentMixedRouter
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d L : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
  {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z) (key : A.graph.Edge↪Fin L)
local notation "R" => Z.placement
local notation "S" => selected R Z.graph Z.positive Z.pay Z.circuit
local notation "same" => funext (fun e => Eq.symm (Z.allWidths e))
local notation "W" => reenter Z T

def orderedBank : Z.bank.Tables F := DescentMixedRouter.Ordered.coefficients (K:=F) (C₀:=C)
  Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align key d S

def orderedReentry : MarkedWorld F d P bits :=
  { (W) with
    tables := DescentResetTrunks.Ordered.installedTables
      A T.home (R).input T.hub same Z.bank Z.tables (orderedBank Z key) key }

theorem orderedReentry_value (x : Ports bits) : (orderedReentry Z T key).value x=A.value x :=
  DescentResetTrunks.Ordered.installed_value A T.home (R).input T.hub same Z.bank Z.tables
    (orderedBank Z key) key (DescentMixedRouter.Ordered.value (K:=F) (C₀:=C)
      Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align key d S) x

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
