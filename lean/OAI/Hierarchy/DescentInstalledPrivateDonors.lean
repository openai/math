import OAI.Hierarchy.DescentPackedResetDonors
import OAI.Hierarchy.DescentResetAtomLedger

namespace OAI
/-! # The previous private operand donors of the physically installed ordered reset -/

set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty DescentResetTrunks DescentRouterBank DescentNamedContact Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P H Q Y : Type} [Field F] [Fintype H] [Fintype Q] {n d p bound L : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F n P bits} {B : BitDescription W} (src : WorldShape p bound B) (hp : 0<p) (one : 1≤bound)
variable (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q) (hub : H→Bool)
variable {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (board : Network d (Bool×Q) (publicWidth group w))
variable (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
variable (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted) (device : ∀v,Shape p (prog v))
variable (limit : ∀v u j g,((device v).chunk u j g).stride≤bound) (widths : ∀e,p∣board.width e)
local notation "out" => installedWorldShape src hp one home group hub same board legacy sorted ids scalar prog valid device limit widths
local notation "siteAt" => (DescentResetTrunks.installedNames W home group hub same board legacy).symm
local notation "used" q:arg => (((out).sites (siteAt q)).recipe hp).UsedWord

def installedDonors (h : H) : used (.inl (false,h)) ≃ (Σi : Fibre home h,((src.sites i.val).recipe hp).UsedWord) := by
  subst w
  exact resetDonor hp W.graph home group board ids src.edges B.recipe src.sites h

omit [Fintype Q] in
theorem relayEmpty (h : H) : IsEmpty (used (.inl (true,h))) := by
  subst w
  exact ⟨relay_no_private hp W.graph home group board ids src.edges h⟩

omit [Fintype Q] in
theorem deviceEmpty (v : board.Site) (void : IsEmpty (prog v).Hidden) : IsEmpty (used (.inr v)) := by
  subst w
  exact ⟨bank_no_private hp W.graph home group board ids src.edges device v void⟩

end
end Hierarchy.DescentBundleHistory

namespace Hierarchy.DescentSixParty.ResetInput
open DescentKernelHistory DescentBundleHistory DescentNamedContact DescentRotor
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {n p bound : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits} {B : BitDescription W}
    {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput W price ε h C Ht) (T : Terminals Z)
variable (src : WorldShape p bound B) (ids : W.graph.Edge↪Fin L) (m : ℕ) (hp : 0<p) (fits : Z.unit=m*p)
variable (menu : ∀π,Configures F Z.graph.arcs C Z.width π) (one : 1≤bound) (wide : max 1 (max Z.width (C*Z.width))≤bound)
local notation "out" => reentryWorldShape src Z T ids m hp fits menu one wide
local notation "siteAt" => (resetNames Z T).symm
local notation "used" q:arg => (((out).sites (siteAt q)).recipe hp).UsedWord

local notation "laneScalar" => DescentLaneGates.scalar Z.graph.arcs C Z.width p
  (rom Z.graph.arcs C Z.width (fixedTable menu))
local notation "laneShapes" => (fun v => ofProgram (fun b => boundaryWidth Z.bank v b / p)
  (Z.laneWidth_eq m p fits v) hp (Z.laneProgram ids m p hp fits v))
local notation "laneLimit" => (fun v u j _ => (Z.lane_stride ids m p hp fits v u j).trans wide)
local notation "laneWidths" => (fun e => Z.lane_dvd m p fits (Z.bank.src e) (.inl ⟨e,Or.inl rfl⟩))

def retainedPrivate (t : Z.Fallback) : used (.inl (false,t)) ≃ (Σv : Fibre T.home t,((src.sites v.val).recipe hp).UsedWord) :=
  installedDonors src hp one T.home Z.placement.input T.hub (funext fun e => (Z.allWidths e).symm)
    Z.bank Z.tables (Z.orderedBank ids) ids laneScalar (Z.laneRecipe ids m p hp fits)
    (Z.lane_valid ids m p hp fits menu) laneShapes laneLimit laneWidths t

theorem relayPrivate (t : Z.Fallback) : IsEmpty (used (.inl (true,t))) :=
  relayEmpty src hp one T.home Z.placement.input T.hub (funext fun e => (Z.allWidths e).symm)
    Z.bank Z.tables (Z.orderedBank ids) ids laneScalar (Z.laneRecipe ids m p hp fits)
    (Z.lane_valid ids m p hp fits menu) laneShapes laneLimit laneWidths t

theorem bankPrivate (v : Z.bank.Site) : IsEmpty (used (.inr v)) :=
  deviceEmpty src hp one T.home Z.placement.input T.hub (funext fun e => (Z.allWidths e).symm)
    Z.bank Z.tables (Z.orderedBank ids) ids laneScalar (Z.laneRecipe ids m p hp fits)
    (Z.lane_valid ids m p hp fits menu) laneShapes laneLimit laneWidths v ⟨fun z => nomatch z⟩

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
