import OAI.Hierarchy.DescentTrunkBundleMaps
import OAI.Hierarchy.DescentBundleLanes
import OAI.Hierarchy.DescentBundleWorld
import OAI.Hierarchy.DescentBatchedReentry
import OAI.Hierarchy.DescentResetWorldHistory
import OAI.Hierarchy.DescentTrunkReadout

namespace OAI
/-! # The same complete operand words and bounded stride on the installed reset graph -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory Computability.BorderVNP.Crossing DescentOrderedWords DescentResetAttachments DescentNamedContact DescentRouterBank
open scoped Classical BigOperators
noncomputable section
variable {n d p R₀ : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) {L : ℕ} (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e) (hp : 0<p)
local notation "M" => DescentResetTrunks.network N home group R
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)
variable (src : ∀v,Shape p (old v)) (dev : ∀v,Shape p (bank v))
local notation "reads" => trunkBits N home group R key old bank

def inShape (h : H) : Shape p (oldProduct N home group R key old h) :=
  combined (oldGather N home group R key old h) Empty.elim (fun _=>Sum.inl)
    (oldGatherShape N home group R key whole old src h) (fun h => nomatch h)
    (fun _=>({map:=id,read:=fun _ _=>rfl} : BlockMap p _ _ id).publicOnly)

def trunkShape : (v : (M).Site)→Shape p (reads v)
  | .inl (false,h)=>(inShape N home group R key whole old src h).retag Sum.inl
  | .inl (true,h)=>(relayShape N home group R key whole hp h).retag (Sum.inr ∘ Sum.inl)
  | .inr v=>(bankPullbackShape N home group R key whole bank hp dev v).retag (Sum.inr ∘ Sum.inr)

omit [Fintype Q] in
theorem trunkStride (one : 1≤R₀)
    (pre : ∀v u j g,((src v).chunk u j g).stride≤R₀)
    (device : ∀v u j g,((dev v).chunk u j g).stride≤R₀) (v u j g) :
    ((trunkShape N home group R key whole hp old bank src dev v).chunk u j g).stride≤R₀ := by
  rcases v with ⟨_|_,h⟩|v
  · rcases u with ⟨⟨v,rfl⟩,u⟩
    exact pre v u j g
  · exact one
  · exact device v u j g

open DescentSixParty DescentResetTrunks DescentChosenRouter
variable {F : Type} [Field F] {W : MarkedWorld F n P bits} {B : BitDescription W}
def installedWorldShape (s : WorldShape p R₀ B) (hp : 0<p) (one : 1≤R₀)
    (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q) (hub : H→Bool)
    {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (board : Network d (Bool×Q) (publicWidth group w))
    (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
    (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted) (device : ∀v,Shape p (prog v))
    (bound : ∀v u j g,((device v).chunk u j g).stride≤R₀) (widths : ∀e,p∣board.width e) :
    WorldShape p R₀ (B.installed home group hub same board legacy sorted ids scalar prog valid) := by
  subst w
  exact ⟨trunkShape W.graph home group board ids s.edges hp B.recipe prog s.sites device,
    trunkStride W.graph home group board ids s.edges hp B.recipe prog s.sites device one s.stride bound,
    installed_divides W home group hub rfl board legacy p s.edges widths⟩


end
end Hierarchy.DescentBundleHistory

namespace Hierarchy.DescentKernelHistory.BitDescription
open DescentSixParty DescentRotor
noncomputable section
variable {F P : Type} [Field F] {n : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} (B : BitDescription W) (Z : ResetInput W price ε h C Ht)
    (T : ResetInput.Terminals Z) (key : W.graph.Edge↪Fin L) (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
    (menu : ∀π,Configures F Z.graph.arcs C Z.width π)

def batchedReset : BitDescription (Z.orderedReentry T key) :=
  B.fromBank Z T key (DescentLaneGates.scalar Z.graph.arcs C Z.width p (rom Z.graph.arcs C Z.width (fixedTable menu)))
    (Z.laneRecipe key m p hp fit) (Z.lane_valid key m p hp fit menu)

end
end Hierarchy.DescentKernelHistory.BitDescription

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty DescentRotor Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {n p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits}
variable {price ε : ℝ} {h C Ht L : ℕ} {B : BitDescription W}
def reentryWorldShape (s : WorldShape p R B) (Z : ResetInput W price ε h C Ht) (T : ResetInput.Terminals Z)
    (key : W.graph.Edge↪Fin L) (m : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
    (menu : ∀π,Configures F Z.graph.arcs C Z.width π) (one : 1≤R) (wide : max 1 (max Z.width (C*Z.width))≤R) :
    WorldShape p R (B.batchedReset Z T key m p hp fit menu) := by
  refine installedWorldShape s hp one T.home Z.placement.input T.hub
    (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables (Z.orderedBank key) key
    (DescentLaneGates.scalar Z.graph.arcs C Z.width p (rom Z.graph.arcs C Z.width (fixedTable menu)))
    (Z.laneRecipe key m p hp fit) (Z.lane_valid key m p hp fit menu)
    (fun v => ofProgram (fun b => boundaryWidth Z.bank v b / p)
      (Z.laneWidth_eq m p fit v) hp (Z.laneProgram key m p hp fit v)) ?_ ?_
  · intro v u j g
    exact (Z.lane_stride key m p hp fit v u j).trans wide
  · intro e
    exact Z.lane_dvd m p fit (Z.bank.src e) (.inl ⟨e,Or.inl rfl⟩)

end
end Hierarchy.DescentBundleHistory

end OAI
