import OAI.Hierarchy.DescentTrunkNodeOrder
import OAI.Hierarchy.DescentBundleReentry
import OAI.Hierarchy.DescentDenseHostTape
import OAI.Hierarchy.DescentBatchedNodeOrder
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Dense public birth rows on the actual ordered and lane-batched reset -/

namespace Hierarchy.DescentKernelHistory.NodeOrder
open DescentSixParty DescentRotor DescentResetTrunks DescentRouterBank DescentNamedContact
open Computability.BorderVNP.Crossing DescentResetAttachments
open scoped Classical BigOperators
noncomputable section
variable {F Y P H Q : Type} [Field F] [Fintype H] [Fintype Q] {n d L : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F n P bits} (B : BitDescription W)
section Installation
variable (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q) (flag : H→Bool)
variable {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
    (legacy sorted : R.Tables F) (key : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
    (r : SiteBits (U:=Y) R) (valid : ReadsBits R scalar r sorted)

def installedNames : All (B.installed home group flag same R legacy sorted key scalar r valid) ≃
    All B ⊕ (W.graph.Edge ⊕ Global r) := by
  subst w
  exact trunkNames W.graph home group R key B.recipe r

end Installation

variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput W price ε h C Ht) (T : ResetInput.Terminals Z) (key : W.graph.Edge↪Fin L)
    (m p : ℕ) (hp : 0<p) (fit : Z.unit=m*p)
    (menu : ∀π,Configures F Z.graph.arcs C Z.width π)
local notation "program" => Z.laneRecipe key m p hp fit
local notation "scale" => DescentLaneGates.scalar Z.graph.arcs C Z.width p (rom Z.graph.arcs C Z.width (fixedTable menu))
local notation "afterReset" => B.batchedReset Z T key m p hp fit menu

/-- The recovered common host and block label name each real bank site. -/
def bankLocation {S : ℕ} (vertex : Z.V↪Fin S) : Z.bank.Site↪ℕ where
  toFun v:=let u:=(Z.resetNames T).symm (.inr v)
    (finProdFinEquiv ((Z.hostTape T vertex).order (Z.placed T u),Z.blockId T u)).val
  inj' := by
    intro v w eqn
    have e:=finProdFinEquiv.injective (Fin.ext eqn)
    have hu := Z.place_unique T ((Z.hostTape T vertex).order.injective (congrArg Prod.fst e)) (congrArg Prod.snd e)
    exact Sum.inr.inj ((Z.resetNames T).symm.injective hu)

/-- The actual instruction ordinal inside a lane program follows all preceding
programs at completed common-host and block positions. -/
def bankOrdinal {S : ℕ} (vertex : Z.V↪Fin S) : Global program≃Fin (∑v,Fintype.card ((program v).Node)) :=
  (Equiv.sigmaCongrRight fun v=>Z.laneNodeOrder key m p hp fit v).trans
    (ProtocolRAMPortRanks.enumerate _ (bankLocation Z T vertex) (bankLocation Z T vertex).injective)

def fromBankOrdinal {S a c : ℕ} (vertex : Z.V↪Fin S) (old : All B≃Fin a) (edge : W.graph.Edge≃Fin c) :
    All afterReset ≃ Fin (a+(c+∑v,Fintype.card ((program v).Node))) :=
  (installedNames B T.home Z.placement.input T.hub (funext fun e=>(Z.allWidths e).symm) Z.bank
    Z.tables (Z.orderedBank key) key scale program (Z.lane_valid key m p hp fit menu)).trans
    ((Equiv.sumCongr old ((Equiv.sumCongr edge (bankOrdinal Z T key m p hp fit vertex)).trans
      finSumFinEquiv)).trans finSumFinEquiv)

end
end Hierarchy.DescentKernelHistory.NodeOrder

end OAI
