import OAI.Hierarchy.DescentBoundedWorldHistory
import OAI.Hierarchy.DescentOrderedReentryBasic
import OAI.Hierarchy.DescentCanonicalBank
import OAI.Hierarchy.DescentTrunkBitHistory
import OAI.Hierarchy.DescentReentryGroupStage

namespace OAI
/-! # Local bit histories on the actual installed trivalent reset graph -/

namespace Hierarchy.DescentKernelHistory.BitDescription
open Computability.BorderVNP.Crossing DescentSixParty DescentResetTrunks DescentRouterBank DescentChosenRouter
open DescentRotor DescentContactTree DescentResetAttachments
open scoped Classical BigOperators
noncomputable section
variable {F H P Q : Type} [Field F] [Fintype H] [Fintype Q] {n d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F n P bits} (B : BitDescription W) (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q)
variable (flag : H→Bool)
def installed {L : ℕ} {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
    (legacy sorted : R.Tables F) (key : W.graph.Edge↪Fin L) {U : Type} (scalar : U→List (List Bool)→F)
    (r : SiteBits (U:=U) R) (valid : ReadsBits R scalar r sorted) :
    BitDescription
      { install W home group flag same R legacy with
        tables := DescentResetTrunks.Ordered.installedTables
          W home group flag same R legacy sorted key } := by
  subst w
  exact ⟨B.Tag⊕(Unit⊕U),trunkScalar B.scalar scalar,trunkBits W.graph home group R key B.recipe r,
    trunk_reads W.graph home group R key B.recipe r B.scalar scalar W.tables sorted B.correct valid⟩

variable {price ε : ℝ} {h C Ht L : ℕ} (Z : ResetInput W price ε h C Ht) (T : ResetInput.Terminals Z)
variable (key : W.graph.Edge↪Fin L)
local notation "R" => Z.placement

/-- A single physical bank and the actual sparse trunk key induce the whole
reset history. Every old node keeps precisely its original bit operands. -/
def fromBank {U : Type} (scalar : U→List (List Bool)→F) (r : SiteBits (U:=U) Z.bank)
    (valid : ReadsBits Z.bank scalar r (Z.orderedBank key)) : BitDescription (Z.orderedReentry T key) :=
  B.installed T.home (R).input T.hub (funext fun e=>(Z.allWidths e).symm) Z.bank Z.tables (Z.orderedBank key)
    key scalar r valid

def orderedReset (menu : ∀π,DescentRotor.Configures F Z.graph.arcs C Z.width π) : BitDescription (Z.orderedReentry T key) := by
  let chosen := DescentChosenRouter.selected R Z.graph Z.positive Z.pay Z.circuit
  let scalar := DescentResetGates.canonicalScalar Z.graph.arcs C Z.width
    (DescentRotor.rom Z.graph.arcs C Z.width (DescentRotor.fixedTable menu))
  let r := DescentCanonicalBank.recipe Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align key n chosen
  apply B.fromBank Z T key scalar r
  intro a x v
  have eqBit : bitInput Z.bank a x v=DescentResetGates.assignmentBit Z.bank a x v := by
    funext i;rcases i with ⟨_|_,j⟩ <;> rfl
  rw [eqBit]
  exact DescentCanonicalBank.recipe_read Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align key n menu chosen a x v


end
end Hierarchy.DescentKernelHistory.BitDescription

end OAI
