import OAI.Hierarchy.DescentResetWireTags
import OAI.Hierarchy.DescentOrderedResetRows
import OAI.Hierarchy.DescentReentryGroupStage
import OAI.Hierarchy.DescentOrdinaryEdgeTape

namespace OAI
/-! # Reset tape orders of the real reentered world and its ordinary cable units -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentRouterBank Computability.BorderVNP.Crossing
noncomputable section
variable {F P H Q : Type} [Field F] [Fintype H] [Fintype Q] {n d : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w)) (tab : R.Tables F)

def installedWireNames : (install A home group hub same R tab).graph.Edge ≃ ((Bool×A.graph.Edge)⊕(H⊕R.Edge)) := by
  subst w
  exact Equiv.refl _
end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCommonHost DescentResetTrunks DescentResetWireTags DescentOrderedReset DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "U" => ordinaryWorld Z T
local notation "cnt" => (fun e => Computability.BorderVNP.Crossing.Network.width (World.graph (MarkedWorld.toWorld W)) e / Z.unit)

def resetTag (vertex : Z.V↪ℕ) (old : A.graph.Edge ↪ℕ) : (W).graph.Edge↪ℕ :=
  (installedWireNames A T.home Z.placement.input T.hub
    (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables).toEmbedding.trans
    (assembled Z.placement vertex T.code Z.graph Z.positive Z.pay Z.circuit d old)

def resetHostTag (vertex : Z.V↪ℕ) : ↥(commonNames Z T)↪ℕ :=
  (Function.Embedding.subtype _).trans (hostTag vertex Z.graph)

variable (vertex : Z.V↪ℕ) (old : A.graph.Edge↪ℕ)

def outgoingTape : (U).graph.Edge≃Fin (Fintype.card (U).graph.Edge) :=
  chronological (W).graph (W).core cnt Z.unit (resetTag Z T vertex old) (resetTag Z T vertex old).injective

/-- Every chunk carries its own true piece offset after all pieces emitted by
strictly earlier reset wires. The old open tethers retain one row. -/
theorem outgoingTape_read (e : (U).graph.Edge) :
    let row := pieceUnit (W).graph (W).core cnt Z.unit e
    (outgoingTape Z T vertex old e).val=ProtocolRAMPortRanks.«prefix»
      (DescentCableUnbundling.span (W).graph (W).core cnt) (resetTag Z T vertex old) row.1+row.2.val := rfl

/-- Unit rows in a subsequent reset inherit exactly this chronological cable
order without rebuilding a new order on one realized subset. -/
def followingGrains (count : (U).graph.Edge→ℕ) :
    (Σe:(U).graph.Edge,Fin (count e))↪Fin (∑e,count e) :=
  grains (U) count (outgoingTape Z T vertex old).toEmbedding

theorem followingGrains_read (count : (U).graph.Edge→ℕ) (e : (U).graph.Edge) (j : Fin (count e)) :
    (followingGrains Z T vertex old count ⟨e,j⟩).val =
      DescentOrderedWords.offset (outgoingTape Z T vertex old).toEmbedding count e+j.val := rfl

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
