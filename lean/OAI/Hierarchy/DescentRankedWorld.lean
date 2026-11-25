import OAI.Hierarchy.DescentStageReindex
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # Whole histories expressed in their physically numbered old graph -/

namespace Hierarchy.DescentSixParty.PhysicalRename
open DescentPhysicalOrder Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F d P bits) (siteRank : A.graph.Site↪ℕ) (edgeRank : A.graph.Edge↪ℕ)

def rankedWorld := world A (rename siteRank) (rename edgeRank)

def rankedStage {G : PoweredGadget F} {u ε : ℝ} (I : StageInput A G u ε) : StageInput (rankedWorld A siteRank edgeRank) G u ε :=
  stage A (rename siteRank) (rename edgeRank) I

omit [Field F] in
/-- The ordinary whole-tape site ID in the renamed world is the offset
computed by prefixing the occupancy flags of the old site directory. -/
theorem siteCode (v : A.graph.Site) :
    (Fintype.equivFin (rankedWorld A siteRank edgeRank).graph.Site (rename siteRank v)).val=
      (Finset.univ.filter (fun u=>siteRank u<siteRank v)).card :=
  (congrArg Fin.val (code_rename siteRank v)).trans (physical_val siteRank v)

omit [Field F] in
theorem edgeCode (i : A.graph.Edge) :
    (Fintype.equivFin (rankedWorld A siteRank edgeRank).graph.Edge (rename edgeRank i)).val=
      (Finset.univ.filter (fun j=>edgeRank j<edgeRank i)).card :=
  (congrArg Fin.val (code_rename edgeRank i)).trans (physical_val edgeRank i)

variable (H : Histories F d P bits) (sites : ∀c,(H.state c).graph.Site↪ℕ) (edges : ∀c,(H.state c).graph.Edge↪ℕ)

/-- Reindex every actual branch, retaining its choice and coefficient. -/
def rankedHistory : Histories F d P bits where
  Choice := H.Choice
  finite := H.finite
  state c := rankedWorld (H.state c) (sites c) (edges c)
  weight := H.weight

theorem rankedHistory_value (x : Ports bits) : (rankedHistory H sites edges).value x=H.value x := by
  apply Finset.sum_congr rfl
  intro c _
  exact congrArg (H.weight c*·) (congrFun (value (H.state c) (rename (sites c)) (rename (edges c))) x)

def rankedHistoryStage {G : PoweredGadget F} {u ε : ℝ} (I : ∀c,StageInput (H.state c) G u ε) :
    ∀c,StageInput ((rankedHistory H sites edges).state c) G u ε :=
  fun c=>rankedStage (H.state c) (sites c) (edges c) (I c)

end
end Hierarchy.DescentSixParty.PhysicalRename

end OAI
