import OAI.Hierarchy.DescentReachedSignedPublicPointer

namespace OAI
/-! Transport the first public bit-block pointer from the graph on the issued
tape back to its physically reached graph along the single normalization equality. -/
namespace Hierarchy.DescentSixParty.Reached
open DescentKernelHistory DescentBundleHistory DescentCompiler DescentStageEdgeReceipt DescentSharedCableNames
open DescentOperandStateBanks DescentPackedOperand DescentPacking Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z degree wire hist p : ℕ}
  (cap : Reached W G q ε S k age z degree wire hist)
  (same : W=W') (hp : 0<p)
local notation "A₁" => cast (congrArg (fun U=>GroupStage U G q ε (Fin (S.groupCount age)) cap.V k) same) cap.placement
local notation "rank" => groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding)
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k rank

def originalSite (v : W'.graph.Site) : W.graph.Site :=
  cast (congrArg (fun U:MarkedWorld F d P bits=>U.graph.Site) same.symm) v

theorem original_cell (v : W'.graph.Site) :
    (A₁).pos v=cap.placement.pos (originalSite same v) ∧ (A₁).block v=cap.placement.block (originalSite same v) :=by
  subst W'
  exact ⟨rfl,rfl⟩

def originalIncident (v : W'.graph.Site) (edge : Incident W'.graph v) :
    Incident W.graph (originalSite same v) := by
  subst W'
  exact edge

omit [_root_.Field F] in
theorem original_fit (v : W'.graph.Site) (edge : Incident W'.graph v) (low : ℕ)
    (fits : (low+1)*p≤W'.graph.width edge.val) :
    (low+1)*p≤W.graph.width (originalIncident same v edge).val :=by
  subst W'
  exact fits

theorem firstCable_on_tape (dated : originalId W.graph.Edge=cap.order.trans Fin.valEmbedding)
    (valid : (A₁).StateBounds S age) (v : W'.graph.Site) (edge : Incident W'.graph v) (low : ℕ)
    (fits : (low+1)*p≤W'.graph.width edge.val) (g : Stage.Grain A₁) (named : g.1=edge.val) :
    let side:=decide (W'.graph.src edge.val≠v)
    let start : Stage.Grain A₁:=⟨g.1,⟨0,Nat.zero_lt_of_lt g.2.isLt⟩⟩
    let wing:=Public.endpoint A₁ (originalId W'.graph.Edge) S valid names side start
    cap.firstCable hp (originalSite same v) (originalIncident same v edge) low (original_fit same v edge low fits)=
      .cable wing.neighbor.val wing.wire.val low :=by
  subst W'
  rcases g with ⟨ee,j⟩
  dsimp only at named
  subst ee
  rw [dated]
  exact cap.firstCable_endpoint hp v edge low fits (Nat.zero_lt_of_lt j.isLt)

end
end Hierarchy.DescentSixParty.Reached

end OAI
