import OAI.Computability.BorderVNP.PackedSewnPhysicalHistoryCost
import OAI.Computability.BorderVNP.PackedTerminalStagedFields

/-! # The real post-sewing chronological source on the final staging bus -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Packing Packing.Inherited Packing.Inherited.FrozenTape Packing.CellAddressCircuit VPVNP.VerifierNetwork
open private oldWire staged_old from OAI.Computability.BorderVNP.PackedTerminalStagedFields

variable {Z H Out Γ : Type} [Fintype Z] [Fintype H] [Fintype Out] [Fintype Γ]
    {s w : ℕ} (history : Frame ((Z ⊕ Bool) ⊕ H) Out)

/-- Read the original geometry and the retained history while the same input
also exposes the newly computed post-sewing site extent. -/
noncomputable def stagedHistory : Frame (StagedWires Z s w ⊕ H) Out :=
  history.subst (Frame.initial (Sum.map oldWire id))

@[simp] theorem stagedHistory_size :
    (stagedHistory (s:=s) (w:=w) history).size = history.size := by
  simp [stagedHistory]

/-- The projected chronological bank reads exactly its original shared
inputs on every execution of the actual new-extent computation. -/
theorem stagedHistory_eval {m n C d k : ℕ} (F : Fields s m n C d k w (Z ⊕ Bool))
    (source : Frame Γ (Z ⊕ Bool)) (x : Γ → Bool) (h : H → Bool) :
    (stagedHistory history).eval (Sum.elim ((stagedSource F source).eval x) h) =
      history.eval (Sum.elim (source.eval x) h) := by
  funext o
  simp only [stagedHistory,Frame.subst_eval]
  congr 1
  funext z
  rcases z with z | z
  · exact (Frame.initial_eval ..).trans (staged_old F source x z)
  · exact Frame.initial_eval ..

end PackedHistoryCircuit.TerminalCells

namespace Packing.SewnField.Grid

open Crossing Inherited FrozenTape TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open CellAddressCircuit VPVNP.VerifierNetwork Shortening.PublicCapacity PackedHistoryCircuit.Normalized.SelectedSchedule
open PackedHistoryCircuit.TerminalCells

variable {R r t pins link inner n V groups copies : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies = R+1)
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
    {σ Geo : Type} [Fintype σ] [Fintype Geo] (shape : Shape) {C k w W : ℕ}
    (F : Fields shape.sites shape.edges (groups*V) C w k w σ) (name : ℕ → ℕ → ℕ)
    (present : Fin shape.edges → σ) (previous : Format) (original : ℕ)

/-- The actual history input for the signed packet on the staged bus. Both
the old-cable and team/tile operands have already been included in this bound. -/
theorem staged_physical_history_cubic (hw : w≤W)
    (logs : Nat.clog 2 (routingRows shape C original ((R+1)*V)) ≤ W) :
    let raw := physicalOperands G hV count hg small F name present
    let old := Sewn.terminalHistory (Geo:=Geo) previous F.sites raw
    (stagedHistory (s:=shape.sites) (w:=w) old).size ≤
      1463400*routingRows shape C original ((R+1)*V)*(W+1)^3 := by
  simpa only [stagedHistory_size] using
    terminal_physical_history_cubic (Geo:=Geo) G hV count hg small shape F name present previous original hw logs

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
