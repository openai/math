import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMStockCommitDebit

namespace OAI
/-! # Price labels and the stock seed retain each original cell before both writes -/
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ}

theorem stage_frame (a : Area) (s : Sources) (g : LabelSource) (m : Memory w) (x : ℕ) (low : x<g.out) (before : g.out≤a.start) :
    stageInput a s g m x=m x :=
  (a.seed_frame s _ x (.inl (low.trans_le before))).trans (ProtocolRAMGeneratedWrite.frame_image g.out a.occurrences ((g.geometry 5).atRow g.edge) m x (.inl low))

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM PurchaseStage
variable {w q goods : ℕ}

/-- The true existing stock, read by the seed and the priced commit, is also its
value at the chronological entry. This avoids a second old-stock input. -/
theorem postOutput_prior (C : Chart w q goods) (a : Attempt) (m : Memory w) (x : ℕ)
    (fit : ready C (.attempt a) m) (safe : protected C x (.attempt a)) :
    postOutput (C.layout a) (repair C a) (prepared C a m) x=m x := by
  have entire := after_frame C (.attempt a) m x fit safe
  rcases fit with ⟨_,_,_,_,_,_,_,_,_,_,commit,_,_⟩
  rcases safe with ⟨_,_,_,_,_,_,_,_,keep⟩
  exact ((C.commit a).frame _ x commit keep).symm.trans entire

end Hierarchy.ProtocolRAM.Calendar

end OAI
