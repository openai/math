import OAI.ThreeFlat.RAM.HistoryStageBody

namespace OAI
/-! # Native guard tree and selected-owner loop for the receiver -/

namespace Hierarchy.HistorySelectedReceiverLoop
open ThreeFlat RAM RAM.PhysicalProcedure RAM.HistoryNodeDirectory
open RAM.HistoryStageBody.Physical
noncomputable section
variable {W : ℕ}

def body (u : ℕ) (bank : Archive) (leaf : Procedure W) (fs : List Family) : Procedure W :=
  fs.foldr (fun f next => ifValue (enabled u f)
    (HistoryStageBody.procedure (layout u bank f) f.childBound W) next) leaf

def selected (u : ℕ) (bank : Archive) (leaf : Procedure W) (fs : List Family) : Procedure W :=
  HistoryNodeDirectory.Selected.procedure (ownerData W u) (body u bank leaf fs)

end
end Hierarchy.HistorySelectedReceiverLoop

end OAI
