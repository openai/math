import OAI.Hierarchy.ProtocolRAMCatalogueRowFields
import OAI.Hierarchy.ProbeReportPlacement
import OAI.Hierarchy.ProbeCoreBoard

namespace OAI
/-! # The fixed partition of all original terminal report ordinals -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage ProbeStage.CoreBoard
open scoped Classical
variable {h W k : ℕ} {S : PurchaseSampler}

/-- The physical core order stores the wire before the stage. The report
socket order stores the stage before the wire. -/
def Board.coreShape :
    Edges S h (2^W) k ≃ Free S h (2^W) k ⊕ ReportSockets.Core h W k :=
  Equiv.sumCongr (Equiv.refl _) ((Equiv.prodComm _ _).prodCongr (Equiv.refl _))

/-- All rows, including dormant acquisition attempts, are present. This
partition only reads the public ordinal, before any program is run. -/
def Board.partition (b : Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k) :
    Fin b.rows ≃ Free S h (2^W) k ⊕ (ReportSockets.Core h W k ⊕ Fin b.boughtRows) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (order.trans Board.coreShape) (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))

theorem Board.private_row (b : Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (f : Free S h (2^W) k) :
    b.partition order (b.coreIndex (order.symm (.inl f)))=.inl f := by
  change (Equiv.sumAssoc _ _ _) ((Equiv.sumCongr _ _) (finSumFinEquiv.symm
    (Fin.castAdd b.boughtRows (order.symm (.inl f)))))=_
  simp [Board.coreShape]

theorem Board.positive_core_row (b : Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (r : ReportSockets.Core h W k) :
    b.partition order (b.coreIndex (order.symm (.inr ((r.1.2,r.1.1),r.2))))=.inr (.inl r) := by
  change (Equiv.sumAssoc _ _ _) ((Equiv.sumCongr _ _) (finSumFinEquiv.symm
    (Fin.castAdd b.boughtRows (order.symm (.inr ((r.1.2,r.1.1),r.2))))))=_
  simp [Board.coreShape]

theorem Board.bought_row (b : Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (i : Fin b.boughtRows) : b.partition order (b.boughtIndex i)=.inr (.inr i) := by
  change (Equiv.sumAssoc _ _ _) ((Equiv.sumCongr _ _) (finSumFinEquiv.symm
    (Fin.natAdd b.coreRows i)))=_
  simp

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
