import OAI.Hierarchy.ProtocolRAMRepairCommit

namespace OAI
/-! # Stock coordinates and the physical row/port enumeration of a committed ballot -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open scoped BigOperators Fin.CommRing Classical
noncomputable section

/-- The single commodity namespace of this stock pass is the one subsequently read by the
frozen market. Every signed commodity occurrence is accumulated before its one capped transfer. -/
structure StockCommit where
  occurrences : ℕ
  goods : ℕ
  columns : RepairHistogram.Columns
  plan : RepairHistogram.CommitPlan
  direct : ℕ
  broadcast : ℕ
  price : Bank

namespace StockCommit
variable {w q d rows : ℕ}

def liveRows (b : Batch q d) (m : Memory w) (rows : ℕ) :=
  Finset.univ.filter (fun j : Fin rows=>committed b m (j.val:Word w))

structure PortPlan (s : StockCommit) (b : Batch q d) (m : Memory w) (rows : ℕ) where
  enum : (Σ _ : Fin rows, Fin d) ≃ Fin s.occurrences
  owner : Bank
  data : Bank
  dest : Expr
  ball : Expr
  field : Expr
  tabs : Fin d→Fin q→Expr
  columns : s.columns=fromBatch owner data dest ball field b tabs
  site : ∀ e, ball.eval m (e.val:Word w)=((enum.symm e).1.val:Word w)
  localIndex : ∀ e, (field.eval m (e.val:Word w)).val=(enum.symm e).2.val
  portRoom : d≤2^w
  termRoom : q≤2^w
  copyRoom : b.copies<2^w
  sumRoom : q*b.copies<2^w

theorem PortPlan.off {s : StockCommit} {b : Batch q d} {m : Memory w} (P : PortPlan s b m rows)
    (e : Fin s.occurrences) (inactiveRow : (P.enum.symm e).1 ∉ liveRows b m rows) :
    installedBits s.columns m e=0 ∧ consumedBits s.columns m e=0 := by
  have skip : ¬committed b m (P.ball.eval m (e.val:Word w)) := by simpa [liveRows,P.site] using inactiveRow
  have read := fromBatch_read P.owner P.data P.dest P.ball P.field b P.tabs m (e.val:Word w)
    (P.enum.symm e).2 P.portRoom (P.localIndex e)
  have zero := inactive b (P.enum.symm e).2 m (P.ball.eval m (e.val:Word w)) (P.tabs (P.enum.symm e).2)
    P.termRoom P.copyRoom P.sumRoom skip
  simp only [installedBits,consumedBits,P.columns,read.1,read.2,zero.1,zero.2,Fin.val_zero,and_self]

theorem PortPlan.read {s : StockCommit} {b : Batch q d} {m : Memory w} (P : PortPlan s b m rows)
    (j : Fin rows) (i : Fin d) :
    installedBits s.columns m (P.enum ⟨j,i⟩)=((b.wire (P.tabs i)).eval m (j.val:Word w)).val ∧
    consumedBits s.columns m (P.enum ⟨j,i⟩)=((debit b i).eval m (j.val:Word w)).val := by
  let e := P.enum ⟨j,i⟩
  have idx : (P.field.eval m (e.val:Word w)).val=i.val :=
    (P.localIndex e).trans (by simp [e])
  have site : P.ball.eval m (e.val:Word w)=(j.val:Word w) := (P.site e).trans (by simp [e])
  obtain ⟨put,take⟩ := fromBatch_read P.owner P.data P.dest P.ball P.field b P.tabs m (e.val:Word w) i P.portRoom idx
  simp only [site] at put take
  exact ⟨by simpa only [installedBits,P.columns] using congrArg Fin.val put,
    by simpa only [consumedBits,P.columns] using congrArg Fin.val take⟩

end StockCommit
end
end Hierarchy.ProtocolRAM.Calendar

end OAI
