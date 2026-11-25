import OAI.Hierarchy.TaggedWidePrograms
import OAI.Hierarchy.ProtocolRAMFrozenWindowCost
import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap
import OAI.Hierarchy.ProtocolRAMSumScoresCheap
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Exact assembly cost of the two native controllers -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical
variable {W m : ℕ} (l : Layout m)

theorem bank_cheap (k : ℕ) (parts : Fin (k+1)→Procedure W) (allowed : ∀i,CheapCode (parts i)) :
    CheapCode (ProcedureBank.program k parts) := by
  induction k with
  | zero => exact allowed 0
  | succ k ih => exact cheap_seq (allowed 0) (ih _ fun i=>allowed i.succ)

theorem bank_text (k : ℕ) (parts : Fin (k+1)→Procedure W) :
    text (ProcedureBank.program k parts)=∑i,text (parts i) := by
  induction k with
  | zero => simp [ProcedureBank.program]
  | succ k ih =>
    rw [ProcedureBank.program,text_seq,ih]
    exact (Fin.sum_univ_succ (fun i : Fin (k+1+1) => text (parts i))).symm

theorem Scatter.cheap (s : Scatter) (w : ℕ) : CheapCode (s.code w) :=
  cheap_seq (scan_cheap w s.base s.length (.lit 0))
    (ProtocolRAMRankCheap.generated w s.scratch (s.scratch+s.rows) s.rows s.address s.value)

/-- All chronological, format, and pruning rows are compiled with the fixed cheap opcode
set, including rows representing a wholly inactive group. -/
theorem Layout.finish_cheap (pfx : Procedure W) (paid : Bank) (prefixOk : CheapCode pfx)
    (terminalOk : CheapCode (l.terminal.code W paid)) : CheapCode (l.finish pfx paid) :=
  cheap_seq (cheap_seq (cheap_seq prefixOk (cheap_seq
    (bank_cheap l.scatterLast _ (fun i=>(l.scatter i).cheap W)) terminalOk))
      (bank_cheap m _ (fun i=>(l.windows i).cheap W (l.windowBase i) (l.inputs i))))
    (PruneFlag.cheap W l.pruneScratch l.pruneRows l.threshold l.prune)

theorem Layout.finish_text (pfx : Procedure W) (paid : Bank) :
    text (l.finish pfx paid)=
      ((text pfx+((∑i,text ((l.scatter i).code W))+text (l.terminal.code W paid)))+
        ∑i,text (l.banks W i))+
        text (SumScores.procedure W l.pruneScratch l.pruneRows l.threshold l.prune) := by
  simp only [Layout.finish,Layout.localCode,text_seq,bank_text]

theorem Layout.finish_time (start : ℕ) (paid : Bank) :
    l.ticks start paid=((start+((∑i,(l.scatter i).ticks)+l.terminal.ticks paid))+
      ∑i,l.windowTicks i)+(4+(l.pruneRows+1)*(42+2*l.prune.work)) := rfl

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
