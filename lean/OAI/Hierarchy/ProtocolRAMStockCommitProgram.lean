import OAI.Hierarchy.ProtocolRAMCalendarRun
import OAI.Hierarchy.ProtocolRAMStockPortPlan
import OAI.Hierarchy.ProtocolRAMRepairCharges

namespace OAI
/-! # Executing the signed stock commit and preserving untouched memory -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

def StockCommit.charges (s : StockCommit) {q d : ℕ} (b : Batch q d) (rows : ℕ) : List Pass :=
  RepairHistogram.directColumns s.direct s.occurrences s.goods s.plan s.columns ++
  [⟨s.broadcast,rows,RepairHistogram.broadcastTerm b s.price⟩]

private theorem passes_frame {w : ℕ} (ps : List Pass) (m : Memory w) (x : ℕ)
    (safe : ∀ p∈ps,x<p.out ∨ p.out+p.rows≤x) : result ps m x=m x := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    rw [result,ih _ (fun t ht=>safe t (by simp [ht]))]
    rcases safe p (by simp) with low|high
    · simp [Pass.apply,image,fillSegment,not_le.mpr low]
    · simp [Pass.apply,image,fillSegment,not_lt.mpr high]

def StockCommit.native (s : StockCommit) {q d : ℕ} (w rows : ℕ) (b : Batch q d) : Commit w where
  native := (program w (s.charges b rows)).seq (RepairHistogram.commit w s.occurrences s.goods s.columns s.plan)
  ticks := clock (s.charges b rows)+RepairHistogram.commitTicks s.occurrences s.goods s.columns s.plan
  after := fun m=>RepairHistogram.commitOut s.columns s.plan s.occurrences s.goods (result (s.charges b rows) m)
  ready := fun m=> let u := result (s.charges b rows) m
                   (∀ p∈s.charges b rows,p.Fits w) ∧
                   RepairHistogram.CommitReady s.columns s.plan w s.occurrences s.goods u ∧
                   ∀ i : Fin s.occurrences,s.plan.bank.base≤RepairHistogram.address s.columns u i ∧
                     RepairHistogram.address s.columns u i≤ s.plan.bank.base+s.goods
  runs := by
    rintro m ⟨columns,mounted,_⟩
    apply Procedure.Exec.then (program_exec _ _ columns)
    intro P R K machine pc reg pub exit installed data cfg start entry same
    exact RepairHistogram.commit_exec s.columns s.plan _ mounted machine pc reg pub exit installed data cfg start entry same
  cheap := @cheap_seq w (program w (s.charges b rows)) (RepairHistogram.commit w s.occurrences s.goods s.columns s.plan)
    (@program_cheap w (s.charges b rows)) (@RepairHistogram.commit_cheap w s.occurrences s.goods s.columns s.plan)
  keeps := fun x=>RepairHistogram.commit_keeps s.plan s.occurrences s.goods x ∧
    ∀ p∈s.charges b rows,x<p.out ∨ p.out+p.rows≤x
  frame := by
    rintro m x ⟨_,_,targets⟩ ⟨keep,archive⟩
    exact (RepairHistogram.commit_frame s.columns s.plan _ _ _ x targets keep).trans
      (passes_frame _ _ _ archive)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
