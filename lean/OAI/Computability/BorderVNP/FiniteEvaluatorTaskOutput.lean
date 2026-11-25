import OAI.Computability.BorderVNP.FiniteEvaluatorTaskCubeChoices

/-! # The exact intermediate RAM of every returned finite report history

Each actual task return came from a published seven-word task table on its
own observed scalar-report bits. The supplemental splice writes the final
RAM from that specific table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.TaskReadback

open VPVNP.BurstRAM RoutingISA CellPacket.Supplement
open scoped Classical
open private rebit_inputs bits_rebit from OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsInverse

variable {w n b h K s : ℕ} {F : Type*} [Fintype F]
  (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (Y : CubePacket.Inputs n b h K s F)
  (report : Reports.Layout) (rows : List Reports.Row) (tasks : TypedTaskBuilder.Layout)
  (supp : ℕ → Batch.Cell) (count controls : ℕ) (bank : Bank w) (mem : Memory w)
  (start : Setup pub mem report rows tasks supp count controls)
  {packet cell deck stop : ℕ} (placed : Placement pub Y report rows tasks supp count packet cell deck stop)
  (original : CubePacket.Prepared Y pub mem)

include start placed original in
/-- Reconstruction from any native return of the report, task writer and splice.
The recovered prefix and its published data are at the real cutoff immediately
before that splice. -/
theorem return_image (x : Evaluator.Returns prepareTasks pub mac bank mem) :
    let stream := x.val.1.flatMap TeamRAM.Event.choices
    ∃ middle : Memory w, readings middle=tasks.published (Reports.image report (Reports.rebit rows stream) (readings mem)) ∧
      x.val.2.2=Batch.written middle supp count := by
  let tape : ReportTape rows := ⟨_,choices_length pub mac report rows tasks supp count controls bank mem start x⟩
  obtain ⟨fields,room,launch⟩ := start.typed tape
  have inputs := rebit_inputs report report.headers rows (readings mem) tape.val tape.property.symm.le start.headers start.rooms start.apart
  obtain ⟨_,_,_,_,_,_,_,⟨middle,image,writes⟩,unique⟩ := run_image pub mac Y report (Reports.rebit rows tape.val)
    tasks supp count controls (placed.rebit pub Y report rows tasks supp count tape) bank mem original start.ptr
    ((Reports.rebit_length rows tape.val) ▸ start.seed) start.frame start.control
    ((Reports.rebit_length rows tape.val) ▸ start.endHeaders) inputs fields room launch
  have same : x.val.1.flatMap TeamRAM.Event.choices=(Reports.rebit rows tape.val).flatMap Reports.Row.bits := by
    rw [bits_rebit,List.take_of_length_le tape.property.le]
  exact ⟨middle,image,(unique _ _ _ x.property same).2.2.trans writes⟩

end FiniteEvaluator.TaskReadback

end BorderVNP
end Computability
end OAI
