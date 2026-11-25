import OAI.Computability.BorderVNP.FiniteEvaluatorTaskReadback
import OAI.Computability.BorderVNP.FiniteEvaluatorProgram
import OAI.Computability.BorderVNP.RoutingISATypedTaskProgram
import OAI.Computability.BorderVNP.CellPacketSupplementalBatch

/-! # Native task preparation retains the owned cube lookup

The finite report choices write their real bit banks. The ordinary task builder
reads that output, and the supplemental prepass uses the resulting descriptors.
Their joined trace consumes precisely the report choices and retains the field
cube data needed by the final private-return phase.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.TaskReadback

open VPVNP.BurstRAM RoutingISA CellPacket.Supplement DiagonalResidueRAM

variable {w n b h K s : ℕ} {F : Type*} [Fintype F]
variable (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
variable (Y : CubePacket.Inputs n b h K s F) (reports : Reports.Layout) (rows : List Reports.Row)
variable (tasks : TypedTaskBuilder.Layout) (supp : ℕ → Batch.Cell)
variable (count controls : ℕ)

/-- Real pointers, typed descriptor words and patch separations at the last
stage of task preparation. -/
structure Launch (pub : Arg → Word w) (tasks : TypedTaskBuilder.Layout) (supp : ℕ → Batch.Cell)
    (count controls : ℕ) (m : Memory w) : Prop where
  pointer : readings m ((pub 0).val+92)+11 < 2^w
  len : readings m ((pub 0).val+90)=count
  base : readings m ((pub 0).val+89)=tasks.tasks
  control : readings m (readings m ((pub 0).val+92)+11)=controls
  taskRoom : tasks.tasks+7*count ≤ 2^w
  controlRoom : controls+4*count ≤ 2^w
  stored : ∀ i<count, Batch.Stored (supp i) tasks.tasks controls i m ∧ Batch.Room (supp i) w
  apart : ∀ j<count, ∀ k<j, ∀ a ∈ (supp j).sources tasks.tasks controls j, (supp k).Outside a

/-- Starting with actual report headers and true sorted task operands, the three
stages have a unique run for the supplied guess string. Its actual splice
input contains the published tasks on the original report image. The final RAM retains
the full cube operands at the original addresses. -/
theorem run_image {packet cell deck stop : ℕ} (placed : Placement pub Y reports rows tasks supp count packet cell deck stop)
    (bank : Bank w) (m : Memory w) (original : CubePacket.Prepared Y pub m)
    (ptr : (pub 0).val=reports.frame) (seed : reports.Seed rows.length (readings m))
    (frame : reports.frame+92 < 2^w) (control : reports.control+27 < 2^w) (headers : reports.headers+6*rows.length < 2^w)
    (inputs : Reports.Inputs reports w rows reports.headers (readings m))
    (fields : tasks.Fields (Reports.image reports rows (readings m)))
    (room : tasks.Room (Reports.image reports rows (readings m)) w)
    (launch : ∀ mt : Memory w, readings mt=tasks.published (Reports.image reports rows (readings m)) →
      Launch pub tasks supp count controls mt) :
    ∃ es t mt, Runs pub mac prepareTasks bank m es t mt ∧
      es.flatMap TeamRAM.Event.choices=rows.flatMap Reports.Row.bits ∧
      traceCost es ≤ Reports.setup.slots+Reports.ticks rows+TypedTaskBuilder.setup.slots+
        tasks.cells*(TypedTaskBuilder.body.slots+1)+19+62*count ∧
      CubePacket.Prepared Y pub mt ∧
      (∃ two : Memory w, readings two=tasks.published (Reports.image reports rows (readings m)) ∧
        mt=Batch.written two supp count) ∧
      ∀ fs u mu, Runs pub mac prepareTasks bank m fs u mu → fs.flatMap TeamRAM.Event.choices=rows.flatMap Reports.Row.bits →
        fs=es ∧ u=t ∧ mu=mt := by
  obtain ⟨as,z,one,first,trace,cost₁,writes⟩ := Reports.prepare_run pub mac bank m reports rows ptr seed frame control headers inputs
  obtain ⟨bs,v,two,second,published,cost₂,clean₂,_⟩ := TypedTaskBuilder.native_program pub mac z one tasks placed.frame.symm
    (writes ▸ fields) (writes ▸ room)
  obtain ⟨hp,hn,hb,hc,ht,hr,stored,apart⟩ := launch two (published.trans (congrArg tasks.published writes))
  obtain ⟨cs,t,third,cost₃,clean₃,_⟩ := Batch.entry_run (pub := pub) (mac := mac) v two supp (ptr ▸ frame)
    hp hn hb hc ht hr stored apart
  have native : Runs pub mac prepareTasks bank m (as++(bs++cs)) t (Batch.written two supp count) := first.seq (second.seq third)
  have choices : (as++(bs++cs)).flatMap TeamRAM.Event.choices=rows.flatMap Reports.Row.bits := by
    rw [List.flatMap_append,List.flatMap_append,trace.2.1,
      List.flatMap_eq_nil_iff.mpr (fun e h => (clean₂ e h).1),List.flatMap_eq_nil_iff.mpr (fun e h => (clean₃ e h).1)]
    simp
  refine ⟨_,_,_,native,choices,?_,prepared pub Y placed original writes published,⟨two,published.trans (congrArg tasks.published writes),rfl⟩,?_⟩
  · rw [show traceCost (as++(bs++cs))=traceCost as+traceCost (bs++cs) from VPVNP.RAMBuckets.cost_append ..,
      show traceCost (bs++cs)=traceCost bs+traceCost cs from VPVNP.RAMBuckets.cost_append ..]
    omega
  · intro fs u mu other same
    exact unique_returns (c:=prepareTasks) (prepareTasks.program_tag_native (by decide)) other native (tail:=[]) (tail':=[]) (by simpa using same.trans choices.symm)

/-- Starting with actual report headers and true sorted task operands, the three
stages have a unique run for the supplied guess string. The final RAM retains
the full cube operands at the original addresses. -/
theorem run {packet cell deck stop : ℕ} (placed : Placement pub Y reports rows tasks supp count packet cell deck stop)
    (bank : Bank w) (m : Memory w) (original : CubePacket.Prepared Y pub m)
    (ptr : (pub 0).val=reports.frame) (seed : reports.Seed rows.length (readings m))
    (frame : reports.frame+92 < 2^w) (control : reports.control+27 < 2^w) (headers : reports.headers+6*rows.length < 2^w)
    (inputs : Reports.Inputs reports w rows reports.headers (readings m))
    (fields : tasks.Fields (Reports.image reports rows (readings m)))
    (room : tasks.Room (Reports.image reports rows (readings m)) w)
    (launch : ∀ mt : Memory w, readings mt=tasks.published (Reports.image reports rows (readings m)) →
      Launch pub tasks supp count controls mt) :
    ∃ es t mt, Runs pub mac prepareTasks bank m es t mt ∧
      es.flatMap TeamRAM.Event.choices=rows.flatMap Reports.Row.bits ∧
      traceCost es ≤ Reports.setup.slots+Reports.ticks rows+TypedTaskBuilder.setup.slots+
        tasks.cells*(TypedTaskBuilder.body.slots+1)+19+62*count ∧
      CubePacket.Prepared Y pub mt ∧
      ∀ fs u mu, Runs pub mac prepareTasks bank m fs u mu → fs.flatMap TeamRAM.Event.choices=rows.flatMap Reports.Row.bits →
        fs=es ∧ u=t ∧ mu=mt := by
  obtain ⟨es,t,mt,run,choices,cost,held,_,unique⟩ := run_image pub mac Y reports rows tasks supp count controls
    placed bank m original ptr seed frame control headers inputs fields room launch
  exact ⟨es,t,mt,run,choices,cost,held,unique⟩

end FiniteEvaluator.TaskReadback

end BorderVNP
end Computability
end OAI
