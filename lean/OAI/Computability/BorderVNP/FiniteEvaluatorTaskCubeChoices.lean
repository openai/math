import OAI.Computability.BorderVNP.FiniteEvaluatorTaskCubeRun
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsInverse
import OAI.Computability.BorderVNP.DiagonalNativeSequence

/-! # Exact report tapes of the complete physical task preparation

Every report bit string of the public length yields one complete preparatory
history. Every actual returning history yields its own unique bit string and
the same protected cube operands, including at an empty report directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.TaskReadback

open VPVNP.BurstRAM RoutingISA CellPacket.Supplement DiagonalResidueRAM
open private shape rebit_inputs bits_rebit shape_ticks from OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsInverse

variable {w n b h K s : ℕ} {F : Type*} [Fintype F]
variable (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
variable (Y : CubePacket.Inputs n b h K s F) (reports : Reports.Layout) (rows : List Reports.Row)
variable (tasks : TypedTaskBuilder.Layout) (supp : ℕ → Batch.Cell) (count controls : ℕ)

/-- The complete true guess stream for one native owned-report directory. -/
abbrev ReportTape (rows : List Reports.Row) := {bs : List Bool // bs.length=Reports.capacity rows}

omit [Fintype F] in
/-- Replacing report values by any stream of the genuine public length preserves
the addresses, stored lengths, and all patch separations. -/
theorem Placement.rebit {packet cell deck stop : ℕ}
    (placed : Placement pub Y reports rows tasks supp count packet cell deck stop) (t : ReportTape rows) :
    Placement pub Y reports (Reports.rebit rows t.val) tasks supp count packet cell deck stop := by
  refine ⟨placed.frame,placed.ordered,placed.operands,placed.reportCounts,?_,placed.outputs,placed.patch⟩
  intro r hr
  obtain ⟨j,eq⟩ := List.get_of_mem hr
  let k : Fin rows.length := Fin.cast (Reports.rebit_length rows t.val) j
  obtain ⟨_,base,can,len⟩ := shape rows t.val t.property.symm.le k
  have old := placed.reportBits (rows.get k) (List.get_mem rows k)
  rw [← eq]
  change cell ≤ (Reports.rebit rows t.val)[k.val].base+(Reports.rebit rows t.val)[k.val].canonical ∧
    (Reports.rebit rows t.val)[k.val].base+(Reports.rebit rows t.val)[k.val].canonical+(Reports.rebit rows t.val)[k.val].bits.length ≤ deck
  simpa only [← base,← can,← len,Reports.Row.start,List.get_eq_getElem,Fin.getElem_fin] using old

variable (bank : Bank w) (m : Memory w)

/-- Source headers, arithmetic bounds and true supplemental sources before
executing any particular report choices. -/
structure Setup (pub : Arg → Word w) (m : Memory w) (reports : Reports.Layout) (rows : List Reports.Row)
    (tasks : TypedTaskBuilder.Layout) (supp : ℕ → Batch.Cell) (count controls : ℕ) : Prop where
  ptr : (pub 0).val=reports.frame
  seed : reports.Seed rows.length (readings m)
  frame : reports.frame+92 < 2^w
  control : reports.control+27 < 2^w
  endHeaders : reports.headers+6*rows.length < 2^w
  headers : ∀ i : Fin rows.length, rows[i].Stored (reports.headers+6*i.val) (readings m)
  rooms : ∀ i : Fin rows.length, rows[i].Fits reports w (reports.headers+6*i.val)
  apart : ∀ i j : Fin rows.length, i<j → ∀ k : Fin 3, rows[i].Outside reports (reports.headers+6*j.val+k.val)
  typed : ∀ t : ReportTape rows, let first := Reports.image reports (Reports.rebit rows t.val) (readings m)
    tasks.Fields first ∧ tasks.Room first w ∧ ∀ mt : Memory w, readings mt=tasks.published first → Launch pub tasks supp count controls mt

variable (start : Setup pub m reports rows tasks supp count controls)
local notation "Hist" => Evaluator.Returns prepareTasks pub mac bank m

include start in
/-- Every returning task program has the declared number of guesses, regardless
of their values or the recorded register and memory endpoint. -/
theorem choices_length (x : Hist) : (x.val.1.flatMap TeamRAM.Event.choices).length=Reports.capacity rows := by
  obtain ⟨u,mu,as,bs,eq,first,tail⟩ := Runs.seq_iff.mp x.property
  have read := Reports.prepare_cover pub mac bank m reports rows start.ptr start.seed start.frame start.control start.endHeaders
    start.headers start.rooms start.apart first
  have clean := tail.unsigned_events (by decide : (Code.seq TypedTaskBuilder.program Batch.entry).unsigned=true)
  rw [eq,List.flatMap_append,List.flatMap_eq_nil_iff.mpr (fun e he => (clean e he).1),List.append_nil]
  exact read.1

variable {packet cell deck stop : ℕ} (placed : Placement pub Y reports rows tasks supp count packet cell deck stop)
variable (original : CubePacket.Prepared Y pub m)

local notation "ticks" => Reports.setup.slots+Reports.ticks rows+TypedTaskBuilder.setup.slots+
  tasks.cells*(TypedTaskBuilder.body.slots+1)+19+62*count

include start placed original in
/-- The observed flattened report tape is a bijection, and every actual
preparation endpoint satisfies the cube lookup and the native clock. -/
theorem return_equiv :
    ∃ E : Hist ≃ ReportTape rows, ∀ x : Hist, (E x).val=x.val.1.flatMap TeamRAM.Event.choices ∧
      CubePacket.Prepared Y pub x.val.2.2 ∧ traceCost x.val.1 ≤ ticks := by
  let read (x : Hist) : ReportTape rows := ⟨_,choices_length pub mac reports rows tasks supp count controls bank m start x⟩
  have inject : Function.Injective read := by
    intro x y eq
    have tapes : x.val.1.flatMap TeamRAM.Event.choices=y.val.1.flatMap TeamRAM.Event.choices := congrArg Subtype.val eq
    obtain ⟨h1,h2,h3⟩ := unique_returns (c:=prepareTasks) (prepareTasks.program_tag_native (by decide)) x.property y.property
      (tail:=[]) (tail':=[]) (by simpa using tapes)
    exact Subtype.ext (Prod.ext h1 (Prod.ext h2 h3))
  have existsRun (t : ReportTape rows) : ∃ x : Hist, read x=t ∧ CubePacket.Prepared Y pub x.val.2.2 ∧ traceCost x.val.1 ≤ ticks := by
    obtain ⟨fields,room,launch⟩ := start.typed t
    have data := rebit_inputs reports reports.headers rows (readings m) t.val t.property.symm.le start.headers start.rooms start.apart
    obtain ⟨es,z,mz,r,bs,hc,cube,_⟩ := run pub mac Y reports (Reports.rebit rows t.val) tasks supp count controls
      (placed.rebit pub Y reports rows tasks supp count t) bank m original start.ptr
      ((Reports.rebit_length rows t.val) ▸ start.seed) start.frame start.control
      ((Reports.rebit_length rows t.val) ▸ start.endHeaders) data fields room launch
    refine ⟨⟨⟨es,z,mz⟩,r⟩,Subtype.ext ?_,cube,?_⟩
    · change es.flatMap TeamRAM.Event.choices=t.val
      rw [bs,bits_rebit,List.take_of_length_le t.property.le]
    · simpa only [shape_ticks t.property.symm.le] using hc
  refine ⟨Equiv.ofBijective read ⟨inject,fun t => (existsRun t).imp (fun _ h => h.1)⟩,fun x => ⟨rfl,?_⟩⟩
  obtain ⟨y,same,done⟩ := existsRun (read x)
  exact inject same ▸ done

end FiniteEvaluator.TaskReadback

end BorderVNP
end Computability
end OAI
