import OAI.Computability.VPVNP.PairSimulationBranchDecoder
import OAI.Computability.VPVNP.CompressorOnlineTraceInverse
import OAI.Computability.VPVNP.CompressorOnlineOrdinalInversion
import OAI.Computability.VPVNP.CompressorTermWorkerFootprint

/-! # Inverting the term selector of a valid physical online row

Each successful burst advances the term worker by one ordinal, including
bursts recovered from an arbitrary accepting path. The directory guard
therefore forces the exact motif count. The admitted term and its entire
list of burst choices are then recovered from the actual source execution.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms NetworkKernel BurstRAM
open CompressorRecords.Schedule CompressorRecords.Schedule.Online
open scoped Fin.CommRing
open private exact_length from OAI.Computability.VPVNP.CompressorOnlineOrdinalInversion

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w : ℕ} {X : State a g} {pass : StatePass A X b n} {o : PassOrigin B f hf pass}

/-- Bundle the control type with its physical machine table, so equality
of installed tables can be used even when the catalog indexes differ. -/
abbrev ProgramTable (w : ℕ) := (Q : Type) × BurstRAM.Program w Q

/-- The term-worker program paired with its control type, instantiated from the pass grid, the
demand and supply orders, and the input's four address words. -/
noncomputable def WorkerInput.table (I : WorkerInput o w) : ProgramTable w :=
  ⟨_,TermWorker.program (grid o).block (grid o).demandOrder.entries (grid o).supplyOrder.entries I.addr⟩

variable {d initial phases : ℕ} {C : Catalog d} {plan : Config C initial phases} {ports : Ports w}

/-- The program and control type installed for a directory row, obtained by instantiating its
catalog worker with the public words read from that row's input. -/
def sourceTable (C : Catalog d) (ports : Ports w) (r : Directory.Row d w) : ProgramTable w :=
  ⟨_, ((C r.worker).table.instantiate w (Directory.words C ports r.worker r.input)).program⟩

private theorem same_table {P T : Schedule.Pass} {w : ℕ} (x : Fin P.params → Word w) (y : Fin T.params → Word w)
    (hp : P = T) (hxy : ∀ j, x j = y (Fin.cast (congrArg Schedule.Pass.params hp) j)) :
    (⟨_,(P.table.instantiate w x).program⟩ : ProgramTable w) = ⟨_,(T.table.instantiate w y).program⟩ := by
  cases hp
  obtain rfl : x = y := funext hxy
  rfl

/-- Identify the installed source using just the selected catalog row
and its public operand words. -/
theorem WorkerInput.installed_of_words (I : WorkerInput o w) (r : Directory.Row d w)
    (code : C r.worker = TermWorker.motifPass (grid o).block (grid o).demandOrder.entries (grid o).e)
    (words : ∀ j, Directory.words C ports r.worker r.input j =
      TermWorker.motifData (grid o).block (grid o).demandOrder.entries (grid o).supplyOrder.entries w I.addr
        (Fin.cast (congrArg Schedule.Pass.params code) j)) : sourceTable C ports r = I.table :=
  same_table _ _ code words

private theorem of_length {m : ℕ} (xs : List (List Bool)) (len : xs.length=m) :
    ∃ t : Fin m → List Bool, List.ofFn t = xs := by
  subst m
  exact ⟨xs.get,List.ofFn_get _⟩

/-- An arbitrary valid selector row, with the term table installed on its
input addresses. The recipe's start, exclusive bound, and actual data
memory are the only inputs besides the machine and fuel identities. -/
theorem WorkerInput.validRow_unique (I : WorkerInput o w) (r : Directory.Row d w)
    (valid : r.Valid C ports) (installed : sourceTable C ports r = I.table)
    (fuel : r.fuel = I.fuel) (start : Directory.start C ports r.input = 0)
    (bound : (Directory.bound C ports r.input).val = o.motifCount)
    (memory : r.dataMemory C ports = I.memory) :
    r.choices.length = o.motifCount ∧ ∃! i : pass.step.Choice, r.choices = List.ofFn (workerTapes o w i) := by
  let G := grid o
  let P := TermWorker.program G.block G.demandOrder.entries G.supplyOrder.entries I.addr
  let stop := Directory.bound C ports r.input
  let pub := Directory.words C ports r.worker r.input
  let cursor (j : ℕ) : Word w := j
  have fit : o.motifCount < 2^w := bound ▸ stop.isLt
  have run := valid.sourceRun
  rw [fuel,start,memory] at run
  have swap := congrArg (fun table : ProgramTable w =>
    runSegment table.2 I.fuel (some 0) I.memory r.choices) installed
  have native : runSegment P I.fuel (some (cursor 0)) I.memory r.choices = some r.reports := swap ▸ run
  have frame := valid.frame
  rw [start,memory] at frame
  have active (j : ℕ) (hj : j < o.motifCount) : cursor j < stop := by
    change j % (2^w) < stop.val
    rw [Nat.mod_eq_of_lt (hj.trans fit),bound]
    exact hj
  have closed : stop ≤ cursor o.motifCount := by
    change stop.val ≤ o.motifCount % (2^w)
    rw [Nat.mod_eq_of_lt fit,bound]
  have progress (j : ℕ) (hj : j < o.motifCount) (mem : Memory w) (_ : True) (bits : List Bool)
      (rep : Report w) (ok : execute P I.fuel (P.start (cursor j)) mem bits = some rep) :
      rep.result = some (cursor (j+1)) ∧ True := by
    let i : Fin o.motifCount := ⟨j,hj⟩
    obtain ⟨hs,ht⟩ := I.addresses i
    have fitS : (TermWorker.source I.addr (cursor j)).val+G.d ≤ 2^w := hs.symm ▸ I.layout.sourceFits i
    have fitT : (TermWorker.base I.addr (cursor j)).val+2+G.e < 2^w := ht.symm ▸ I.layout.termFits i
    have h := (TermWorker.Footprint.call G.block G.demandOrder.entries G.supplyOrder.entries I.addr
      (cursor j) mem I.fuel bits rep fitS fitT ok).1
    exact ⟨by simpa only [cursor,Nat.cast_add,Nat.cast_one] using h,trivial⟩
  have len := exact_length P I.fuel ports r.worker pub stop cursor o.motifCount (fun _ _ => True)
    active closed progress 0 (Nat.zero_le _) I.memory trivial r.choices r.reports native frame
  have hlen : r.choices.length = o.motifCount := by simpa only [Nat.zero_add] using len
  obtain ⟨t,ht⟩ := of_length r.choices hlen
  have htRun : (I.run t).isSome := Option.isSome_iff_exists.mpr ⟨r.reports,by
    change runSegment P I.fuel (some 0) I.memory (List.ofFn t) = some r.reports
    rw [ht]; exact native⟩
  let value := I.termEquiv.symm ⟨t,htRun⟩
  have hvalue : List.ofFn (I.termEquiv value).val = r.choices :=
    (congrArg (fun v : I.Accepted => List.ofFn v.val) (I.termEquiv.apply_symm_apply ⟨t,htRun⟩)).trans ht
  refine ⟨hlen,value,hvalue.symm,fun j hj => ?_⟩
  apply I.termEquiv.injective
  exact Subtype.ext (List.ofFn_inj.mp (hj.symm.trans hvalue.symm))

/-- The accepted term also describes the data in the actual post-worker
memory. No new guess is made to choose the continuation state. -/
theorem WorkerInput.validRow_fields (I : WorkerInput o w) (r : Directory.Row d w)
    (valid : r.Valid C ports) (installed : sourceTable C ports r = I.table)
    (fuel : r.fuel = I.fuel) (start : Directory.start C ports r.input = 0)
    (bound : (Directory.bound C ports r.input).val = o.motifCount)
    (memory : r.dataMemory C ports = I.memory) :
    ∃ i : pass.step.Choice, I.decodePacket r.choices = some i ∧
      ∀ j, TermRecordScan.Fields (grid o).block (grid o).supplyOrder.entries (grid o).pPos
        ((batch o i).demand j) ((batch o i).choice j).val (I.layout.base j) (r.endMemory C ports) := by
  obtain ⟨_,i,hi,_⟩ := I.validRow_unique r valid installed fuel start bound memory
  obtain ⟨reports,hr,fields,_⟩ := I.selected_run i
  have actual := valid.sourceRun
  rw [fuel,start,memory,hi] at actual
  have same := congrArg (fun table : ProgramTable w =>
    runSegment table.2 I.fuel (some 0) I.memory (List.ofFn (workerTapes o w i))) installed
  have worker : I.run (I.termEquiv i).val = some r.reports := same.symm.trans actual
  have eq := Option.some.inj (hr.symm.trans worker)
  rw [eq] at fields
  refine ⟨i,(I.decodePacket_iff r.choices i).mpr hi.symm,?_⟩
  simpa only [Directory.Row.endMemory,memory] using fields

/-- The three entering control calls and the closing call do not change
the multiplicity of the term selected by the recovered row. -/
theorem WorkerInput.validStep_rowChoices (I : WorkerInput o w) (s : Run.Step d (initial+phases) w)
    {cap : ℕ} {m : Memory w} (valid : s.Valid plan ports cap m) (installed : sourceTable C ports s.row = I.table)
    (fuel : s.row.fuel = I.fuel) (start : Directory.start C ports s.row.input = 0)
    (bound : (Directory.bound C ports s.row.input).val = o.motifCount)
    (memory : s.row.dataMemory C ports = I.memory) :
    ∃! i : pass.step.Choice, rowChoices s.row = [] :: [] :: [] :: (List.ofFn (workerTapes o w i) ++ [[]]) := by
  obtain ⟨_,i,hi,hu⟩ := I.validRow_unique s.row valid.source installed fuel start bound memory
  refine ⟨i,by simp only [rowChoices,hi],fun j hj => hu j ?_⟩
  simpa only [rowChoices,List.cons.injEq,true_and,List.append_cancel_right_eq] using hj

/-- The reference input used by the semantic decoder can have its own
memory and private clock. For the recovered row, use the demand cells in
the actual post-launch RAM and the fuel installed by the calendar. The
canonical full-width tapes depend only on the pass and selected term. -/
theorem WorkerInput.decode_validStep (I : WorkerInput o w) (s : Run.Step d (initial+phases) w)
    {cap : ℕ} {m : Memory w} (valid : s.Valid plan ports cap m) (installed : sourceTable C ports s.row = I.table)
    (start : Directory.start C ports s.row.input = 0)
    (bound : (Directory.bound C ports s.row.input).val = o.motifCount)
    (data : TermRecordScan.Inputs (grid o).demandOrder.entries I.layout (termRows o).demand (s.row.dataMemory C ports))
    (budget : TermWorker.budget (grid o).block (grid o).d (grid o).e w X.maxWireWidth ≤ s.row.fuel) :
    ∃! i : pass.step.Choice, I.decodePacket s.row.choices = some i ∧
      rowChoices s.row = [] :: [] :: [] :: (List.ofFn (workerTapes o w i) ++ [[]]) := by
  let J : WorkerInput o w := { I with memory := s.row.dataMemory C ports, inputs := data, fuel := s.row.fuel, clock := budget }
  obtain ⟨_,i,hi,_⟩ := J.validRow_unique s.row valid.source installed rfl start bound rfl
  have decoded := (I.decodePacket_iff s.row.choices i).mpr hi.symm
  exact ⟨i,⟨decoded,by simp only [rowChoices,hi]⟩,fun j hj => Option.some.inj (hj.1.symm.trans decoded)⟩

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
