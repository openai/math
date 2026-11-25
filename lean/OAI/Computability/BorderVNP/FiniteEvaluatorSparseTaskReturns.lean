import OAI.Computability.BorderVNP.FragmentBucketWordImage
import OAI.Computability.BorderVNP.FiniteEvaluatorSparseProgram
import OAI.Computability.BorderVNP.FiniteEvaluatorTaskCubeRun
import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits

/-! # Native returns from the five public sparse task producers

The fragment emitter and stable sort determine every word of the task
builder's input. The builder publishes the compact task rows, the
supplemental pass patches their descriptors, and the sparse pass writes the
compressed exterior. All five runs use their predecessors' actual words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.SparseTasks

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM
open CellPacket.Supplement

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {s : Bank w} {m : Memory w}

/-- After the finite scalar guesser, the sparse finite evaluator uses the same
five native producers as the signed preparation before typed serialization. -/
theorem prepare_split : prepareSparseTasks = .seq prepareReports SignedPrep.beforeTyped := rfl

/-- Lengths, tables and occupied fragment rows used by the physical task
preparation on the scalar report's returned memory. -/
structure Inputs (pub : Arg → Word w) (m : Memory w) where
  /-- The fragment directory decoded from the public arguments and the returning scalar report memory. -/
  fragments : ScheduleClock.FragmentDirectoryInput pub m
  /-- Layout in which the typed builder publishes the compact task rows. -/
  tasks : TypedTaskBuilder.Layout
  /-- Number of seven-word tasks visited by the supplemental patch pass. -/
  count : ℕ
  /-- Base address of the four-word control records for supplemental descriptor patching. -/
  controls : ℕ
  /-- Supplemental cell descriptor indexed by task ordinal. -/
  merge : ℕ → Batch.Cell
  /-- Layout for the compressed exterior words written after task patching. -/
  exterior : SparseExterior.Layout
  /-- Owned exterior row used to write each task’s sparse input. -/
  owned : ℕ → SparseExterior.Owned

variable (X : Inputs pub m)

/-- Complete output of the fragment producer and its stable per-cell bucket. -/
noncomputable def Inputs.bucketImage : ℕ → ℕ :=
  let f := X.fragments
  let tags := f.layout.bucketTag f.fit f.bucket f.rows f.cells
  let fields := fun i => FragmentRows.fieldValue (f.layout.bucketRow (readings m) f.bucket f.rows i)
  f.bucket.wordImage tags fields (f.layout.image (readings m))

/-- Word RAM of the typed task builder, computed from the preceding bucket output. -/
noncomputable def Inputs.built : Memory w :=
  fun a => word w (X.tasks.published X.bucketImage a)

/-- Physical patched task descriptors immediately before sparse encoding. -/
noncomputable def Inputs.patched : Memory w := Batch.written X.built X.merge X.count

/-- Final word values, including the compressed exterior bits and their two
replacement operands in each seven-word task record. -/
noncomputable def Inputs.image : ℕ → ℕ :=
  SparseExterior.written X.exterior X.owned (readings X.patched) X.exterior.count

/-- Sum of the actual component allowances at the public loop bounds of the
fragment, task, supplemental and exterior writers. -/
noncomputable def Inputs.cost : ℕ :=
  ScheduleClock.fragmentDirectoryTicks X.fragments.layout (readings m) +
    (TypedTaskBuilder.setup.slots+X.tasks.cells*(TypedTaskBuilder.body.slots+1)+2) +
    (17+62*X.count) + (SparseExterior.setup.slots+
      (∑ i ∈ Finset.range X.exterior.count, (X.owned i).charge w)+1)

/-- Physical operands at the three successive computed memories. -/
structure Inputs.Ready : Prop where
  taskFrame : (pub 0).val=X.tasks.frame
  taskFields : X.tasks.Fields X.bucketImage
  taskRoom : X.tasks.Room X.bucketImage w
  supplement : TaskReadback.Launch pub X.tasks X.merge X.count X.controls X.built
  sparseFrame : (pub 0).val=X.exterior.frame
  sparseHeader : X.exterior.control+36<2^w
  sparseLoaded : X.exterior.Loaded (readings X.patched)
  sparseRows : ∀ i < X.exterior.count, (X.owned i).Initial X.exterior i X.patched
  independent : ∀ i < X.exterior.count, ∀ j < i, ∀ a,
    (X.owned i).Source X.exterior i a → (X.owned j).Outside X.exterior j a

/-- One normal execution at each boundary in the actual fixed native suffix. -/
structure Visits (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) where
  /-- Return of the fragment emitter from the original register bank and memory. -/
  rows : Returns FragmentRows.program pub mac s m
  /-- Return of the stable bucket pass on the emitted fragment rows. -/
  bucket : Returns FragmentBucket.program pub mac rows.val.2.1 rows.val.2.2
  /-- Return of the typed task builder on the bucketed fragment directory. -/
  typed : Returns TypedTaskBuilder.program pub mac bucket.val.2.1 bucket.val.2.2
  /-- Return of the supplemental pass that patches the descriptors referenced by the typed tasks. -/
  supplement : Returns Batch.entry pub mac typed.val.2.1 typed.val.2.2
  /-- Return of the exterior writer after supplemental descriptor patching. -/
  exterior : Returns SparseExterior.prepare pub mac supplement.val.2.1 supplement.val.2.2

/-- Chronological concatenation, carrying the actual last registers and RAM. -/
def Visits.join (v : Visits pub mac s m) : Returns SignedPrep.beforeTyped pub mac s m :=
  ⟨(v.rows.val.1++(v.bucket.val.1++(v.typed.val.1++(v.supplement.val.1++v.exterior.val.1))),v.exterior.val.2),
    v.rows.property.seq (v.bucket.property.seq (v.typed.property.seq (v.supplement.property.seq v.exterior.property)))⟩

/-- Exact chronological cost on the five returned event streams. -/
theorem Visits.cost (v : Visits pub mac s m) : traceCost v.join.val.1 =
    traceCost v.rows.val.1+traceCost v.bucket.val.1+traceCost v.typed.val.1+
      traceCost v.supplement.val.1+traceCost v.exterior.val.1 := by
  simp only [Visits.join,Transmission.cost_append]
  omega

/-- The genuine output, chronological cost and empty positive private tape. -/
def Inputs.ReturnImage (r : Returns SignedPrep.beforeTyped pub mac s m) : Prop :=
  TraceOK r.val.1 [] r.val.1.length ∧ traceCost r.val.1 ≤ X.cost ∧ readings r.val.2.2 = X.image

/-- All five actual executions, including the exact stable-bucket memory,
seven-word compact task publication and the physically patched descriptors. -/
theorem run_visits (ready : X.Ready) (mac : TeamOpcode.Macros w 8) (s : Bank w) :
    ∃ v : Visits pub mac s m, readings v.rows.val.2.2=X.fragments.layout.image (readings m) ∧
      readings v.bucket.val.2.2=X.bucketImage ∧ v.typed.val.2.2=X.built ∧
      v.supplement.val.2.2=X.patched ∧ X.ReturnImage v.join := by
  let f := X.fragments
  let tag := f.layout.bucketTag f.fit f.bucket f.rows f.cells
  let field := fun i => FragmentRows.fieldValue (f.layout.bucketRow (readings m) f.bucket f.rows i)
  obtain ⟨e₁,s₁,m₁,run₁,time₁,out₁⟩ := FragmentRows.program_run pub mac s m f.layout f.loaded f.fit
  change readings m₁=f.layout.image (readings m) at out₁
  obtain ⟨e₂,s₂,m₂,run₂,time₂,result⟩ := FragmentBucket.program_runs pub mac s₁ m₁ f.bucket tag field
    (readings pub 0) f.control f.room (out₁ ▸ f.layout.bucket_input f.fit f.bucket f.base f.rows f.cells)
    rfl (out₁ ▸ f.header) f.frame f.controlRoom
  have out₂ : readings m₂=X.bucketImage := (result.memory f.bucket tag field).trans
    (congrArg (f.bucket.wordImage tag field) out₁)
  obtain ⟨e₃,s₃,m₃,run₃,time₃,out₃⟩ := TypedTaskBuilder.program_run pub mac s₂ m₂ X.tasks ready.taskFrame
    (out₂ ▸ ready.taskFields) (out₂ ▸ ready.taskRoom)
  have built : m₃=X.built := by
    funext a
    apply Fin.ext
    have actual := congrFun (out₃.trans (congrArg X.tasks.published out₂)) a
    change (m₃ a).val = _ at actual
    change (m₃ a).val = (word w (X.tasks.published X.bucketImage a)).val
    rw [←actual,word_val _ _ (m₃ a).isLt]
  subst m₃
  have launch := ready.supplement
  obtain ⟨e₄,s₄,run₄,time₄,_,_⟩ := Batch.entry_run (pub:=pub) (mac:=mac) s₃ X.built X.merge f.frame
    launch.pointer launch.len launch.base launch.control launch.taskRoom launch.controlRoom launch.stored launch.apart
  obtain ⟨e₅,s₅,m₅,run₅,time₅,out₅,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) s₄ X.patched
    X.exterior X.owned ready.sparseFrame ready.sparseLoaded (ready.sparseFrame ▸ f.frame)
    ready.sparseHeader ready.sparseRows ready.independent
  let v : Visits pub mac s m := ⟨⟨(_,_,_),run₁⟩,⟨(_,_,_),run₂⟩,⟨(_,_,_),run₃⟩,⟨(_,_,_),run₄⟩,⟨(_,_,_),run₅⟩⟩
  have clean := v.join.property.unsigned_events (by decide)
  refine ⟨v,out₁,out₂,rfl,rfl,⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (clean e he).1,
    fun e he => (clean e he).2⟩,?_,out₅⟩
  rw [v.cost]
  change traceCost e₁+traceCost e₂+traceCost e₃+traceCost e₄+traceCost e₅ ≤ _
  change traceCost e₁ ≤ 256*(2*f.layout.host.count+f.layout.count+1) at time₁
  rw [f.cells,f.rows] at time₂
  unfold Inputs.cost ScheduleClock.fragmentDirectoryTicks
  change _ ≤ 256*(2*f.layout.host.count+f.layout.count+1)+(31+19*f.layout.cells+38*(f.layout.stream (readings m)).length)+_+_+_
  omega

/-- Determinism identifies the chronological trace, registers, and entire RAM
of any two normal returns of these five native stages. -/
theorem return_eq (a b : Returns SignedPrep.beforeTyped pub mac s m) : a=b := by
  obtain ⟨ev,reg,mem⟩ := a.property.unique_of_deterministic (by decide) b.property
  exact Subtype.ext (Prod.ext ev (Prod.ext reg mem))

/-- Exactly one physical suffix return from the genuine prepared report memory. -/
theorem return_unique (ready : X.Ready) (mac : TeamOpcode.Macros w 8) (s : Bank w) :
    ∃! r : Returns SignedPrep.beforeTyped pub mac s m, X.ReturnImage r := by
  obtain ⟨v,_,_,_,_,good⟩ := run_visits X ready mac s
  exact ⟨v.join,good,fun q _ => return_eq q v.join⟩

/-- Every returning sparse finite preparation has the actual computed word
memory and cost at this cut, independently of later private call choices. -/
theorem return_facts (ready : X.Ready) (r : Returns SignedPrep.beforeTyped pub mac s m) : X.ReturnImage r := by
  obtain ⟨q,hq,_⟩ := return_unique X ready mac s
  exact return_eq q r ▸ hq

end FiniteEvaluator.SparseTasks

end BorderVNP
end Computability
end OAI
