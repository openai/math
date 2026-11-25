import OAI.Computability.BorderVNP.FiniteEvaluatorSparseTaskReturns
import OAI.Computability.BorderVNP.FragmentRowsBucketProgram
import OAI.Computability.BorderVNP.DiagonalNativeSparseProtection

/-! # The actual physical words across sparse finite task preparation

The emitter and bucket operands are constructed from the real arena and its
37 published control words. The following readbacks identify both encoded
task operands, the compressed bit bank, and the retained cube input words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM

/-- The earlier signed arena publication determines all stable-bucket bases,
the true number of occupied rows, and their word-address bounds. -/
noncomputable def FragmentDirectoryInput.ofPublishedSignedArena {w : ℕ} (pub : Arg → Word w) (m : Memory w)
    (a : SignedTaskArena.Layout) (ctl u v k : ℕ)
    (fit : (FragmentRows.Layout.fromFrame (readings pub 0) (readings m)).Fits w (readings m))
    (ptr : readings m (readings pub 0+92)=ctl) (words : ∀ j : Fin 37, readings m (ctl+j.val)=a.controls j.val)
    (low : readings pub 0+112≤ctl) (below : ctl+37≤a.fragments.quads)
    (cables : (FragmentRows.Layout.fromFrame (readings pub 0) (readings m)).host.count=a.cube.cables)
    (raw : readings m (readings pub 0+9)≤a.cube.maxRows) (cells : readings m (readings pub 0+11)=a.cube.cells)
    (high : a.endAddress w u v k<2^w) : FragmentDirectoryInput pub m := by
  let f := FragmentRows.Layout.fromFrame (readings pub 0) (readings m)
  let b := a.fragments.bucket (f.stream (readings m)).length
  obtain ⟨room,header,frame,control⟩ := FragmentArena.bucket_after_emitter a (readings m) ptr words low below cables raw high
  refine ⟨f,b,ctl,rfl,fit,?_,rfl,cells.symm,room,header,frame,control⟩
  change a.fragments.quads=readings m (readings m (readings pub 0+92)+28)
  rw [ptr]
  exact (words (28 : Fin 37)).symm

end RoutingISA.Evaluator.ScheduleClock

namespace FiniteEvaluator.SparseTasks

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM CellPacket.Supplement

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
variable (X : Inputs pub m)

/-- The three true task-builder operands suffice for the computed compact word
publication, prior to establishing the supplemental and sparse entry conditions. -/
theorem Inputs.built_of_bucket (mac : TeamOpcode.Macros w 8) (bank : Bank w) (sorted : Memory w)
    (output : readings sorted=X.bucketImage) (frame : (pub 0).val=X.tasks.frame)
    (fields : X.tasks.Fields X.bucketImage) (room : X.tasks.Room X.bucketImage w) :
    readings X.built=X.tasks.published X.bucketImage := by
  obtain ⟨_,_,built,_,_,words⟩ := TypedTaskBuilder.program_run pub mac bank sorted X.tasks frame
    (output ▸ fields) (output ▸ room)
  have actual : readings built=X.tasks.published X.bucketImage := words.trans (congrArg X.tasks.published output)
  funext a
  change (word w (X.tasks.published X.bucketImage a)).val=X.tasks.published X.bucketImage a
  exact word_val _ _ ((congrFun actual a) ▸ (built a).isLt)

/-- The actual typed word memory has exactly the seven-word task publication
computed on the stable bucket, including the global call owners and compact count. -/
theorem Inputs.built_words (ready : X.Ready) (mac : TeamOpcode.Macros w 8) (s : Bank w) :
    readings X.built=X.tasks.published X.bucketImage := by
  obtain ⟨v,_,sorted,_,_,_⟩ := run_visits X ready mac s
  exact X.built_of_bucket mac v.bucket.val.2.1 v.bucket.val.2.2 sorted ready.taskFrame ready.taskFields ready.taskRoom

/-- All words below the fragment reservations except the one published count
are retained from the actual post-report RAM. -/
theorem Inputs.bucket_below (a : ℕ) (low : a<X.fragments.layout.quads)
    (clear : a≠X.fragments.layout.control+29)
    (pairs : a<X.fragments.bucket.pairs) (triples : a<X.fragments.bucket.triples)
    (cursors : a<X.fragments.bucket.cursors) : X.bucketImage a=readings m a := by
  unfold Inputs.bucketImage FragmentBucket.Layout.wordImage
  simp only [not_le_of_gt pairs,not_le_of_gt triples,not_le_of_gt cursors,false_and,dite_eq_right,not_false_eq_true]
  exact FragmentArena.image_below X.fragments.layout (readings m) a low clear

/-- Words below the fragment arena, outside the task, supplemental and sparse
output rows, survive all five stages in the true returned word RAM. -/
theorem Inputs.word_below (ready : X.Ready) (ret : Returns SignedPrep.beforeTyped pub mac s m)
    (a : ℕ) (low : a<X.fragments.layout.quads) (clear : a≠X.fragments.layout.control+29)
    (pairs : a<X.fragments.bucket.pairs) (triples : a<X.fragments.bucket.triples)
    (cursors : a<X.fragments.bucket.cursors) (tasks : ¬X.tasks.outputAt a)
    (supp : ∀ i < X.count, (X.merge i).Outside a)
    (sparse : ∀ i < X.exterior.count, (X.owned i).Outside X.exterior i a) : ret.val.2.2 a=m a := by
  apply Fin.ext
  change readings ret.val.2.2 a=readings m a
  rw [(return_facts X ready ret).2.2,Inputs.image,SparseExterior.written_preserve X.exterior X.owned
    (readings X.patched) (i:=0) (Nat.zero_le _) a (fun j _ hj => sparse j hj)]
  change readings (Batch.written X.built X.merge X.count) a=readings m a
  have kept := congrArg Fin.val (Batch.preserve X.built X.merge (i:=0) (Nat.zero_le X.count) a (fun i _ hi => supp i hi))
  exact kept.trans ((congrFun (X.built_words ready mac s) a).trans
    ((Batch.task_published_outside X.tasks X.bucketImage a tasks).trans (X.bucket_below a low clear pairs triples cursors)))

/-- Read both published exterior operands and every actual compressed bit from
any five-stage return, at the exact task record and destination stride. -/
theorem Inputs.exterior_words (ready : X.Ready) (ret : Returns SignedPrep.beforeTyped pub mac s m)
    {original : ℕ → TypedBatch.Task} (safe : SparseExterior.Protected X.exterior X.owned original)
    (i : ℕ) (hi : i<X.exterior.count) :
    let l := X.exterior
    let o := X.owned i
    readings ret.val.2.2 (l.tasks+7*i+2)=o.dest l ∧
      readings ret.val.2.2 (l.tasks+7*i+3)=o.field.bytes.length ∧
      ∀ j : Fin o.field.bytes.length, readings ret.val.2.2 (o.dest l+j.val)=o.field.bytes[j].toNat := by
  intro l o
  have post := (return_facts X ready ret).2.2
  have later (a : ℕ) (apart : ∀ j, i < j → j < l.count → (X.owned j).Outside l j a) :
      readings ret.val.2.2 a=o.image l i (SparseExterior.written l X.owned (readings X.patched) i) a := by
    rw [post]
    exact SparseExterior.written_preserve l X.owned (readings X.patched) (i:=i+1) hi a (fun j h h' => apart j h h')
  have task (k : ℕ) (hk : k ∈ [2,3]) := later (l.tasks+7*i+k) (fun j hj h => safe.row i hi j h hj.ne' k hk)
  have counter : l.counts+o.global ≠ l.tasks+7*i+2 ∧ l.counts+o.global ≠ l.tasks+7*i+3 := safe.counter i hi
  have distinct : l.tasks+7*i+2 ≠ l.tasks+7*i+3 := by omega
  constructor
  · rw [task 2 (by decide),SparseExterior.Owned.image,Function.update_of_ne counter.1.symm,
      Function.update_of_ne distinct,Function.update_self]
  constructor
  · rw [task 3 (by decide),SparseExterior.Owned.image,Function.update_of_ne counter.2.symm,Function.update_self]
  · intro j
    have separate := safe.self i hi j.val j.isLt
    rw [later _ (fun k h h' => safe.bytes i hi j.val j.isLt k h' h.ne'),SparseExterior.Owned.image,
      Function.update_of_ne separate.2.2,Function.update_of_ne separate.2.1,Function.update_of_ne separate.1]
    exact CellPacketEncode.putDigits_read _ _ _ j

end FiniteEvaluator.SparseTasks

end BorderVNP
end Computability
end OAI
