import OAI.Computability.BorderVNP.FiniteEvaluatorSparseTaskReadback
import OAI.Computability.BorderVNP.FiniteEvaluatorSparseReports
import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeSource
import OAI.Computability.BorderVNP.DiagonalNativeSparseOriginals

/-! # Field-cell preparation on the actual patched and compressed RAM

The original chunk headers and private sections are read before the
supplemental splice. The sparse writer then replaces the exterior operands.
The same returned memory gives the owner, scalar report lengths, packet
descriptors and compressed bits required by the two finite private calls.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.SparseTasks

open VPVNP.BurstRAM RoutingISA Evaluator CellPacket CellPacket.Supplement

variable {w : ℕ} {pub : Arg → Word w} {m : Memory w} (X : Inputs pub m)

/-- Frame, count and scalar tail fields at the actual RAM after the supplemental patch. -/
structure PatchedFields (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (mem : Memory w) : Prop where
  frame : l.Fields (readings mem)
  width : readings mem (l.frame+30)=w
  count : readings mem (l.frame+90)=l.before raw l.cells
  owners : ∀ c < l.cells, readings mem (l.call c)=l.owner raw c
  tails : ∀ c < l.cells, readings mem (l.tails+c)=raw (l.tails+c)

/-- Transport the genuine task publication through the supplemental stores.
The rank and owner words come from the native builder on the exact stable
bucket image. The tail words remain the actual per-global-cell report sizes. -/
theorem Inputs.patched_fields {Site : Type} (ready : X.Ready) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (src : ℕ → Batch.Owned Site) (merge : X.merge=fun i => (src i).cell)
    (width : X.bucketImage (X.tasks.frame+30)=w)
    (control : ∀ k < 8, ¬X.tasks.outputAt (X.tasks.control+k))
    (apart : Reports.MetaOutside X.tasks X.count src) : PatchedFields X.tasks X.bucketImage X.patched := by
  let l := X.tasks
  have built := X.built_words ready mac s
  have keep (a : ℕ) (h : ∀ i < X.count, (src i).cell.Outside a) :
      readings X.patched a=l.published X.bucketImage a := by
    have original := congrArg Fin.val (Batch.preserve X.built X.merge (i:=0) (Nat.zero_le X.count)
      a (fun i _ hi => merge ▸ h i hi))
    exact original.trans (congrFun built a)
  have frame (k : ℕ) (hk : k < 112) (ne : k≠90) :
      readings X.patched (l.frame+k)=X.bucketImage (l.frame+k) :=
    (keep _ (fun i hi => (apart i hi).1 k hk)).trans (l.published_field X.bucketImage ready.taskRoom ne hk)
  have header (k : ℕ) (hk : k < 8) : readings X.patched (l.control+k)=X.bucketImage (l.control+k) :=
    (keep _ (fun i hi => (apart i hi).2.1 k hk)).trans (Batch.task_published_outside l X.bucketImage _ (control k hk))
  have live : l.Fields (readings X.patched) := by
    obtain ⟨a,b,c,d,e,f,g,h⟩ := ready.taskFields.outer
    obtain ⟨i,j,k,p,q,r,t,v⟩ := ready.taskFields.header
    exact ⟨⟨(frame 0 (by decide) (by decide)).trans a,(frame 7 (by decide) (by decide)).trans b,
      (frame 14 (by decide) (by decide)).trans c,(frame 15 (by decide) (by decide)).trans d,
      (frame 72 (by decide) (by decide)).trans e,(frame 87 (by decide) (by decide)).trans f,
      (frame 89 (by decide) (by decide)).trans g,(frame 92 (by decide) (by decide)).trans h⟩,
      ⟨(header 0 (by decide)).trans i,(header 1 (by decide)).trans j,(header 2 (by decide)).trans k,
       (header 3 (by decide)).trans p,(header 4 (by decide)).trans q,(header 5 (by decide)).trans r,
       (header 6 (by decide)).trans t,(header 7 (by decide)).trans v⟩⟩
  refine ⟨live,(frame 30 (by decide) (by decide)).trans width,?_,?_,?_⟩
  · exact (keep _ (fun i hi => (apart i hi).1 90 (by decide))).trans (Function.update_self ..)
  · intro c hc
    exact (keep _ (fun i hi => ((apart i hi).2.2 c hc).2)).trans (l.published_owner X.bucketImage ready.taskRoom hc)
  · intro c hc
    exact (keep _ (fun i hi => ((apart i hi).2.2 c hc).1)).trans
      (Batch.task_published_outside l X.bucketImage _ (ready.taskRoom.input c hc _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

/-- Genuine patched task headers, original descriptors and private chunk
sources suffice for both finite calls at the computed compressed memory. -/
theorem Inputs.cells_prepared {Site : Type} {F : Type*} [Fintype F] {n : ℕ}
    (ready : X.Ready) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (src : ℕ → Batch.Owned Site) (fields : ℕ → SparseExterior.Field) (digits : ℕ → ℕ)
    (claims : ∀ i, FiniteScalarRounds.Index F → Fin (digits i) → Bool)
    (merge : X.merge=fun i => (src i).cell) (width : X.bucketImage (X.tasks.frame+30)=w)
    (controlClear : ∀ k < 8, ¬X.tasks.outputAt (X.tasks.control+k)) (splice : Reports.MetaOutside X.tasks X.count src)
    (count : X.count=X.tasks.before X.bucketImage X.tasks.cells) (total : X.exterior.count=X.count)
    (table : X.exterior.tasks=X.tasks.tasks)
    (original : ∀ i < X.count, ScheduleClock.MergeFields (src i) X.tasks.tasks X.controls i X.built)
    (ranges : ScheduleClock.MergeRanges src X.count X.tasks.tasks X.controls)
    (safe : SparseExterior.Protected X.exterior X.owned (fun i => (src i).typed))
    (apart : Reports.SparseMetaOutside X.tasks X.exterior X.owned)
    (arenas : X.tasks.Arenas X.bucketImage w (fun i => (X.owned i).typed X.exterior (src i).typed))
    (control : X.tasks.SourceRange X.tasks.control 8) (tails : X.tasks.SourceRange X.tasks.tails X.tasks.cells)
    (call : ∀ i < X.count, (src i).callRow=X.tasks.call (TypedTaskBuilder.globalCell X.tasks X.bucketImage i))
    (zero : ∀ i < X.count, (src i).extra=[])
    (field : ∀ i < X.count, (X.owned i).field=fields (TypedTaskBuilder.globalCell X.tasks X.bucketImage i))
    (data : ∀ i < X.count, (X.owned i).field.tail=FiniteScalarRounds.stream F (claims i))
    (tail : ∀ i < X.count, X.bucketImage (X.tasks.tails+TypedTaskBuilder.globalCell X.tasks X.bucketImage i)=
      (FiniteScalarRounds.stream F (claims i)).length)
    (scalar : ∀ i < X.count, 2*digits i*Fintype.card F < CompactMachine.nativeClock n)
    (cap : ∀ i < X.count, (((X.owned i).typed X.exterior (src i).typed).cell.burst w).length≤TeamScales.width n (1/2))
    (legal : ∀ i < X.count, (src i).placed.directory.ProfileWidths ∧
      SparseExterior.clock w (src i).placed.directory (src i).placed.privateWires (X.owned i).field ≤ n^25) :
    let cells := Reports.sparseInputs X.tasks X.bucketImage (fun i => (X.owned i).supplemental X.exterior (src i)) fields digits claims
    Cells.Prepared cells pub X.imageMemory n (.sparse fields) ∧
      ∀ c < X.tasks.cells, readings X.imageMemory (X.tasks.call c)=X.tasks.owner X.bucketImage c := by
  intro cells
  let ret := (return_unique X ready mac s).exists.choose
  have final := (return_facts X ready ret).2.2
  have wordEq := X.eq_imageMemory ret.val.2.2 final
  have post : readings X.imageMemory=X.image := wordEq ▸ final
  have scalars := X.patched_fields ready mac s src merge width controlClear splice
  have source (i : ℕ) (hi : i < X.exterior.count) :
      (src i).typed.Stored X.patched X.exterior.tasks i ∧
      WordsAt (readings X.patched) (src i).typed.cell.descriptorBase (descriptors (src i).typed.cell.chunks) ∧
      ∀ c ∈ (src i).typed.cell.chunks, c.Stored (readings X.patched) := by
    rw [Inputs.patched,merge,table]
    exact ranges.sources X.built original i (total ▸ hi)
  have readyCells := Reports.sparsePrepared pub X.patched X.imageMemory X.tasks X.bucketImage src X.exterior
    X.owned fields digits claims ready.taskFrame scalars.frame scalars.width scalars.count (total.trans count) table post
    safe apart ready.taskRoom arenas control tails (fun i hi => (source i hi).1)
    (fun i hi => (source i hi).2.1) (fun i hi => (source i hi).2.2) scalars.owners
    (total ▸ call) (total ▸ zero) (total ▸ field) (fun i hi => field i (total ▸ hi) ▸ data i (total ▸ hi))
    (fun i hi => (scalars.tails _ (TypedTaskBuilder.global_spec X.tasks X.bucketImage (count ▸ total ▸ hi)).1).trans (tail i (total ▸ hi)))
    (total ▸ scalar) (total ▸ cap) (total ▸ legal)
  refine ⟨readyCells,?_⟩
  intro c hc
  have actual := SparseExterior.written_preserve X.exterior X.owned (readings X.patched) (i:=0)
    (Nat.zero_le X.exterior.count) (X.tasks.call c) (fun j _ hj => ((apart j hj).2.2 c hc).2)
  exact (congrFun post _).trans (actual.trans (scalars.owners c hc))

end FiniteEvaluator.SparseTasks

end BorderVNP
end Computability
end OAI
