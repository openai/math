import OAI.Computability.VPVNP.CompressorSourceOnline

/-!
# Embedding a contiguous native substep in the fixed block program

A window identifies each occurrence by its ordinal inside the complete
static block. Equal worker tables can occur many times. An indexed map
of a chronological source walk retains this distinction while keeping
the original input memories, tapes and reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM Schedule

namespace BlockPlanner

/-- A decomposition of the script block around a specified contiguous list of visits. -/
structure Window (A : Script) (visits : List Visit) where
  /-- Visits in the block preceding the first occurrence in the window. -/
  before : List Visit
  /-- Visits in the block following the window. -/
  after : List Visit
  block : A.block = before ++ visits ++ after

namespace Window

variable {A : Script} {visits : List Visit} (W : Window A visits)

/-- Index of a window occurrence in the block, obtained by skipping its preceding visits. -/
def position (i : Fin visits.length) : Fin A.block.length :=
  ⟨W.before.length+i.val,by rw [W.block]; simp only [List.length_append]; have := i.isLt; omega⟩

/-- Index of a window occurrence in the whole script, including the initialization prefix. -/
def index (i : Fin visits.length) : Fin A.size := (W.position i).natAdd A.initial.length

theorem index_val (i : Fin visits.length) : (W.index i).val = A.initial.length + W.before.length + i.val := by
  change A.initial.length+(W.before.length+i.val) = _; omega

theorem visit (i : Fin visits.length) : A.visit (W.index i) = visits[i.val] := by
  rw [index,A.block_visit]
  change A.block[W.before.length+i.val]'_ = _
  erw [List.getElem_of_eq W.block]
  rw [List.getElem_append_left (by simp only [List.length_append]; have := i.isLt; omega)]
  rw [List.getElem_append_right (by omega)]
  simp

end Window
end BlockPlanner

theorem SourceWalk.mapAt {J K : Type*} {w : ℕ} {source : J → Memory w → List (Report w) → Prop}
    {dest : K → Memory w → List (Report w) → Prop} {js : List J} {m : Memory w} {rs : List (Report w)}
    (h : SourceWalk source js m rs) (labels : Fin js.length → K)
    (convert : ∀ i mem log, source js[i.val] mem log → dest (labels i) mem log) :
    SourceWalk dest (List.ofFn labels) m rs := by
  induction h with
  | done => simp only [List.length_nil,List.ofFn_zero]; exact .done _
  | @next j js m rs ts hhead _ ih =>
    rw [@List.ofFn_succ K js.length labels]
    exact .next (convert 0 m rs hhead) (ih _ (fun i mem log hs ↦ convert i.succ mem log hs))

namespace SourceOnline.Visit

variable {A : BlockPlanner.Script} {w : ℕ}

/-- Form a script visit from a native worker, transporting its operands to the matching catalog
entry. -/
def ofWorker (j : Fin A.size) (W : Pass) (hw : A.catalog j = W) (fuel : ℕ) (start stop : Word w)
    (params : Fin W.params → Word w) (choices : List (List Bool)) : SourceOnline.Visit A w :=
  ⟨j,fuel,start,stop,fun i ↦ params (Fin.cast (congrArg Pass.params hw) i),choices⟩

theorem ofWorker_runs (j : Fin A.size) (W : Pass) (hw : A.catalog j = W) (fuel : ℕ) (start stop : Word w)
    (params : Fin W.params → Word w) (choices : List (List Bool)) (m : Memory w) (rs : List (Report w)) :
    (ofWorker j W hw fuel start stop params choices).Runs m rs ↔
      runSegment (W.table.instantiate w params).program fuel (some start) m choices = some rs := by
  subst W; rfl

end SourceOnline.Visit
end CompressorRecords

end VPVNP
end Computability
end OAI
