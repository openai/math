import OAI.Computability.VPVNP.RAMTapeSortGatherPreserve
import OAI.Computability.VPVNP.RAMTapeBoundaryDecision
import OAI.Computability.VPVNP.StructuredStackLoop

/-!
# Fetching comparison operands at one physical sorting row

The row traversal retains its unary row offset. A local stride additionally
fetches its XOR partner from the same materialized block. At a cross-site
stride the two remote fields are instead consumed as record streams.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortRow

open Boundary RAMSort RAMBoundary

/-- Stacks for a sorting row, including the current and next blocks, remote streams, row
offsets, comparator orientation, and validity flags. -/
inductive Port
  | current | next | crossSend | crossReceive | width | row | partner | orientation | localFlag
  | lookup | saved | widthBack | recordBack | left | right | savedLeft | savedRight | selectTmp | flags
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Which locally fetched record to stage, the current row's record or its partner's. -/
inductive Operand | first | other
  deriving DecidableEq

/-- Select the unary row offset or partner offset used to fetch this operand. -/
def Operand.index : Operand → Port | .first => .row | .other => .partner
/-- Select the left or right staging stack for the fetched operand. -/
def Operand.destination : Operand → Port | .first => .left | .other => .right

/-- Connect the block reader to the current block, scratch stacks, and this operand's
destination. -/
def fetchPorts (operand : Operand) : SortGather.Port → Port
  | .block => .current
  | .offset => .lookup
  | .width => .width
  | .widthBack => .widthBack
  | .saved => .saved
  | .recordBack => .recordBack
  | .output => operand.destination

/-- Fetch the indexed record from the current block while preserving the operand's offset. -/
def fetch (operand : Operand) : FiniteRoutine Port :=
  SortGather.fetchPreserving (fetchPorts operand) operand.index

/-- Scratch and the word-width register required by a materialized array lookup. -/
structure FetchReady (w : ℕ) (s : Stacks Port) : Prop where
  width : s .width = List.replicate w true
  lookup : s .lookup = []
  widthBack : s .widthBack = []
  saved : s .saved = []
  recordBack : s .recordBack = []

theorem fetch_runs {w B : ℕ} (o : Operand) (s : Stacks Port) (block : Fin B → RawSlot w)
    (i : Fin B) (hready : FetchReady w s) (hblock : s .current = blockBytes (List.ofFn block))
    (hidx : s o.index = List.replicate i.val true) :
    (fetch o).Runs (5*i.val+2+SortGather.cost i.val w) s
      (Function.update s o.destination (recordBytes (block i) ++ s o.destination)) := by
  let rows := List.ofFn block
  have hi : i.val < rows.length := by simp [rows]
  have hs := List.take_append_drop i.val rows
  rw [List.drop_eq_getElem_cons hi] at hs
  have he : s .current = blockBytes (rows.take i.val) ++ recordBytes (block i) ++
      blockBytes (rows.drop (i.val+1)) := by
    rw [hblock]
    have h := congrArg blockBytes hs
    simpa only [blockBytes, List.flatMap_append, List.flatMap_cons, rows, List.getElem_ofFn,
      List.append_assoc] using h.symm
  have hinj : Function.Injective (fetchPorts o) := by cases o <;> decide
  have hdis : ∀ j, o.index ≠ fetchPorts o j := by cases o <;> decide
  apply SortGather.fetchPreserving_runs _ hinj _ hdis w i.val s
    (blockBytes (rows.take i.val)) (recordBytes (block i)) (blockBytes (rows.drop (i.val+1)))
  · simp [rows]
  · exact length_recordBytes _
  · exact he
  · exact hidx
  · exact hready.lookup
  · exact hready.width
  · exact hready.widthBack
  · exact hready.saved
  · exact hready.recordBack

/-- The computed partner offset is private to one row. Discard it when
returning control to the outer traversal. -/
def clearPartner : FiniteRoutine Port :=
  .ofRoutine (Routine.popLoop Port.partner (fun _ => true) Routine.ret Routine.ret)

theorem clearPartner_runs (s : Stacks Port) :
    clearPartner.Runs (2*(s .partner).length+1) s (Function.update s .partner []) := by
  generalize hx : s .partner = xs
  induction xs generalizing s with
  | nil =>
    have he : Function.update s .partner [] = s := by rw [← hx, Function.update_eq_self]
    rw [he]
    simpa [clearPartner, FiniteRoutine.ofRoutine, FiniteRoutine.Runs] using Routine.Runs.popLoop_empty Port.partner (fun _ => true) Routine.ret Routine.ret hx
  | cons b xs ih =>
    let mid := Function.update s Port.partner xs
    have h := Routine.Runs.popLoop_continue Port.partner (fun _ => true) Routine.ret Routine.ret hx rfl
      (mid := mid) (n := 1) (by cases b <;> exact Routine.runs_ret mid)
      (ih mid (Function.update_self ..))
    rw [show 1+1+(2*xs.length+1) = 2*(xs.length+1)+1 by omega] at h
    simpa only [clearPartner, FiniteRoutine.ofRoutine, FiniteRoutine.Runs, List.length_cons,
      mid, Function.update_idem] using h

end RAMTape.SortRow

end VPVNP
end Computability
end OAI
