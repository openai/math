import OAI.Computability.VPVNP.RAMTapeSortOneStageModel
import OAI.Computability.VPVNP.RAMTapeSortLayerRows

/-! # Executing one sorting stage of the transcript validator

The finite routine splits the incident field when the stride crosses sites,
visits every row, then reverses the accumulated output into the current block.
The entire operation uses the live unary phase and stride of the schedule.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortOneStage

open BurstRAM RAMSort RAMBoundary Boundary

/-- Prepare the stage's incident streams, visit every row under its phase and stride, then
expose the selected next block in forward order. -/
def program : FiniteRoutine Port :=
  (prepare.followedBy (SortLayerRows.program.onPorts Sum.inl)).followedBy advance

/-- A single callback for the schedule's nested phase and stride loops. -/
def layer : FiniteRoutine (SortSchedule.Port Port) := program.onPorts schedulePorts

variable {h d w : ℕ}

/-- The validator returns the selected local block, the unconsumed tail of
the incident stream, and the comparator flags in reverse row order. -/
theorem runs (hw : 2 ≤ w) (s : Stage (h+d)) (v : Word d) (left : ℕ)
    (current send recv : Wires h (RawSlot w)) (tail flags : List Bool) :
    ∃ t ≤ budget h d w, layer.Runs t
      (SortSchedule.bank (data v w h current (stream s send recv tail) flags) left s.phase s.stride)
      (SortSchedule.bank (data v w h (SortLayerRows.selected s v current recv) tail
        ((List.ofFn (SortLayerRows.checks s current send recv)).reverse.flatten ++ flags)) left s.phase s.stride) := by
  obtain ⟨t, ht, first⟩ := prepare_runs s v current send recv tail flags
  obtain ⟨u, hu, scan⟩ := SortLayerRows.runs hw s v current send recv [] [] tail flags
  simp only [List.append_nil] at scan
  have rows := rows_runs v s.phase s.stride w h scan
  let out := SortLayerRows.selected s v current recv
  let checks := (List.ofFn (SortLayerRows.checks s current send recv)).reverse.flatten ++ flags
  have move := advance_runs v s.phase s.stride w h (blockBytes (List.ofFn current))
    (blockBytes (List.ofFn out)) tail checks
  have native := (first.followedBy rows).followedBy move
  simp only [length_blockBytes, List.length_ofFn] at native
  refine ⟨_, ?_, schedule_run v s.phase s.stride w h left current out _ flags tail checks
    (native := program) native⟩
  have hu' := hu.trans (SortLayerRows.budget_le s)
  unfold budget
  omega

theorem runs_local (hw : 2 ≤ w) (s : Stage (h+d)) (hl : s.stride < h) (v : Word d) (left : ℕ)
    (current send recv : Wires h (RawSlot w)) (tail flags : List Bool) :
    ∃ t ≤ budget h d w, layer.Runs t (SortSchedule.bank (data v w h current tail flags) left s.phase s.stride)
      (SortSchedule.bank (data v w h (SortLayerRows.selected s v current recv) tail
        ((List.ofFn (SortLayerRows.checks s current send recv)).reverse.flatten ++ flags)) left s.phase s.stride) := by
  simpa only [stream, hl, ↓reduceIte] using runs hw s v left current send recv tail flags

theorem runs_cross (hw : 2 ≤ w) (s : Stage (h+d)) (hc : h ≤ s.stride) (v : Word d) (left : ℕ)
    (current send recv : Wires h (RawSlot w)) (tail flags : List Bool) :
    ∃ t ≤ budget h d w, layer.Runs t
      (SortSchedule.bank (data v w h current (blockBytes (List.ofFn send) ++ (blockBytes (List.ofFn recv) ++ tail))
        flags) left s.phase s.stride)
      (SortSchedule.bank (data v w h (SortLayerRows.selected s v current recv) tail
        ((List.ofFn (SortLayerRows.checks s current send recv)).reverse.flatten ++ flags)) left s.phase s.stride) := by
  simpa only [stream, Nat.not_lt.mpr hc, ↓reduceIte] using runs hw s v left current send recv tail flags

end RAMTape.SortOneStage

end VPVNP
end Computability
end OAI
