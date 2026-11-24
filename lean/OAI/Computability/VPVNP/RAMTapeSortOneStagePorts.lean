import OAI.Computability.VPVNP.RAMTapeSortBoundary
import OAI.Computability.VPVNP.RAMTapeSortLayerDispatch
import OAI.Computability.VPVNP.RAMTapeSortLayerRowsPorts
import OAI.Computability.VPVNP.RAMTapeSortSchedule

/-! # Registers shared by the boundary moves and row traversal of a sorting stage

The row traversal and the exchange-stream split share their temporary ports.
The stage also has a preserved unary record count for splitting a whole block.
When installed in the schedule, its phase and stride refer directly to the
schedule's counters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortOneStage

open BurstRAM RAMBoundary Boundary

/-- The extra port holds the unary number of records in a site block. -/
abbrev Port := SortLayerRows.Port ⊕ Unit

private def row (p : SortRow.Port) : Port := .inl (.inl (.inl p))

/-- Initialize one stage's row and boundary stacks, including the site identifier, stage
exponents, live record streams, flags and unary block size. -/
def bank {d : ℕ} (v : Word d) (a j w h : ℕ) (current next send recv flags : List Bool) :
    Stacks Port :=
  Sum.elim (SortOffsets.idle (SortLayerRows.bank v a j w current next send recv flags) h)
    (fun _ => List.replicate (2^h) true)

/-- Connect the local-versus-cross-site stride test to the row-width and stride counters and
temporary storage. -/
def dispatchPorts : SortLayerDispatch.Port → Port
  | .width => .inl (.inr .width)
  | .stride => .inl (.inl (.inr .stride))
  | .tmp => .inl (.inl (.inr .tmp))

/-- Route block splitting and advancement to the same current, next, incident and scratch
stacks used by the row traversal. -/
def boundaryPorts : SortBoundary.Port → Port
  | .current => row .current
  | .next => row .next
  | .crossSend => row .crossSend
  | .crossReceive => row .crossReceive
  | .width => row .width
  | .slots => .inr ()
  | .scratch1 => row .lookup
  | .scratch2 => row .saved

theorem dispatchPorts_injective : Function.Injective dispatchPorts := by decide
theorem boundaryPorts_injective : Function.Injective boundaryPorts := by decide

/-- The local branch leaves the incident stream in place. The cross-site
branch separates its first block onto the send stack. -/
def prepare : FiniteRoutine Port :=
  SortLayerDispatch.routine dispatchPorts (SortBoundary.splitCross.onPorts boundaryPorts) .ret

private theorem split_run {d : ℕ} (v : Word d) (a j w h : ℕ)
    (cur send recv flags : List Bool) (hlen : send.length = 2^h*(5*w)) :
    (SortBoundary.splitCross.onPorts boundaryPorts).Runs (SortBoundary.splitCost (2^h) w)
      (bank v a j w h cur [] [] (send++recv) flags)
      (bank v a j w h cur [] send recv flags) := by
  let initial := bank v a j w h cur [] [] (send++recv) flags
  let small := initial ∘ boundaryPorts
  have hr := SortBoundary.splitCross_runs (2^h) w small send recv hlen rfl rfl rfl rfl rfl rfl
  apply FiniteRoutine.runs_onPorts_framed _ boundaryPorts_injective hr
  · intro p; rfl
  · intro p; cases p <;> rfl
  · intro p hp
    rcases p with ((r|e)|o)|u
    · cases r <;> first | rfl | exact (hp .crossSend rfl).elim | exact (hp .crossReceive rfl).elim
    · cases e <;> rfl
    · rfl
    · rfl

theorem prepare_cross {d : ℕ} (v : Word d) (a j w h : ℕ)
    (cur send recv flags : List Bool) (hc : h ≤ j) (hlen : send.length = 2^h*(5*w)) :
    prepare.Runs (6*h+5+SortBoundary.splitCost (2^h) w)
      (bank v a j w h cur [] [] (send++recv) flags)
      (bank v a j w h cur [] send recv flags) :=
  SortLayerDispatch.cross_runs _ dispatchPorts_injective _ .ret rfl rfl hc (split_run v a j w h cur send recv flags hlen)

theorem prepare_local {d : ℕ} (v : Word d) (a j w h : ℕ)
    (cur recv flags : List Bool) (hl : j < h) :
    prepare.Runs (6*j+8) (bank v a j w h cur [] [] recv flags) (bank v a j w h cur [] [] recv flags) :=
  SortLayerDispatch.local_runs _ dispatchPorts_injective (SortBoundary.splitCross.onPorts boundaryPorts)
    .ret (s := bank v a j w h cur [] [] recv flags) rfl rfl hl (Routine.runs_ret _)

/-- Discard the old current block and reverse the completed next block into its place on the
stage's physical ports. -/
def advance : FiniteRoutine Port := SortBoundary.advance.onPorts boundaryPorts

theorem advance_runs {d : ℕ} (v : Word d) (a j w h : ℕ)
    (cur next recv flags : List Bool) :
    advance.Runs (cur.length + 2*next.length + 2)
      (bank v a j w h cur next.reverse [] recv flags)
      (bank v a j w h next [] [] recv flags) := by
  let initial := bank v a j w h cur next.reverse [] recv flags
  let small := initial ∘ boundaryPorts
  have hr := SortBoundary.advance_runs small
  change SortBoundary.advance.Runs (cur.length + 2*next.reverse.length + 2) small
    (Function.update (Function.update small .next []) .current next.reverse.reverse) at hr
  rw [List.reverse_reverse, List.length_reverse] at hr
  apply FiniteRoutine.runs_onPorts_framed _ boundaryPorts_injective hr
  · intro p; rfl
  · intro p; cases p <;> rfl
  · intro p hp
    rcases p with ((r|e)|o)|u
    · cases r <;> first | rfl | exact (hp .current rfl).elim | exact (hp .next rfl).elim
    · cases e <;> rfl
    · rfl
    · rfl

theorem rows_runs {d : ℕ} (v : Word d) (a j w h : ℕ)
    {cur next send recv flags cur' next' send' recv' flags' : List Bool}
    {rows : FiniteRoutine SortLayerRows.Port} {t : ℕ}
    (hr : rows.Runs t (SortOffsets.idle (SortLayerRows.bank v a j w cur next send recv flags) h)
      (SortOffsets.idle (SortLayerRows.bank v a j w cur' next' send' recv' flags') h)) :
    (rows.onPorts (Sum.inl : SortLayerRows.Port → Port)).Runs t
      (bank v a j w h cur next send recv flags) (bank v a j w h cur' next' send' recv' flags') := by
  apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective hr
  · intro p; rfl
  · intro p; rfl
  · rintro (p|u) hp
    · exact (hp p rfl).elim
    · rfl

/-- Share the stage's phase and stride directly with the schedule counters and route its
remaining stacks to the schedule's data bank. -/
def schedulePorts : Port → SortSchedule.Port Port
  | .inl (.inl (.inr .phase)) => .inl .phase
  | .inl (.inl (.inr .stride)) => .inl .stride
  | p => .inr p

theorem schedulePorts_injective : Function.Injective schedulePorts := by decide

/-- Between layers, the schedule itself supplies phase and stride. -/
def data {d : ℕ} (v : Word d) (w h : ℕ) (cur : Word h → RawSlot w)
    (recv flags : List Bool) : Stacks Port :=
  bank v 0 0 w h (blockBytes (List.ofFn cur)) [] [] recv flags

private theorem schedule_bank {d : ℕ} (v : Word d) (a j w h left : ℕ) (cur : Word h → RawSlot w)
    (recv flags : List Bool) (p : Port) :
    SortSchedule.bank (data v w h cur recv flags) left a j (schedulePorts p) =
      bank v a j w h (blockBytes (List.ofFn cur)) [] [] recv flags p := by
  rcases p with ((r|e)|o)|u
  · cases r <;> rfl
  · cases e <;> rfl
  · rfl
  · rfl

theorem schedule_run {d : ℕ} (v : Word d) (a j w h left : ℕ) (cur cur' : Word h → RawSlot w)
    (recv flags recv' flags' : List Bool) {native : FiniteRoutine Port} {t : ℕ}
    (hr : native.Runs t (bank v a j w h (blockBytes (List.ofFn cur)) [] [] recv flags)
      (bank v a j w h (blockBytes (List.ofFn cur')) [] [] recv' flags')) :
    (native.onPorts schedulePorts).Runs t
      (SortSchedule.bank (data v w h cur recv flags) left a j)
      (SortSchedule.bank (data v w h cur' recv' flags') left a j) := by
  apply FiniteRoutine.runs_onPorts_framed _ schedulePorts_injective hr
    (schedule_bank v a j w h left cur recv flags) (schedule_bank v a j w h left cur' recv' flags')
  intro p hp
  rcases p with c | (((r|e)|o)|u)
  · cases c <;> rfl
  · exact (hp (.inl (.inl (.inl r))) rfl).elim
  · cases e <;> rfl
  · exact (hp (.inl (.inr o)) rfl).elim
  · exact (hp (.inr u) rfl).elim

end RAMTape.SortOneStage

end VPVNP
end Computability
end OAI
