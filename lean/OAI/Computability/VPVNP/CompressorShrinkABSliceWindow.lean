import OAI.Computability.VPVNP.CompressorShrinkABSliceOperands
import OAI.Computability.VPVNP.CompressorBlockABSliceFootprint
import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorScriptWindow
import OAI.Computability.VPVNP.CompressorBlockHeaderPacket

/-!
# Native AB visits in the fixed shrinking script

The AB section starts after the thirty-six demand and selection visits and
the twelve resident-list visits. Its scalar expressions read the current
level header before the scratch region. Every source stage therefore uses
the operands evaluated from its own chronological input memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockSlices

open BurstRAM PhaseRecipe BlockPlanner Compression ShrinkBlockInputs DescriptorSpace SourceTransport
open ShrinkABSliceRecipe
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)

local notation "A" => BlockProgram.script B
local notation "F" => BlockProgram.geometry B
local notation "O" => BlockProgram.arena B i.val 0
local notation "AB" => BlockProgram.arena B i.val 1

/-- The shrinking visits preceding the AB intersection window, including term selection and
construction of the resident lists. -/
def preceding :=
  let chosen := selectedInputs B F i O
  beforeSlices B F i O ++ ShrinkResidentsPlan.visits chosen (BlockProgram.arena B i.val 5)
    (LevelFields.atLevel i.val) (ShrinkBundlePlan.absoluteCD i.val (a i) O) (a i)

/-- The contiguous window of AB intersection visits in the fixed script for this shrinking
substep. -/
abbrev abWindow : Window A (intersections i O AB) := BlockGroups.shrink B i 6

theorem preceding_length : (preceding B i).length = 48 := by
  rw [preceding,List.length_append,beforeSlices_length,ShrinkResidentsPlan.visits_length]

theorem abWindow_offset : (abWindow B i).before.length = (BlockIndex.earlier B i).length+48 := by
  rw [abWindow,BlockGroups.shrink_offset,← preceding_length B i]
  congr 2

variable {w : ℕ} {pub : Fin 5 → Word w} {state : Word w} {ref : Memory w}

private theorem expr_agree (e : Expr) (D : ℕ → Prop) (start : ℕ) (mem : Memory w)
    (ok : e.ReadsFrom (fun x => D x ∧ x < start) pub state ref) (same : Agree (· < start) ref mem) :
    e.eval pub state ref = e.eval pub state mem ∧ e.ReadsFrom D pub state mem := by
  induction e with
  | lit | publicWord | state => exact ⟨rfl,trivial⟩
  | binary op x y ix iy =>
    obtain ⟨hx,rx⟩ := ix ok.1
    obtain ⟨hy,ry⟩ := iy ok.2
    exact ⟨congrArg₂ op.eval hx hy,rx,ry⟩
  | load x ih =>
    obtain ⟨hx,rx⟩ := ih ok.1
    exact ⟨(same _ ok.2.2).trans (congrArg (fun j : Word w => mem j.val) hx),rx,hx ▸ ok.2.1⟩

/-- A guarded whole-level run produces the precise operand and execution
contract of every member of the script window. -/
theorem ab_header_walk {m n rows first : ℕ} (I : Inputs) (L : DescriptorSpace.Layout)
    (D : ℕ → Prop) (start high : ℕ) (t p : Fin 5 → Word w)
    (heads : Describes I pub state ref t p rows first) (low : levelStart L 0 ≤ start)
    (ok : Supported (fun x => D x ∧ x<start) pub state ref I)
    (js : List (Stage m n)) (mem : Memory w) (rs : List (Report w))
    (walk : SourceWalk (Guarded I pub state ref rows 95 (fun x => start≤x ∧ x<high)) js mem rs)
    (same : Agree (· < start) ref mem) :
    SourceWalk (fun v cur logs => HeaderPacket.Run L pub state v cur logs 95 (List.replicate rows []) ∧
      HeaderOperands.Supported D pub state cur v) (js.map (stage I)) mem rs := by
  induction walk with
  | done => exact .done _
  | @next j js cur xs ys head tail ih =>
    obtain ⟨run,progress,rd,wr⟩ := head
    let v := stage I j
    have ops := stage_supported (fun x => D x ∧ x < start) pub state ref ok j
    have first := expr_agree v.initial D start cur ops.initial same
    have last := expr_agree v.stop D start cur ops.stop same
    have args (k) := expr_agree (v.params k) D start cur (ops.params k) same
    have init : v.initial.eval pub state cur = 0 := by cases j <;> rfl
    have stop : v.stop.eval pub state cur = (rows : Word w) := last.1.symm.trans (by cases j <;> exact heads.rowsAt)
    have he : (fun k => (v.params k).eval pub state ref) = (fun k => (v.params k).eval pub state cur) :=
      funext fun k => (args k).1
    have next : Agree (· < start) ref (after cur (eventLog xs)) :=
      fun x hx => (same x hx).trans (after_outside cur wr (fun h => (Nat.not_le_of_lt hx) h.1)).symm
    refine .next ⟨⟨by decide,?_,?_,fun x a h => low.trans (rd x a h).1,fun x a h => low.trans (wr x a h).1⟩,
      ⟨first.2,last.2,fun k => (args k).2⟩⟩ (ih next)
    · change runSegment (v.worker.table.instantiate w (fun k => (v.params k).eval pub state cur)).program
        95 (some (v.initial.eval pub state cur)) cur (List.replicate rows []) = some xs
      rw [init,← he]; exact run
    · change SourceOnline.Progress (v.stop.eval pub state cur) (v.initial.eval pub state cur) xs
      rw [init,stop]; exact progress

end CompressorRecords.BlockSlices

end

end VPVNP
end Computability
end OAI
