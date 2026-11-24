import OAI.Computability.VPVNP.RankQueryStackFrameField
import OAI.Computability.VPVNP.RankQueryStackCodec

/-!
# Fixed bit-stack controls for Schur continuations

Ten independently tagged histories form one synchronized continuation stack.
The histories keep earlier frames intact through calls and returns. The routines
below require only the current ten live registers, and execute the same control
for every stack depth and register width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.FrameStore

open RAMTape Evaluator.InputBank

private def batch (op : Fin 10 → FiniteRoutine Port) : List (Fin 10) → FiniteRoutine Port
  | [] => .ret
  | i :: is => (batch op is).followedBy (op i)

/-- Save all ten live fields into their respective history stacks. -/
def push : FiniteRoutine Port := batch pushField (List.finRange 10)
/-- Restore all ten fields of the most recently saved frame. -/
def pop : FiniteRoutine Port := batch popField (List.finRange 10)

variable {n U Z p e : ℕ} {c : SliceArithmetic.Vector p e}

private abbrev Data := Fin 10 → List Bool

/-- The newest saved field is first at every history port. -/
def histories (width : ℕ) (fs : List (Frame.SchurFrame n U Z c)) : Data :=
  fun i => fs.flatMap (fun f => fieldBits (f.bits width i))

private theorem histories_cons (width : ℕ) (f : Frame.SchurFrame n U Z c) (fs : List (Frame.SchurFrame n U Z c)) :
    histories width (f :: fs) = fun i => fieldBits (f.bits width i) ++ histories width fs i := by
  funext i; simp [histories]

private def selected (ks : List (Fin 10)) (yes no : Data) : Data := fun i =>
  if i ∈ ks then yes i else no i

private theorem update_selected (ks : List (Fin 10)) (yes no : Data) (j : Fin 10) :
    Function.update (selected ks yes no) j (yes j) = selected (j :: ks) yes no := by
  funext i
  by_cases h : i = j <;> simp [selected, h]

private theorem selected_nil (yes no : Data) : selected [] yes no = no := by funext i; simp [selected]

private theorem selected_all (yes no : Data) : selected (List.finRange 10) yes no = yes := by
  funext i; simp [selected]

private theorem push_partial (ks : List (Fin 10)) (live hist : Data) (hks : ks.Nodup) :
    (batch pushField ks).Runs ((ks.map (fun i => 3*(live i).length+2)).sum+1) (registers live hist)
      (registers (selected ks (fun _ => []) live)
        (selected ks (fun i => fieldBits (live i) ++ hist i) hist)) := by
  induction ks with
  | nil =>
    rw [selected_nil, selected_nil]
    simp only [List.map_nil, List.sum_nil, Nat.zero_add]
    exact StackRuns.cons (.goto rfl) (.nil ..)
  | cons i ks ih =>
    let l := selected ks (fun _ => []) live
    let h := selected ks (fun i => fieldBits (live i) ++ hist i) hist
    have hl : l i = live i := by simp [l, selected, hks.notMem]
    have hh : h i = hist i := by simp [h, selected, hks.notMem]
    have step := pushField_runs i l h
    rw [hl, hh] at step
    have sl : Function.update l i [] = selected (i :: ks) (fun _ => []) live := update_selected ..
    have sh : Function.update h i (fieldBits (live i) ++ hist i) =
        selected (i :: ks) (fun j => fieldBits (live j) ++ hist j) hist := update_selected ..
    rw [sl, sh] at step
    have both := FiniteRoutine.Runs.followedBy (ih hks.of_cons) step
    simp only [batch, List.map_cons, List.sum_cons]
    convert both using 1
    omega

private theorem pop_partial (ks : List (Fin 10)) (live hist : Data) (hks : ks.Nodup) :
    (batch popField ks).Runs ((ks.map (fun i => 3*(live i).length+1)).sum+1)
      (registers (fun _ => []) (fun i => fieldBits (live i) ++ hist i))
      (registers (selected ks live (fun _ => []))
        (selected ks hist (fun i => fieldBits (live i) ++ hist i))) := by
  induction ks with
  | nil =>
    rw [selected_nil, selected_nil]
    simp only [List.map_nil, List.sum_nil, Nat.zero_add]
    exact StackRuns.cons (.goto rfl) (.nil ..)
  | cons i ks ih =>
    let l := selected ks live (fun _ => [])
    let h := selected ks hist (fun j => fieldBits (live j) ++ hist j)
    have hl : l i = [] := by simp [l, selected, hks.notMem]
    have hh : h i = fieldBits (live i) ++ hist i := by simp [h, selected, hks.notMem]
    have step := popField_runs i l h _ _ hh
    rw [hl, List.append_nil] at step
    have sl : Function.update l i (live i) = selected (i :: ks) live (fun _ => []) := update_selected ..
    have sh : Function.update h i (hist i) =
        selected (i :: ks) hist (fun j => fieldBits (live j) ++ hist j) := update_selected ..
    rw [sl, sh] at step
    have both := FiniteRoutine.Runs.followedBy (ih hks.of_cons) step
    simp only [batch, List.map_cons, List.sum_cons]
    convert both using 1
    omega

/-- Save ten fields of arbitrary bit lengths; their lengths may differ by field. -/
theorem push_data_runs (live hist : Fin 10 → List Bool) :
    push.Runs (((List.finRange 10).map (fun i => 3*(live i).length+2)).sum+1) (registers live hist)
      (registers (fun _ => []) (fun i => fieldBits (live i) ++ hist i)) := by
  simpa only [push, selected_all] using push_partial (List.finRange 10) live hist (List.nodup_finRange 10)

/-- Restore ten fields of arbitrary bit lengths and leave their history tails intact. -/
theorem pop_data_runs (live hist : Fin 10 → List Bool) :
    pop.Runs (((List.finRange 10).map (fun i => 3*(live i).length+1)).sum+1)
      (registers (fun _ => []) (fun i => fieldBits (live i) ++ hist i)) (registers live hist) := by
  simpa only [pop, selected_all] using pop_partial (List.finRange 10) live hist (List.nodup_finRange 10)

/-- Move one entire live continuation into the histories. -/
theorem push_runs (width : ℕ) (f : Frame.SchurFrame n U Z c) (fs : List (Frame.SchurFrame n U Z c)) :
    push.Runs (10*(3*width+2)+1) (registers (f.bits width) (histories width fs))
      (registers (fun _ => []) (histories width (f :: fs))) := by
  rw [histories_cons]
  have hw (i : Fin 10) : (f.bits width i).length = width := UniversalCountStack.length_digits ..
  have ht : (((List.finRange 10).map (fun i => 3*(f.bits width i).length+2)).sum+1) = 10*(3*width+2)+1 := by
    simp [hw]; omega
  rw [← ht]
  exact push_data_runs ..

/-- Recover the saved direction, parent query, remaining summand and both scalars. -/
theorem pop_runs (width : ℕ) (f : Frame.SchurFrame n U Z c) (fs : List (Frame.SchurFrame n U Z c)) :
    pop.Runs (10*(3*width+1)+1) (registers (fun _ => []) (histories width (f :: fs)))
      (registers (f.bits width) (histories width fs)) := by
  rw [histories_cons]
  have hw (i : Fin 10) : (f.bits width i).length = width := UniversalCountStack.length_digits ..
  have ht : (((List.finRange 10).map (fun i => 3*(f.bits width i).length+1)).sum+1) = 10*(3*width+1)+1 := by
    simp [hw]; omega
  rw [← ht]
  exact pop_data_runs ..

/-- The abstract call-stack depth directly bounds the bit height of each history port. -/
theorem history_length (width : ℕ) (fs : List (Frame.SchurFrame n U Z c)) (i : Fin 10) :
    (histories width fs i).length = fs.length * (2*width+1) := by
  induction fs with
  | nil => simp [histories]
  | cons f fs ih =>
    change (fieldBits (f.bits width i) ++ histories width fs i).length = _
    rw [List.length_append, length_fieldBits, Frame.bits, UniversalCountStack.length_digits, ih,
      List.length_cons]
    ring

/-- Bit-space bound throughout a push, including instructions inside the field scans. -/
theorem push_space (width : ℕ) (f : Frame.SchurFrame n U Z c) (fs : List (Frame.SchurFrame n U Z c)) :
    UniversalCountStack.SpaceRun push.body.standalone (max width (fs.length*(2*width+1)) + (10*(3*width+2)+1))
      (10*(3*width+2)+1) (some push.body.entry) (registers (f.bits width) (histories width fs))
      none (registers (fun _ => []) (histories width (f :: fs))) := by
  apply UniversalCountStack.spaceRun_of_steps (push_runs width f fs)
  intro port
  apply Nat.add_le_add_right
  cases port with
  | inl i => change (UniversalCountStack.digits width (f.words i)).length ≤ _; simp
  | inr i => change (histories width fs i).length ≤ _; simp [history_length]

/-- Bit-space bound throughout a pop, independent of the number of earlier calls. -/
theorem pop_space (width : ℕ) (f : Frame.SchurFrame n U Z c) (fs : List (Frame.SchurFrame n U Z c)) :
    UniversalCountStack.SpaceRun pop.body.standalone ((fs.length+1)*(2*width+1) + (10*(3*width+1)+1))
      (10*(3*width+1)+1) (some pop.body.entry) (registers (fun _ => []) (histories width (f :: fs)))
      none (registers (f.bits width) (histories width fs)) := by
  apply UniversalCountStack.spaceRun_of_steps (pop_runs width f fs)
  intro port
  apply Nat.add_le_add_right
  cases port with
  | inl i => exact Nat.zero_le _
  | inr i => exact (history_length width (f :: fs) i).le

end RankQuery.Stack.FrameStore

end VPVNP
end Computability
end OAI
