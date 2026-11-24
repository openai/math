import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.StructuredStackLoop

/-!
# Emitting the bits of a record word without consuming its register

The buffer for the pre-sort probe records is accumulated in reverse bit
order. A fixed pop/push control copies each word's bits onto this buffer and
restores the source using one scratch stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.WordCopy

variable {K : Type} (tmpPort outPort : K)
open Routine

/-- Copy a single popped bit to the accumulating record buffer and save it
temporarily for restoration. -/
private def saveBit (f : Bool → Bool) (b : Bool) :=
  (Routine.push outPort (f b)).followedBy (Routine.push tmpPort b)

private def save (f : Bool → Bool) (src : K) :=
  Routine.popLoop src (fun _ => true) (saveBit tmpPort outPort f false) (saveBit tmpPort outPort f true)

private def restore (src : K) :=
  Routine.popLoop tmpPort (fun _ => true) (Routine.push src false) (Routine.push src true)

/-- Copy the source word to the reverse buffer bit by bit through the given Boolean map, then
restore the source from scratch. -/
def mapWord (f : Bool → Bool) (src : K) : FiniteRoutine K :=
  .ofRoutine ((save tmpPort outPort f src).followedBy (restore tmpPort src))

variable [DecidableEq K] {src : K}

private def frame (src : K) (s : Stacks K) (x tmp buf : List Bool) : Stacks K :=
  fun j => if j = src then x else if j = tmpPort then tmp else if j = outPort then buf else s j

private theorem frame_eq (src : K) (s : Stacks K) :
    frame tmpPort outPort src s (s src) (s tmpPort) (s outPort) = s := by
  funext j
  simp only [frame]
  split_ifs <;> subst_vars <;> rfl

private theorem set_src (s : Stacks K) (x tmp buf x' : List Bool) :
    Function.update (frame tmpPort outPort src s x tmp buf) src x' = frame tmpPort outPort src s x' tmp buf := by
  funext j
  by_cases h : j=src <;> simp [frame, h]

private theorem set_tmp (h : src ≠ tmpPort) (s : Stacks K) (x tmp buf tmp' : List Bool) :
    Function.update (frame tmpPort outPort src s x tmp buf) tmpPort tmp' = frame tmpPort outPort src s x tmp' buf := by
  funext j
  by_cases h₁ : j=tmpPort <;> simp [frame, h₁, Ne.symm h]

private theorem set_buf (h : src ≠ outPort) (hd : tmpPort ≠ outPort) (s : Stacks K) (x tmp buf buf' : List Bool) :
    Function.update (frame tmpPort outPort src s x tmp buf) outPort buf' = frame tmpPort outPort src s x tmp buf' := by
  funext j
  by_cases h₁ : j=outPort <;> simp [frame, h₁, Ne.symm h, Ne.symm hd]

private theorem saveBit_runs (f : Bool → Bool) (h₁ : src ≠ tmpPort) (h₂ : src ≠ outPort) (h₃ : tmpPort ≠ outPort)
    (s : Stacks K) (x tmp buf : List Bool) (b : Bool) :
    (saveBit tmpPort outPort f b).Runs 2 (frame tmpPort outPort src s x tmp buf) (frame tmpPort outPort src s x (b::tmp) (f b::buf)) := by
  have hb := runs_push outPort (f b) (frame tmpPort outPort src s x tmp buf)
  have ht := runs_push tmpPort b (frame tmpPort outPort src s x tmp (f b::buf))
  simp only [set_buf _ _ h₂ h₃, set_tmp _ _ h₁, frame, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃,
    ↓reduceIte] at hb ht
  exact hb.followedBy ht

private theorem save_runs (f : Bool → Bool) (h₁ : src ≠ tmpPort) (h₂ : src ≠ outPort) (h₃ : tmpPort ≠ outPort)
    (s : Stacks K) (x tmp buf : List Bool) :
    (save tmpPort outPort f src).Runs (3*x.length+1) (frame tmpPort outPort src s x tmp buf)
      (frame tmpPort outPort src s [] (x.reverse++tmp) ((x.map f).reverse++buf)) := by
  induction x generalizing tmp buf with
  | nil =>
    apply Runs.popLoop_empty
    simp [frame]
  | cons b xs ih =>
    have head : frame tmpPort outPort src s (b::xs) tmp buf src = b::xs := by simp [frame]
    have hbody := saveBit_runs tmpPort outPort f h₁ h₂ h₃ s xs tmp buf b
    have tail := ih (b::tmp) (f b::buf)
    have H := Runs.popLoop_continue src (fun _ => true) (saveBit tmpPort outPort f false) (saveBit tmpPort outPort f true) head rfl
      (by rw [set_src]; cases b <;> exact hbody) tail
    simpa [save, List.reverse_cons, List.append_assoc, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm] using H

private theorem restore_runs (h₁ : src ≠ tmpPort) (s : Stacks K) (x tmp buf : List Bool) :
    (restore tmpPort src).Runs (2*tmp.length+1) (frame tmpPort outPort src s x tmp buf)
      (frame tmpPort outPort src s (tmp.reverse++x) [] buf) := by
  induction tmp generalizing x with
  | nil =>
    apply Runs.popLoop_empty
    simp [frame, Ne.symm h₁]
  | cons b tmp ih =>
    have head : frame tmpPort outPort src s x (b::tmp) buf tmpPort = b::tmp := by simp [frame, Ne.symm h₁]
    have hbody := runs_push src b (frame tmpPort outPort src s x tmp buf)
    rw [set_src] at hbody
    have H := Runs.popLoop_continue tmpPort (fun _ => true) (Routine.push src false)
      (Routine.push src true) head rfl (by
        rw [set_tmp _ _ h₁]
        cases b <;> simpa [frame] using hbody) (ih (b::x))
    simpa [restore, List.reverse_cons, List.append_assoc, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm] using H

/-- Five primitive instructions per source bit and the two empty-stack tests. -/
theorem mapWord_run (f : Bool → Bool) (h₁ : src ≠ tmpPort) (h₂ : src ≠ outPort) (h₃ : tmpPort ≠ outPort) (s : Stacks K)
    (ht : s tmpPort = []) :
    (mapWord tmpPort outPort f src).Runs (5*(s src).length+2) s
      (Function.update s outPort (((s src).map f).reverse ++ s outPort)) := by
  let x := s src
  let b := s outPort
  have ha := save_runs tmpPort outPort f h₁ h₂ h₃ s x [] b
  have hr := restore_runs tmpPort outPort h₁ s [] x.reverse ((x.map f).reverse ++ b)
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at ha hr
  have H := ha.followedBy hr
  have hi := frame_eq tmpPort outPort src s
  rw [ht] at hi
  have ho := set_buf tmpPort outPort (src := src) h₂ h₃ s x [] b ((x.map f).reverse ++ b)
  rw [hi] at ho
  rw [hi, ← ho] at H
  rw [show 3*x.length+1+(2*x.length+1) = 5*x.length+2 by omega] at H
  exact H

/-- Prepare a zero word from the preserved width template, using one empty
scratch stack. Every input bit contributes one output zero. -/
theorem zero_template (h₁ : src ≠ tmpPort) (h₂ : src ≠ outPort) (h₃ : tmpPort ≠ outPort)
    (s : Stacks K) (hs : s tmpPort = []) (ho : s outPort = []) :
    (mapWord tmpPort outPort (fun _ => false) src).Runs (5*(s src).length+2) s
      (Function.update s outPort (List.replicate (s src).length false)) := by
  simpa [ho, List.map_const'] using mapWord_run tmpPort outPort (fun _ => false) h₁ h₂ h₃ s hs

end RAMTape.WordCopy

end VPVNP
end Computability
end OAI
