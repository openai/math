import OAI.Computability.VPVNP.RAMTapeInputPorts
import OAI.Computability.VPVNP.StructuredStackLoop
import OAI.Computability.VPVNP.StructuredStackRuns

/-!
# Reading fixed-width fields with a finite stack control

The reader consumes one unary count mark and one input bit at a time. It
collects the bits in reverse order and restores them to their destination in
a second pass. Both passes use the same finite control at every input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputReader

open Routine

/-- Fixed-width fields following the prefix on a site tape, namely the address, four-bit
header, and incident vector. -/
inductive Field where
  | address | header | incident
  deriving DecidableEq

/-- Select the unary width counter for the address, header, or incident vector. -/
def Field.counter : Field → InputPort
  | .address => .addressCount
  | .header => .count
  | .incident => .incidentCount

/-- Select the stack on which the reader deposits the requested field. -/
def Field.output : Field → InputPort
  | .address => .address
  | .header => .header
  | .incident => .incident

private def copyBit :=
  popCase InputPort.input (Routine.halt false) (Routine.push .tmp false) (Routine.push .tmp true)

/-- Consume one input bit per true width mark, pushing the bits onto a temporary stack in
reverse order. -/
def collect (f : Field) :=
  popLoop f.counter (fun _ => true) (Routine.halt false) copyBit

/-- Move the collected field bits from the temporary stack to their output stack in original
order. -/
def restore (f : Field) :=
  popLoop .tmp (fun _ => true) (Routine.push f.output false) (Routine.push f.output true)

/-- Read one fixed-width field by collecting its bits and then restoring their order. -/
def readField (f : Field) := (collect f).followedBy (restore f)

/-- The unrelated registers are carried through all field instructions. -/
private def frame (s : Stacks InputPort) (f : Field) (input count tmp output : List Bool) :
    Stacks InputPort := fun j =>
  if j = .input then input else if j = f.counter then count else
    if j = .tmp then tmp else if j = f.output then output else s j

private theorem frame_eq (s : Stacks InputPort) (f : Field) :
    frame s f (s .input) (s f.counter) (s .tmp) (s f.output) = s := by
  funext j
  cases j <;> cases f <;> rfl

private theorem write_in (s : Stacks InputPort) (f : Field) (x c t o x' : List Bool) :
    Function.update (frame s f x c t o) .input x' = frame s f x' c t o := by
  funext j
  cases j <;> cases f <;> rfl

private theorem write_count (s : Stacks InputPort) (f : Field) (x c t o c' : List Bool) :
    Function.update (frame s f x c t o) f.counter c' = frame s f x c' t o := by
  funext j
  cases j <;> cases f <;> rfl

private theorem write_tmp (s : Stacks InputPort) (f : Field) (x c t o t' : List Bool) :
    Function.update (frame s f x c t o) .tmp t' = frame s f x c t' o := by
  funext j
  cases j <;> cases f <;> rfl

private theorem write_out (s : Stacks InputPort) (f : Field) (x c t o o' : List Bool) :
    Function.update (frame s f x c t o) f.output o' = frame s f x c t o' := by
  funext j
  cases j <;> cases f <;> rfl

private theorem at_count (s : Stacks InputPort) (f : Field) (x c t o : List Bool) :
    frame s f x c t o f.counter = c := by cases f <;> rfl

private theorem at_tmp (s : Stacks InputPort) (f : Field) (x c t o : List Bool) :
    frame s f x c t o .tmp = t := by cases f <;> rfl

private theorem at_out (s : Stacks InputPort) (f : Field) (x c t o : List Bool) :
    frame s f x c t o f.output = o := by cases f <;> rfl

private theorem copyBit_runs (s : Stacks InputPort) (f : Field) (b : Bool) (x c t o : List Bool) :
    copyBit.Runs 2 (frame s f (b::x) c t o) (frame s f x c (b::t) o) := by
  have put := runs_push InputPort.tmp b (frame s f x c t o)
  rw [at_tmp, write_tmp] at put
  have hi : frame s f (b::x) c t o .input = b :: x := rfl
  cases b with
  | false => exact runs_popCase_false InputPort.input _ _ _ hi (by rw [write_in]; exact put)
  | true => exact runs_popCase_true InputPort.input _ _ _ hi (by rw [write_in]; exact put)

private theorem collect_runs (s : Stacks InputPort) (f : Field) (xs suffix t o : List Bool) :
    (collect f).Runs (3*xs.length+1) (frame s f (xs++suffix) (List.replicate xs.length true) t o)
      (frame s f suffix [] (xs.reverse ++ t) o) := by
  induction xs generalizing t with
  | nil =>
    exact Runs.popLoop_empty f.counter (fun _ => true) (Routine.halt false) copyBit (at_count s f suffix [] t o)
  | cons b bs ih =>
    let c := List.replicate bs.length true
    let x := bs ++ suffix
    have h := Runs.popLoop_true_continue (mid := frame s f x c (b::t) o) (n := 2) f.counter (fun _ => true) (Routine.halt false) copyBit
      (at_count s f (b::x) (true::c) t o) rfl
      (by rw [write_count]; exact copyBit_runs s f b x c t o) (ih (b::t))
    simpa [collect, c, x, List.replicate_succ, List.reverse_cons, List.append_assoc,
      Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem restore_runs (s : Stacks InputPort) (f : Field) (x c t o : List Bool) :
    (restore f).Runs (2*t.length+1) (frame s f x c t o) (frame s f x c [] (t.reverse++o)) := by
  induction t generalizing o with
  | nil => exact Runs.popLoop_empty .tmp (fun _ => true) (Routine.push f.output false) (Routine.push f.output true) (at_tmp s f x c [] o)
  | cons b bs ih =>
    have put : (Routine.push f.output b).Runs 1 (frame s f x c bs o) (frame s f x c bs (b::o)) := by
      rw [← write_out s f x c bs o (b::o)]
      have hs : StackStep (Routine.push f.output b).standalone (some ()) (frame s f x c bs o)
          none (Function.update (frame s f x c bs o) f.output (b :: frame s f x c bs o f.output)) :=
        .push rfl
      rw [at_out] at hs
      exact .cons hs (.nil ..)
    have h := Runs.popLoop_continue (mid := frame s f x c bs (b::o)) (n := 1) InputPort.tmp (fun _ => true) (Routine.push f.output false) (Routine.push f.output true)
      (at_tmp s f x c (b::bs) o) rfl (by rw [write_tmp]; cases b <;> exact put) (ih (b::o))
    simpa [restore, List.reverse_cons, List.append_assoc, Nat.mul_succ, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h

/-- Deterministic stack update after a field has been read. -/
def fieldResult (s : Stacks InputPort) (f : Field) (data suffix : List Bool) : Stacks InputPort :=
  Function.update (Function.update (Function.update s .input suffix) f.counter []) f.output (data ++ s f.output)

/-- One counter mark and one input bit are consumed in three stack steps,
then two steps restore each bit to its original order. -/
theorem readField_runs (s : Stacks InputPort) (f : Field) (data suffix : List Bool)
    (hin : s .input = data ++ suffix) (hc : s f.counter = List.replicate data.length true)
    (ht : s .tmp = []) :
    (readField f).Runs (5*data.length+2) s (fieldResult s f data suffix) := by
  have h₁ := collect_runs s f data suffix [] (s f.output)
  simp only [List.append_nil] at h₁
  have h₂ := restore_runs s f suffix [] data.reverse (s f.output)
  simp only [List.length_reverse, List.reverse_reverse] at h₂
  have hs := frame_eq s f
  rw [hin, hc, ht] at hs
  have he : frame s f suffix [] [] (data ++ s f.output) = fieldResult s f data suffix := by
    funext i
    cases f <;> cases i <;> first | rfl | exact ht.symm
  rw [hs] at h₁
  rw [he] at h₂
  exact (show 3*data.length+1+(2*data.length+1) = 5*data.length+2 by omega) ▸ h₁.followedBy h₂

/-- A zero padding bit consumes a pop and a return. A one in this region
executes a rejecting halt. -/
def padding := popLoop InputPort.input (fun _ => true) Routine.ret (Routine.halt false)

theorem padding_runs (s : Stacks InputPort) (n : ℕ) (hi : s .input = List.replicate n false) :
    padding.Runs (2*n+1) s (Function.update s .input []) := by
  induction n generalizing s with
  | zero =>
    change s .input = [] at hi
    have he : Function.update s .input [] = s := by rw [← hi]; exact Function.update_eq_self _ _
    rw [he]
    exact Runs.popLoop_empty InputPort.input _ _ _ hi
  | succ n ih =>
    rw [List.replicate_succ] at hi
    let t := Function.update s InputPort.input (List.replicate n false)
    have hh := Runs.popLoop_false_continue InputPort.input (fun _ => true) Routine.ret (Routine.halt false)
      hi rfl (runs_ret t) (ih t (Function.update_self ..))
    have he : Function.update t .input [] = Function.update s .input [] := by
      simp [t, Function.update_idem]
    rw [he] at hh
    exact (show 1+1+(2*n+1) = 2*(n+1)+1 by omega) ▸ hh

end RAMTape.InputReader

end VPVNP
end Computability
end OAI
