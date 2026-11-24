import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-!
# Prepending a five-word successor record

The record fields are words 3 through 7 of the successor message. To
prepend them in increasing order, the machine visits them in decreasing
order. For each word it reverses the bits onto a scratch stack, then pops
them back to both the source and the record.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorFields

/-- Ports used to prepend successor words three through seven to the saved record while
restoring the word stacks. -/
inductive RecordPort where
  | tmp | record | word (i : Fin 8)
  deriving DecidableEq, Fintype

private inductive CopyPort where
  | src | tmp | dst
  deriving DecidableEq

private inductive CopyState where
  | read | save (b : Bool) | restore | putSource (b : Bool) | putRecord (b : Bool) | done
  deriving DecidableEq, Fintype

private def copyCode : StackCode CopyPort CopyState
  | .read => .pop .src fun b => b.elim .restore .save
  | .save b => .push .tmp b .read
  | .restore => .pop .tmp fun b => b.elim .done .putSource
  | .putSource b => .push .src b (.putRecord b)
  | .putRecord b => .push .dst b .restore
  | .done => .halt true

private def frame (x tmp dst : List Bool) : Stacks CopyPort
  | .src => x
  | .tmp => tmp
  | .dst => dst

private theorem update_frame (x tmp dst bits : List Bool) (k : CopyPort) :
    Function.update (frame x tmp dst) k bits = match k with
      | .src => frame bits tmp dst
      | .tmp => frame x bits dst
      | .dst => frame x tmp bits := by
  cases k <;> funext j <;> cases j <;> rfl

local macro "copy_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [frame, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_frame])

private theorem read_runs (x tmp dst : List Bool) :
    StackRuns copyCode (2*x.length+1) .read (frame x tmp dst)
      .restore (frame [] (x.reverse ++ tmp) dst) := by
  induction x generalizing tmp with
  | nil => copy_step; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    copy_step
    copy_step
    exact ih (b :: tmp)

private theorem restore_runs (x tmp dst : List Bool) :
    StackRuns copyCode (3*tmp.length+1) .restore (frame x tmp dst)
      .done (frame (tmp.reverse ++ x) [] (tmp.reverse ++ dst)) := by
  induction tmp generalizing x dst with
  | nil => copy_step; exact .nil ..
  | cons b tmp ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    copy_step
    copy_step
    copy_step
    exact ih (b :: x) (b :: dst)

private theorem copy_runs (x dst : List Bool) :
    StackRuns copyCode (5*x.length+2) .read (frame x [] dst) .done (frame x [] (x ++ dst)) := by
  have h := read_runs x [] dst
  rw [List.append_nil] at h
  have h' := restore_runs [] x.reverse dst
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h'
  rw [show 5*x.length+2 = (2*x.length+1) + (3*x.length+1) by omega]
  exact h.trans h'

private def normal : CopyState → Bool
  | .done => true
  | _ => false

private def copyPorts {K : Type} (src dst tmp : K) : CopyPort → K
  | .src => src
  | .tmp => tmp
  | .dst => dst

/-- Prepend the contents of one bit stack to another, preserving their order
and restoring the source. The temporary stack must start empty. -/
def prependCopy {K : Type} (src dst tmp : K) : FiniteRoutine K :=
  FiniteRoutine.ofStackCode copyCode (copyPorts src dst tmp) .read normal

/-- Each bit costs two instructions to save it and three to restore and copy it.
The two empty pops finish the scans. Only the destination changes. -/
theorem prependCopy_runs {K : Type} [DecidableEq K] (src dst tmp : K)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) (s : Stacks K) (ht : s tmp = []) :
    (prependCopy src dst tmp).Runs (5 * (s src).length + 2) s
      (Function.update s dst (s src ++ s dst)) := by
  have inj : Function.Injective (copyPorts src dst tmp) := by
    intro i j h
    cases i <;> cases j <;> simp_all [copyPorts]
  apply FiniteRoutine.runs_ofStackCode_framed inj (normal := normal) rfl rfl
    (fun q h => by cases q <;> first | rfl | contradiction) (copy_runs (s src) (s dst))
  · intro i
    cases i <;> first | rfl | exact ht
  · intro i
    cases i <;> simp [copyPorts, frame, hsd, hdt.symm, ht]
  · intro i h
    exact Function.update_of_ne (Ne.symm (h .dst)) ..

private def copyField {K : Type} (ports : RecordPort → K) (i : Fin 8) : FiniteRoutine K :=
  prependCopy (ports (.word i)) (ports .record) (ports .tmp)

private theorem copyField_runs {K : Type} [DecidableEq K] {ports : RecordPort → K}
    (hp : Function.Injective ports) (i : Fin 8) (s : Stacks K) (ht : s (ports .tmp) = []) :
    (copyField ports i).Runs (5*(s (ports (.word i))).length+2) s
      (Function.update s (ports .record) (s (ports (.word i)) ++ s (ports .record))) :=
  prependCopy_runs _ _ _ (hp.ne (by simp)) (hp.ne (by simp)) (hp.ne (by simp)) s ht

/-- A fixed routine for the record payload, independent of the word width. -/
def appendRecord {K : Type} (ports : RecordPort → K) : FiniteRoutine K :=
  ((((copyField ports 7).followedBy (copyField ports 6)).followedBy (copyField ports 5)).followedBy
    (copyField ports 4)).followedBy (copyField ports 3)

/-- Each word costs two empty pops and five instructions per bit. All
source and scratch stacks return to their initial contents. -/
theorem appendRecord_runs {K : Type} [DecidableEq K] {ports : RecordPort → K}
    (hp : Function.Injective ports) (s : Stacks K) {w : ℕ} (ht : s (ports .tmp) = [])
    (hlen : ∀ i : Fin 8, 3 ≤ i.val → (s (ports (.word i))).length = w) :
    (appendRecord ports).Runs (25*w+10) s (Function.update s (ports .record)
      (s (ports (.word 3)) ++ s (ports (.word 4)) ++ s (ports (.word 5)) ++ s (ports (.word 6))
        ++ s (ports (.word 7)) ++ s (ports .record))) := by
  let state (bits : List Bool) := Function.update s (ports .record) bits
  let word (i : Fin 8) := s (ports (.word i))
  have step (i : Fin 8) (hi : 3 ≤ i.val) (bits : List Bool) :
      (copyField ports i).Runs (5*w+2) (state bits) (state (word i ++ bits)) := by
    have ht' : state bits (ports .tmp) = [] := by simp [state, hp.eq_iff, ht]
    have hi' : state bits (ports (.word i)) = word i := by
      simp [state, word, hp.eq_iff]
    simpa only [hi', word, hlen i hi, state, Function.update_self, Function.update_idem] using
      copyField_runs hp i (state bits) ht'
  have h7 := step 7 (by decide) (s (ports .record))
  have h6 := FiniteRoutine.Runs.followedBy h7 (step 6 (by decide) _)
  have h5 := FiniteRoutine.Runs.followedBy h6 (step 5 (by decide) _)
  have h4 := FiniteRoutine.Runs.followedBy h5 (step 4 (by decide) _)
  have h3 := FiniteRoutine.Runs.followedBy h4 (step 3 (by decide) _)
  rw [show 25*w+10 = (5*w+2)+(5*w+2)+(5*w+2)+(5*w+2)+(5*w+2) by omega]
  simpa only [appendRecord, state, word, Function.update_eq_self, List.append_assoc] using h3

end RAMTape.SuccessorFields

end VPVNP
end Computability
end OAI
