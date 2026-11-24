import OAI.Computability.VPVNP.RoutineSpace
import OAI.Computability.VPVNP.SpaceRunMonotone
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-!
# Staging and cleaning the fixed banks of coefficient-query subroutines

A call copies selected read-only words into its private registers. On return
it prepends selected output stacks to the caller's ports and erases its
private bank. The time bound of the called routine and its space bound
enter the resulting estimates separately.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.CallBank

open RAMTape UniversalCountStack

/-- Stack addresses for the caller's words, the callee's private registers and the scratch
stack used during copying. -/
inductive Port (X I : Type) where
  | external (x : X)
  | internal (i : I)
  | scratch
  deriving DecidableEq, Fintype

variable {X I : Type} [DecidableEq X] [DecidableEq I]

/-- Combine caller and callee stacks into a single call frame with an empty copy scratch stack. -/
def frame (x : Stacks X) (u : Stacks I) : Stacks (Port X I)
  | .external k => x k
  | .internal k => u k
  | .scratch => []

/-- Initial or returned frame containing the caller's stacks and empty private and scratch
banks. -/
def clean (x : Stacks X) := frame (I := I) x fun _ => []

private theorem update_internal (x : Stacks X) (u : Stacks I) (i : I) (v : List Bool) :
    Function.update (frame x u) (.internal i) v = frame x (Function.update u i v) := by
  funext j
  cases j with
  | internal j => by_cases h : i = j <;> simp [frame, h, eq_comm]
  | _ => rfl

private theorem update_external (x : Stacks X) (u : Stacks I) (i : X) (v : List Bool) :
    Function.update (frame x u) (.external i) v = frame (Function.update x i v) u := by
  funext j
  cases j with
  | external j => by_cases h : i = j <;> simp [frame, h, eq_comm]
  | _ => rfl

private def copyIn (source : I → X) (i : I) : FiniteRoutine (Port X I) :=
  SuccessorFields.prependCopy (.external (source i)) (.internal i) .scratch

private def fill (source : I → X) : List I → FiniteRoutine (Port X I)
  | [] => .ret
  | i :: is => (fill source is).followedBy (copyIn source i)

/-- The private inputs after staging a call. Each selected register holds a copy of its
designated caller stack. -/
def filled (source : I → X) (is : List I) (x : Stacks X) (i : I) : List Bool :=
  if i ∈ is then x (source i) else []

private theorem fill_runs (source : I → X) (is : List I) (x : Stacks X) (B : ℕ) (hn : is.Nodup)
    (hB : ∀ k, (x k).length ≤ B) :
    ∃ t ≤ is.length*(5*B+2)+1, (fill source is).Runs t (clean x) (frame x (filled source is x)) := by
  induction is with
  | nil =>
    have he : filled source [] x = fun _ => [] := funext fun _ => by simp [filled]
    rw [he]
    exact ⟨1,by simp,Routine.runs_ret _⟩
  | cons i is ih =>
    obtain ⟨hi,hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨t,ht,hr⟩ := ih hn'
    let u := filled source is x
    have hrun := SuccessorFields.prependCopy_runs (K := Port X I) (.external (source i)) (.internal i) .scratch
      (by simp) (by simp) (by simp) (frame x u) rfl
    change (copyIn source i).Runs (5*(x (source i)).length+2) (frame x u)
      (Function.update (frame x u) (.internal i) (x (source i) ++ u i)) at hrun
    have he : Function.update u i (x (source i) ++ u i) = filled source (i::is) x := by
      funext j
      by_cases h : j=i <;> simp [filled, u, h, hi]
    rw [update_internal, he] at hrun
    refine ⟨_, ?_, hr.followedBy hrun⟩
    have := hB (source i); rw [List.length_cons, Nat.succ_mul is.length (5*B+2)]; omega

private def copyOut (pair : I × X) : FiniteRoutine (Port X I) :=
  SuccessorFields.prependCopy (.internal pair.1) (.external pair.2) .scratch

private def save : List (I × X) → FiniteRoutine (Port X I)
  | [] => .ret
  | p :: ps => (copyOut p).followedBy (save ps)

/-- Caller stacks after prepending the specified callee outputs, in order, to their destination
stacks. -/
def saved (u : Stacks I) : List (I × X) → Stacks X → Stacks X
  | [], x => x
  | (i,k) :: ps, x => saved u ps (Function.update x k (u i ++ x k))

private theorem save_runs (ps : List (I × X)) (x : Stacks X) (u : Stacks I) (C : ℕ) (hC : ∀ i, (u i).length ≤ C) :
    ∃ t ≤ ps.length*(5*C+2)+1, (save ps).Runs t (frame x u) (frame (saved u ps x) u) := by
  induction ps generalizing x with
  | nil => exact ⟨1,by simp,Routine.runs_ret _⟩
  | cons pair ps ih =>
    obtain ⟨i,k⟩ := pair
    have hrun := SuccessorFields.prependCopy_runs (K := Port X I) (.internal i) (.external k) .scratch
      (by simp) (by simp) (by simp) (frame x u) rfl
    change (copyOut (i,k)).Runs (5*(u i).length+2) (frame x u)
      (Function.update (frame x u) (.external k) (u i ++ x k)) at hrun
    rw [update_external] at hrun
    obtain ⟨t,ht,hr⟩ := ih (Function.update x k (u i ++ x k))
    refine ⟨_, ?_, hrun.followedBy hr⟩
    have := hC i; rw [List.length_cons, Nat.succ_mul ps.length (5*C+2)]; omega

omit [DecidableEq X] [DecidableEq I] in
private theorem frame_cap (x : Stacks X) (u : Stacks I) {B C : ℕ}
    (hB : ∀ k, (x k).length ≤ B) (hC : ∀ k, (u k).length ≤ C) (k : Port X I) :
    (frame x u k).length ≤ max B C := by
  cases k with
  | external j => exact (hB j).trans (le_max_left ..)
  | internal j => exact (hC j).trans (le_max_right ..)
  | scratch => exact Nat.zero_le _

/-- Stage the selected input words, execute the private routine, copy its outputs back and
erase the specified private registers. -/
def machine (source : I → X) (ins : List I) (f : FiniteRoutine I) (outs : List (I × X)) (wipe : List I) :
    FiniteRoutine (Port X I) :=
  (((fill source ins).followedBy (f.onPorts Port.internal)).followedBy (save outs)).followedBy
    (SliceArithmetic.CallClear.cleanup (wipe.map Port.internal))

/-- Cost of all copies and clears around the called program. -/
def overhead (inputs outputs cleared B C : ℕ) :=
  (inputs*(5*B+2)+1) + (outputs*(5*C+2)+1) + (cleared*(C+1)+1)

theorem machine_run (source : I → X) (ins : List I) (f : FiniteRoutine I) (outs : List (I × X)) (wipe : List I)
    (x : Stacks X) (u v : Stacks I) {T B C : ℕ} (hn : ins.Nodup) (hB : ∀ k, (x k).length ≤ B)
    (hin : filled source ins x = u) (hr : f.BoundedRun C T u v) (hz : ∀ i ∉ wipe, v i = []) :
    let work := overhead ins.length outs.length wipe.length B C
    ∃ t ≤ T+work, (machine source ins f outs wipe).BoundedRun (B+C+work) t
      (clean x) (clean (saved v outs x)) := by
  intro work
  obtain ⟨a,ha,hfill⟩ := fill_runs source ins x B hn hB
  rw [hin] at hfill
  obtain ⟨b,hb,hsave⟩ := save_runs outs x v C hr.final_cap
  let x' := saved v outs x
  obtain ⟨d,hd,herase⟩ := SliceArithmetic.CallClear.cleanup_runs (wipe.map (Port.internal (X := X))) (frame x' v) C
    (fun i hi => by obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi; exact hr.final_cap j)
  rw [List.length_map] at hd
  have he : SliceArithmetic.CallClear.erased (wipe.map (Port.internal (X := X))) (frame x' v) = clean x' := by
    funext i; cases i with
    | external | scratch => simp [SliceArithmetic.CallClear.erased, clean, frame]
    | internal i => by_cases hi : i ∈ wipe <;> simp [SliceArithmetic.CallClear.erased, clean, frame, hi, hz]
  rw [he] at herase
  have hcapC : C ≤ B+C+work := by omega
  have hcore := FiniteRoutine.BoundedRun.onPorts (a := f) (ports := Port.internal)
    (fun _ _ e => Port.internal.inj e) (frame x u) (hr.mono_cap hcapC)
    (fun k outside => by
      cases k with
      | external j => exact (hB j).trans (by omega)
      | internal i => exact (outside i rfl).elim
      | scratch => exact Nat.zero_le _)
  have install (s : Stacks I) : installStacks (Port.internal (X := X)) (frame x u) s = frame x s := by
    apply installStacks_frame (ports := Port.internal) (base := frame x u) (small := s) (target := frame x s) (fun _ _ e => Port.internal.inj e) (fun _ => rfl)
    rintro (j | j | _) outside <;> first | rfl | exact (outside j rfl).elim
  rw [install, install] at hcore
  have hfill' : (fill source ins).BoundedRun (B+C+work) a (clean x) (frame x u) :=
    spaceRun_of_steps hfill fun k => by
      have hx : (clean (I := I) x k).length ≤ B := by cases k <;> first | apply hB | exact Nat.zero_le _
      dsimp [work, overhead]; omega
  have hs' : (save outs).BoundedRun (B+C+work) b (frame x v) (frame x' v) :=
    spaceRun_of_steps hsave fun k => by
      have := frame_cap x v hB hr.final_cap k; dsimp [work, overhead]; omega
  have hclear' : (SliceArithmetic.CallClear.cleanup (wipe.map (Port.internal (X := X)))).BoundedRun (B+C+work) d
      (frame x' v) (clean x') := spaceRun_of_steps herase fun k => by
    have htemp : SpaceRun (save outs).body.standalone (max B C + b) b (some (save outs).body.entry) (frame x v)
        none (frame x' v) := spaceRun_of_steps hsave fun j => Nat.add_le_add_right (frame_cap x v hB hr.final_cap j) b
    have := htemp.final_cap k
    dsimp [work, overhead]; omega
  refine ⟨_, ?_, ((hfill'.followedBy hcore).followedBy hs').followedBy hclear'⟩
  dsimp [work, overhead]; omega

end RadicalCertificate.MonomialIndex.CallBank

end VPVNP
end Computability
end OAI
