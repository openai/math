import OAI.ThreeFlat.RAM.ProcedureBank
import OAI.ThreeFlat.RAM.PhysicalExactRun
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Execute a series with genuine data dependencies between successive stages -/
namespace Hierarchy.ProtocolRAMDependentSeries
open Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators

/-- A stage may read every earlier stage. The invariant at stage zero is the
actual immutable input and each step produces the next invariant on the
same heap as its physical execution. -/
theorem chain {W : ℕ} (n : ℕ) (P : Fin (n+1)→Procedure W) (ticks : Fin (n+1)→ℕ)
    (inv : ℕ→Memory W→Prop) (mem : Memory W) (start : inv 0 mem)
    (run : ∀i s,inv i.val s→∃t,(P i).Exec s t (ticks i) ∧ inv (i.val+1) t) :
    ∃t,(ProcedureBank.program n P).Exec mem t (∑i,ticks i) ∧ inv (n+1) t := by
  induction n generalizing mem inv with
  | zero=>
    obtain ⟨t,h,ok⟩:=run 0 mem start
    refine ⟨t,?_,ok⟩
    have one : (∑ i,ticks i)=ticks 0:=by simp
    rw [one]
    change (P 0).Exec mem t (ticks 0)
    exact @h
  | succ k ih=>
    obtain ⟨m,first,ready⟩:=run 0 mem start
    obtain ⟨t,rest,done⟩:=ih (fun i=>P i.succ) (fun i=>ticks i.succ)
      (fun i=>inv (i+1)) m ready (fun i s hi=>run i.succ s hi)
    refine ⟨t,?_,done⟩
    rw [ProcedureBank.program,Fin.sum_univ_succ]
    exact first.then rest

end Hierarchy.ProtocolRAMDependentSeries

end OAI
