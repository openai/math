import OAI.Optimization.LinearProgramming.NormalSubspace.OuterStage
import OAI.Optimization.LinearProgramming.NormalSubspace.OuterBank
import OAI.Optimization.LinearProgramming.NormalSubspace.Window
import OAI.Optimization.LinearProgramming.RAM.CallablePublicDecision
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! Pass from the two mathematical register banks of the subspace program to
finite inputs on an ordinary RAM. Both floors depend only on the fixed program
and the two public dimensions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open RAM RAM.Callable RAM.Tape Polynomial

noncomputable def innerFloor (f : Fragment) (c : Cond) (work : Polynomial ℕ) : AddressTerm 2 :=
  Boot.lpTimeFloor (Boot.publicOperandBound f c) ((innerRoom work).eval 1) (innerRoom work).natDegree

noncomputable def installed (f : Fragment) (c : Cond) (work : Polynomial ℕ) : Fragment :=
  .seq (outerStage (innerFloor f c work)) f

noncomputable def installedTime (f : Fragment) (c : Cond) (work : Polynomial ℕ) : Polynomial ℕ :=
  outerStageTime (innerFloor f c work)+work

instance (f : Fragment) [Fragment.FixedAccess f] (c : Cond) (work : Polynomial ℕ) :
    Fragment.FixedAccess (installed f c work) := by
  unfold installed outerStage Odd.leaf Recovery.PackedPCG.numericCall
  infer_instance

/-- A local run starting at both complete ideal banks also runs after the real
inner boot. The last decision reads the same values inside the finite window. -/
theorem installed_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Fragment) [Fragment.FixedAccess f] (guard : Cond) (work : Polynomial ℕ)
    (r c : ℕ) (xs : List K) (P : K→Prop) (Q : Prop) (length : xs.length=(r+c)^2)
    (safe : (start [r,c] xs).memory.AllData P) (zeroSafe : P 0)
    (body : ∀ vm, OuterVM r c (start [r,c] xs).memory vm →
      ∃ out, f.Run P (Odd.memory (Odd.memory (start [] ([]:List K)).memory (start [r,c] xs).memory) vm)
        (work.eval (r+c)) out ∧ (guard.test out=true ↔ Q)) :
    ∃ out, (installed f guard work).Run P (Odd.memory (start [] ([]:List K)).memory (start [r,c] xs).memory)
      ((installedTime f guard work).eval (r+c)) out ∧ (guard.test out=true ↔ Q) := by
  let floor := innerFloor f guard work
  let cap := Boot.twoDimCap subspaceLength floor r c
  let n := r+c
  let bound := 4*n+2*outerVMAddresses.eval n+3
  obtain ⟨vm,stage,data,node,first,dimension,offset,root,addresses⟩ :=
    outerStage_run floor r c xs P length safe zeroSafe
  obtain ⟨out,run,test⟩ := body vm ⟨data,node,first,dimension,offset,root,addresses⟩
  have enough := (Boot.twoDimCap_bounds subspaceLength floor r c).1
  change (Boot.lpTimeFloor (Boot.publicOperandBound f guard) ((innerRoom work).eval 1)
    (innerRoom work).natDegree).value (Boot.dimensions r c)≤cap at enough
  rw [Boot.lpTimeFloor_value] at enough
  have envelope : bound+work.eval n≤polyBound ((innerRoom work).eval 1) (innerRoom work).natDegree n := by
    calc _ = (innerRoom work).eval n := by
           simp only [bound,innerRoom,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
         _ ≤ _ := polynomial_eval_le_polyBound (innerRoom work) n
  have operandWidth : f.localBudget≤Boot.publicOperandBound f guard := le_max_left ..
  have guardBound : guard.accessBudget≤Boot.publicOperandBound f guard := le_max_right ..
  have room : max f.localBudget bound+work.eval n≤cap := by dsimp only [bound,n] at envelope ⊢;omega
  have guardRoom : guard.accessBudget≤cap := by omega
  obtain ⟨t,limited,same⟩ := innerTrim_fixed_run run (nested_index r c xs vm addresses) room
  refine ⟨t,?_,?_⟩
  · simpa only [installed,installedTime,Polynomial.eval_add] using stage.seq limited
  · rw [guard_of_low guard t out guardRoom same];exact test

noncomputable def decisionProgram (f : Fragment) (guard : Cond) (work : Polynomial ℕ) : Program :=
  let time := installedTime f guard work
  Boot.publicDecision subspaceLength (installed f guard work) guard 1 0 (time.eval 1) time.natDegree

noncomputable def decisionTime (f : Fragment) (guard : Cond) (work : Polynomial ℕ) : Polynomial ℕ :=
  let time := installedTime f guard work
  Boot.publicDecisionTime subspaceLength (installed f guard work) guard (time.eval 1) time.natDegree

/-- One fixed ordinary-input program returns the truth of the subspace decision.
Its duration includes all input moves, both finite boots, and the final branch. -/
theorem decision_run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Fragment) [Fragment.FixedAccess f] (guard : Cond) (work : Polynomial ℕ)
    (r c : ℕ) (xs : List K) (P : K→Prop) (Q : Prop) (length : xs.length=(r+c)^2)
    (safe : (start [r,c] xs).memory.AllData P) (zeroSafe : P 0)
    (body : ∀ vm, OuterVM r c (start [r,c] xs).memory vm →
      ∃ out, f.Run P (Odd.memory (Odd.memory (start [] ([]:List K)).memory (start [r,c] xs).memory) vm)
        (work.eval (r+c)) out ∧ (guard.test out=true ↔ Q)) :
    ∃ k≤(decisionTime f guard work).eval (r+c),∃ tr : Fin (k+1)→State K,
      Trace (decisionProgram f guard work) (start [r,c] xs) k tr ∧
      ∃ flag : Bool, (flag=true ↔ Q) ∧ (tr (Fin.last k)).output=some (if flag then 1 else 0) ∧
        ∀ i j,P ((tr i).data j) := by
  obtain ⟨out,go,test⟩ := installed_run f guard work r c xs P Q length safe zeroSafe body
  let time := installedTime f guard work
  obtain ⟨k,hk,tr,executed,halt,_,width⟩ := Boot.publicDecision_correct subspaceLength
    (installed f guard work) guard 1 0 (time.eval 1) time.natDegree r c xs P out
    (length.trans (subspaceLength_value r c).symm) safe zeroSafe
    (go.mono (polynomial_eval_le_polyBound time (r+c)))
  exact ⟨k,hk,tr,executed,guard.test out,test,halt,width⟩

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
