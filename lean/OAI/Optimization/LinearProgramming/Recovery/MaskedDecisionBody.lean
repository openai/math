import OAI.Optimization.LinearProgramming.NormalSubspace.Calls
import OAI.Optimization.LinearProgramming.Recovery.MaskedProgram
import OAI.Optimization.LinearProgramming.Recovery.PairBuilder
import OAI.Optimization.LinearProgramming.Recovery.ConstraintBits
import OAI.Optimization.LinearProgramming.RAM.SafeRun
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf

/-! The caller's support flags are the actual input to a fixed numerical subroutine.
Only the matrix, its flags, and ordinary dimensions enter the native branch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedDecision
open RAM RAM.Callable Geometry Matrix OracleSpec
open scoped Matrix

private def finish : Block := .op (.addrConst 0 0)
def guard : Cond := Odd.cond (.addrLT 0 154)

def body (solver : NormalSubspace.Spec) : Fragment := .seq (Odd.leaf MaskedInput.program)
  (.seq (PairBuilder.program true) (.seq (NormalSubspace.call solver 154) (Odd.leaf finish)))

noncomputable def time (solver : NormalSubspace.Spec) (h n : ℕ) := 4*MaskedInput.programTime h n+
  (PairBuilder.time (MaskedInput.pairLayout h n)+(NormalSubspace.callTime solver (PairBuilder.capacity (h+n) n 0) n+4))

def entryWidth (h n e : ℕ) := max (PairBuilder.rowWidth (h+n) n e)
  (PairBuilder.rowWidth n n (PairBuilder.residualWidth n n (PairBuilder.rowWidth (h+n) n e)))

noncomputable def width (solver : NormalSubspace.Spec) (h n e : ℕ) :=
  max (max e (PairBuilder.pairWidth (h+n) n e)) (solver.height.eval (n+n^2*entryWidth h n e))

private theorem capturedSize {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (dim : r+s=n) (b : ℕ) (hd : ∀i j,ratBits (D i j) ≤ b) (he : ∀i j,ratBits (E i j) ≤ b) :
    r+s+((MinorLog.entries D++MinorLog.entries E).map ratBits).sum ≤ n+n^2*b := by
  subst n;exact NormalSubspace.inputSize_le D E hd he

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  exact Finset.sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

private def blank := (start [] ([] : List ℚ)).memory

private theorem blank_foot : Footprint 0 (blank.atPC 0) := ⟨fun _=>le_rfl,fun _ _=>rfl,fun _ _=>rfl⟩

theorem body_run (solver : NormalSubspace.Spec) {h n : ℕ} (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n))
    (hn : 0 < n) (e : ℕ) (three : 3 ≤ e) (rows : ∀i j,ratBits (E i j) ≤ e) :
    ∃ out,(body solver).Run (fun z=>ratBits z ≤ width solver h n e)
      (Odd.memory blank (start [h,n] (MaskedInput.bundle E S)).memory) (time solver h n) out ∧
      (guard.test out=true ↔ ∃z∈LinearMap.ker (maskedEquations E S).mulVecLin,0 ≤ z ∧ 0 < z ⟨0,hn⟩) := by
  let l:=MaskedInput.pairLayout h n
  let C:=maskedEquations E S
  let W:=width solver h n e
  have low : e ≤ W := (le_max_left ..).trans (le_max_left ..)
  have pairBound : max e (PairBuilder.pairWidth (h+n) n e) ≤ W := le_max_left ..
  have blankSafe : PairBuilder.Within e blank := fun _=>three
  obtain ⟨v,c,hc,read,setup,table⟩:=MaskedInput.program_run E S (fun z=>ratBits z ≤ e) three three (MaskedInput.bundle_height E S e three rows)
  have data:=maskedEquations_bits E S rows three
  obtain ⟨front,back,k,s,F,R,pair,nw,cw,foot,_,packed,_,fb,rb⟩:=PairBuilder.program_run true l C blank v e e setup table
    data blankSafe read.safe_end blank_foot
  obtain ⟨indR,indF,orth,dim,space⟩:=kernelPair_spec C F R packed.firstSpan packed.kernelSpan
  have size:=(eval_mono solver.height (capturedSize R F dim (entryWidth h n e) (fun i j=>(rb i j).trans (le_max_right ..))
    (fun i j=>(fb i j).trans (le_max_left ..)))).trans (le_max_right (max e (PairBuilder.pairWidth (h+n) n e)) _)
  let cap:=PairBuilder.capacity (h+n) n 0
  have positive : 0 < cap:=PairBuilder.old_fits _ _ _
  have raw : RawTapes back l.out 208 cap (encodedGramInput R++encodedGramInput F) [s,k]:=packed.tapes
  obtain ⟨endNative,b,decision,correct,_⟩:=NormalSubspace.call_run solver R F dim hn indR indF orth back front l.out 208 cap
    (cap-1) 154 W raw foot (by omega) (PairBuilder.input_fits (h:=h+n) (n:=n) 0 (by omega))
    (PairBuilder.pair_fits _ _ _) (fun j=>(cw j).trans pairBound) (fun j=>(nw j).trans pairBound) (three.trans low) size
  let vm:=back.putIndex 154 b.toNat
  have endSafe : endNative.AllData (fun z=>ratBits z ≤ W):=fun i=>by simpa only [Odd.data_even] using decision.safe_end (2*i)
  have vmSafe : vm.AllData (fun z=>ratBits z ≤ W):=fun j=>(cw j).trans pairBound
  have endRun:=Odd.leaf_run _ endNative endSafe (Block.Eval.op_addrConst (safe:=Memory.AllData (fun z=>ratBits z ≤ W)) vm 0 0 vmSafe vmSafe)
  have begin:=(Odd.leaf_run _ blank blankSafe read).weakenData (fun _ b=>b.trans low)
  have middle:=pair.weakenData (fun _ b=>b.trans pairBound)
  refine ⟨Odd.memory endNative (vm.putIndex 0 0),(begin.seq (middle.seq (decision.seq endRun))).mono ?_,?_⟩
  · unfold time;gcongr
  · have bit : guard.test (Odd.memory endNative (vm.putIndex 0 0))=b := by
      unfold guard
      rw [Odd.cond_test]
      cases b <;> simp [Cond.test,vm]
    rw [bit,correct]
    change (∃z∈rowSpace R,0 ≤ z ∧ 0 < z ⟨0,hn⟩) ↔ _
    rw [space]

end MaskedDecision
end Recovery
end LinearProgramming
end Optimization
end OAI
