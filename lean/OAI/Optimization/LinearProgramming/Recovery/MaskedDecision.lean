import OAI.Optimization.LinearProgramming.Recovery.MaskedPreparationCost
import OAI.Optimization.LinearProgramming.Recovery.MaskedDecisionBody
import OAI.Optimization.LinearProgramming.Recovery.MaskedPairBounds
import OAI.Optimization.LinearProgramming.Recovery.PairAccess
import OAI.Optimization.LinearProgramming.RAM.CallablePublicDecision
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! The public support-test entry is a finite ordinary program. Its original
[h,n] tape is exactly h·n rational opposite-basis entries followed by the n flags. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedDecision
open RAM RAM.Callable RAM.Tape Geometry Polynomial

instance body_fixedAccess (s : NormalSubspace.Spec) : Fragment.FixedAccess (body s) := by
  unfold body NormalSubspace.call Fragment.stage Odd.leaf
  infer_instance

noncomputable def bodyPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ :=
  4*preparePolynomial+(MaskedInput.pairTimePolynomial+(19*MaskedInput.pairCapacityPolynomial+225+(2*s.clock+2)+4))

noncomputable def heightPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ :=
  let B:=MaskedInput.pairEntryPolynomial
  X+B+s.height.comp (X+X^2*B)

theorem time_bound (s : NormalSubspace.Spec) (h n : ℕ) : time s h n ≤ (bodyPolynomial s).eval (h+n) := by
  simp only [bodyPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  unfold time NormalSubspace.callTime
  have p:=prepare_bound h n
  have k:=MaskedInput.pairTime_le h n
  have c:=MaskedInput.pairCapacity_le h n
  have f:=eval_mono s.clock (by omega : n ≤ h+n)
  omega

theorem height_bound (s : NormalSubspace.Spec) (h n e : ℕ) : width s h n e ≤ (heightPolynomial s).eval (h+n+e) := by
  have main:=MaskedInput.pairWidth_le h n e
  have row : entryWidth h n e ≤ MaskedInput.pairEntryPolynomial.eval (h+n+e):=max_le (MaskedInput.rowWidth_le ..) (MaskedInput.kernelRowWidth_le ..)
  have number : n ≤ h+n+e:=by omega
  have input : n+n^2*entryWidth h n e ≤ h+n+e+(h+n+e)^2*MaskedInput.pairEntryPolynomial.eval (h+n+e):=by gcongr
  have sol:=eval_mono s.height input
  simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_pow]
  unfold width;omega

noncomputable def program (s : NormalSubspace.Spec) : Program :=
  Boot.publicDecision lengthTerm (body s) guard 1 0 ((bodyPolynomial s).eval 1) (bodyPolynomial s).natDegree

noncomputable def clockPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ :=
  Boot.publicDecisionTime lengthTerm (body s) guard ((bodyPolynomial s).eval 1) (bodyPolynomial s).natDegree

theorem program_spec (s : NormalSubspace.Spec) {h n : ℕ} (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n))
    (hn : 0 < n) (e : ℕ) (three : 3 ≤ e) (rows : ∀i j,ratBits (E i j) ≤ e) :
    ∃ k ≤ (clockPolynomial s).eval (h+n),∃ tr : Fin (k+1)→State ℚ,Trace (program s) (start [h,n] (MaskedInput.bundle E S)) k tr ∧
      (∃ b : Bool,(tr (Fin.last k)).output=some b.toNat ∧ (b=true ↔ ∃z∈LinearMap.ker (maskedEquations E S).mulVecLin,0 ≤ z ∧ 0 < z ⟨0,hn⟩)) ∧
      ∀ i j,ratBits ((tr i).data j) ≤ (heightPolynomial s).eval (h+n+e) := by
  obtain ⟨out,run,decides⟩:=body_run s E S hn e three rows
  let W:=(heightPolynomial s).eval (h+n+e)
  have step:=(time_bound s h n).trans (polynomial_eval_le_polyBound (bodyPolynomial s) _)
  have size:=height_bound s h n e
  have base : e ≤ W:=(show e ≤ width s h n e from (le_max_left ..).trans (le_max_left ..)).trans size
  have original:=MaskedInput.bundle_height E S e three rows
  have num : (MaskedInput.bundle E S).length=lengthTerm.value (Boot.dimensions h n) := by
    change (MaskedInput.bundle E S).length=h*n+n
    simp [MaskedInput.bundle]
  obtain ⟨k,hk,tr,full,tag,_,safe⟩:=Boot.publicDecision_correct lengthTerm (body s) guard 1 0 ((bodyPolynomial s).eval 1) (bodyPolynomial s).natDegree
    h n (MaskedInput.bundle E S) (fun z=>ratBits z ≤ W) out num (fun j=>(original j).trans base) (three.trans base)
    ((run.weakenData (fun _ b=>b.trans size)).mono step)
  exact ⟨k,hk,tr,full,⟨guard.test out,by cases hb : guard.test out <;> simpa [hb] using tag,decides⟩,safe⟩

end MaskedDecision
end Recovery
end LinearProgramming
end Optimization
end OAI
