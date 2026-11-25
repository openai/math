import OAI.Optimization.LinearProgramming.Recovery.PrincipalMath
import OAI.Optimization.LinearProgramming.Recovery.PrincipalWitnessReady
import OAI.Optimization.LinearProgramming.Recovery.GlobalCapacity
import OAI.Optimization.LinearProgramming.Recovery.WitnessCall
import OAI.Optimization.LinearProgramming.Recovery.PrincipalRegisters
import OAI.Optimization.LinearProgramming.Recovery.SlackRAM

/-! Execute the full support-deletion scan against fresh native marked-subspace
calls, solve on its final masks, and retrieve the actual normalized vector while
preserving the original inequalities. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal
open RAM RAM.Callable Geometry Matrix SupportRAM

noncomputable def scanWidth (s : NormalSubspace.Spec) (h n e : ℕ) := max e (max ((MaskedDecision.heightPolynomial s).eval (h+n+e)) (WitnessProgram.heightPolynomial.eval (h+n+e)))
noncomputable def scan (s : NormalSubspace.Spec) := markedSearch (SupportBundle.invoke s)
noncomputable def searchWitness (s : NormalSubspace.Spec) : Fragment := (scan s).seq (WitnessCall.invoke.seq WitnessCall.receive)

instance scanAccess (s : NormalSubspace.Spec) : Fragment.FixedAccess (scan s) := by
  unfold scan markedSearch markedLoop markedIteration outerLeaf SupportBundle.invoke Fragment.stage Odd.leaf
  infer_instance

instance witnessAccess (s : NormalSubspace.Spec) : Fragment.FixedAccess (searchWitness s) := by
  unfold searchWitness WitnessCall.invoke WitnessCall.receive Fragment.stage Odd.leaf
  infer_instance

noncomputable def scanTime (s : NormalSubspace.Spec) (h m cap : ℕ) := 4*(5*(m+1)+7)+(m*(SupportBundle.callClock s h (m+1) cap+34)+1)
noncomputable def scanLimit (s : NormalSubspace.Spec) (h m cap limit : ℕ) := nextLimit (scan s) cap limit (scanTime s h m cap)
noncomputable def searchTime (s : NormalSubspace.Spec) (h m cap limit : ℕ) := scanTime s h m cap+
  (WitnessCall.numericalTime h (m+1) cap+WitnessCall.receiveTime (scanLimit s h m cap limit) (m+1))

set_option maxHeartbeats 550000 in
theorem searchWitness_run {m d h : ℕ} (s : NormalSubspace.Spec) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ)
    (E : Matrix (Fin h) (Fin (m+1)) ℚ) (raw src e limit : ℕ) (native caller : Memory ℚ) (thin : h ≤ m+1)
    (three : 3 ≤ e) (rows : ∀i j,ratBits (E i j) ≤ e) (eqs : LinearMap.ker E.mulVecLin=(side A b (ref A b).primal).denote)
    (hi : 256 ≤ raw) (space : raw+(m*d+m) ≤ src) (addr : ∀j,caller.index j ≤ limit)
    (oldSafe : native.AllData (fun q=>ratBits q ≤ e)) (inSafe : caller.AllData (fun q=>ratBits q ≤ e))
    (old : Footprint (capacity s m d-1) (native.atPC 0)) (ctx : SupportBundle.Context E (ref A b).primal src (capacity s m d) caller)
    (origin : SlackRAM.InputAt caller raw A b) (i24 : caller.index 24=raw) (i28 : caller.index 28=m) (i29 : caller.index 29=d) :
    ∃ next out, (searchWitness s).Run (fun q=>ratBits q ≤ scanWidth s h (m+1) e) (Odd.memory native caller)
      (searchTime s h m (capacity s m d) limit) (Odd.memory next out) ∧ Footprint (capacity s m d-1) (next.atPC 0) ∧
      WitnessReady A b raw (src+h*(m+1)+(m+1)) (capacity s m d) out ∧
      next.AllData (fun q=>ratBits q ≤ scanWidth s h (m+1) e) ∧ out.AllData (fun q=>ratBits q ≤ scanWidth s h (m+1) e) ∧
      ∀j,out.index j ≤ nextLimit (searchWitness s) (capacity s m d) limit (searchTime s h m (capacity s m d) limit) := by
  let cap:=capacity s m d
  let n:=m+1
  let W:=scanWidth s h n e
  let base:=src+h*n
  let X:=ref A b
  have be : e ≤ W:=le_max_left ..
  have sm : 3 ≤ W:=three.trans be
  have pn : 0 < n:=Nat.zero_lt_succ _
  have w1 : (MaskedDecision.heightPolynomial s).eval (h+n+e) ≤ W:=(le_max_left ..).trans (le_max_right ..)
  have w2 : WitnessProgram.heightPolynomial.eval (h+n+e) ≤ W:=(le_max_right ..).trans (le_max_right ..)
  obtain ⟨fits,finalFits⟩:=capacity_after_scan s m d h thin
  obtain ⟨words,two,_⟩:=capacity_inputs s m d h thin
  have ns : native.AllData (fun q=>ratBits q ≤ W):=fun j=>(oldSafe j).trans be
  have cs : caller.AllData (fun q=>ratBits q ≤ W):=fun j=>(inSafe j).trans be
  have hc:=SupportBundle.actual_call s E X.primal src cap e W pn three rows w1 sm fits words two
    (restriction A b X.primal) (restriction_correct A b X.primal E eqs)
  obtain ⟨u,v,fp,us,vs,ct,frame,mask,run⟩:=markedSearch_run_withContext (restriction A b X.primal) (SupportBundle.invoke s)
    (fun q=>ratBits q ≤ W) (by exact sm) (by exact sm) (fun z=>Footprint (cap-1) (z.atPC 0)) (SupportBundle.Context E X.primal src cap)
    (SupportBundle.Context.stable E X.primal src cap (by omega)) hc (by omega) native caller old ns cs ctx.marked ctx.flags ctx
  have run' : (scan s).Run (fun q=>ratBits q ≤ W) (Odd.memory native caller) (scanTime s h m cap) (Odd.memory u v):=run
  have mask' : Layout v base n X.allowed:=by rw [show X.allowed=_ from allowed A b];exact mask
  obtain ⟨endNative,found,vec,es,ef⟩:=WitnessCall.invoke_run E X.allowed X.primal src cap e W n pn three rows sm w2 words two
    u v fp us vs ct mask' X.point (normalized_solution A b E eqs)
  have nc (j) : native.index j ≤ cap:=(old.address j).trans (Nat.sub_le ..)
  have bound0:=final_caller_index run' nc addr
  have savedAddresses (j) : (v.putIndex 1 0).index j ≤ scanLimit s h m cap limit:=by
    by_cases hj : j=1
    · simp [Memory.putIndex,hj]
    · simpa [Memory.putIndex,hj,scanLimit] using bound0 j
  have inBound : (v.putIndex 1 0).AllData (fun q=>ratBits q ≤ W):=vs
  have head150 : (v.putIndex 1 0).index 150=n:=by simpa [Memory.putIndex] using ct.marked
  have head151 : (v.putIndex 1 0).index 151=base:=by simpa [Memory.putIndex] using ct.flags
  obtain ⟨out,receive,p212,outVec,data,p24,p28,p29,p60,p156⟩:=WitnessCall.receive_run (fun q=>ratBits q ≤ W) endNative
    (v.putIndex 1 0) base n (scanLimit s h m cap limit) X.point es inBound head150 head151 (by dsimp [base];omega) savedAddresses vec
  have complete : (searchWitness s).Run (fun q=>ratBits q ≤ W) (Odd.memory native caller) (searchTime s h m cap limit) (Odd.memory endNative out):=
    run'.seq (found.seq receive)
  have kept (a : ℕ) (lo : raw ≤ a) (hs : a < raw+(m*d+m)) : out.data a=caller.data a:=by
    have under : a < base:=by dsimp [base];omega
    exact (data a (by omega) (Or.inl (by omega))).trans (frame.data a (by omega) (by omega) (Or.inl under))
  have oldInput : SlackRAM.InputAt out raw A b:=by
    constructor
    · intro i j
      have mul:=Nat.mul_le_mul_right d (Nat.succ_le_of_lt i.isLt)
      rw [Nat.succ_mul] at mul
      exact (kept _ (by omega) (by omega)).trans (origin.1 i j)
    · intro i;exact (kept _ (by omega) (by omega)).trans (origin.2 i)
  refine ⟨endNative,out,complete,ef.mono (Nat.le_sub_one_of_lt finalFits),⟨oldInput,?_,?_,?_,?_,?_,p212,outVec⟩,es,?_,final_caller_index complete nc addr⟩
  · change out.index 24=v.index 24 at p24
    exact p24.trans ((frame.index 24 (by decide) (by decide) (by decide) (by decide)).trans i24)
  · change out.index 28=v.index 28 at p28
    exact p28.trans ((frame.index 28 (by decide) (by decide) (by decide) (by decide)).trans i28)
  · change out.index 29=v.index 29 at p29
    exact p29.trans ((frame.index 29 (by decide) (by decide) (by decide) (by decide)).trans i29)
  · change out.index 60=v.index 60 at p60
    exact p60.trans ct.capacity
  · change out.index 156=v.index 156 at p156
    exact p156.trans ct.sideBit
  · intro j;simpa only [Odd.data_slot] using complete.safe_end (Odd.slot j)

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
