import OAI.Optimization.LinearProgramming.Recovery.PrincipalFinish
import OAI.Optimization.LinearProgramming.Recovery.PhysicalSupport
import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationCost

/-! A single clock chosen before the LP input. Heights of selected complementary
bases are always at most m+1, including during all m support-deletion calls. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal
open RAM RAM.Callable Geometry Polynomial

noncomputable def capPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ := C (capacityC s)*(X+2)^(capacityE s)+2
noncomputable def queryPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ :=
  19*capPolynomial s+225+(2*(MaskedDecision.clockPolynomial s).comp (2*(X+1))+2)
noncomputable def scanPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ :=
  4*(5*(X+1)+7)+(X*(queryPolynomial s+34)+1)
noncomputable def scanAddresses (s : NormalSubspace.Spec) : Polynomial ℕ :=
  C (scan s).localBudget+2*(capPolynomial s+InitialOrientation.finalAddresses s)+1+scanPolynomial s
noncomputable def searchPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ := scanPolynomial s+
  ((19*capPolynomial s+225+(2*WitnessProgram.clockPolynomial.comp (2*(X+1))+2))+
  (4*WitnessCall.receivePolynomial.comp (scanAddresses s)+(21*(X+1)+5)))
noncomputable def searchAddresses (s : NormalSubspace.Spec) : Polynomial ℕ :=
  C (searchWitness s).localBudget+2*(capPolynomial s+InitialOrientation.finalAddresses s)+1+searchPolynomial s

private noncomputable def transposePolynomial : Polynomial ℕ :=
  let read:=X*(4*X+5)+4*X+6
  X*(X*(read+X*(4*X+5)+4*X+6+3)+5)+2

noncomputable def publishPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ :=
  16+(4*((PrimalOutput.headerTime.comp (searchAddresses s))+(10*X+6+transposePolynomial))+
    ((19*capPolynomial s+225+(2*10_000_000_000*(X+1)^9+2))+(21*X+18)+(13*X+14)))+(8+(13*X+14))
noncomputable def workerClock (s : NormalSubspace.Spec) : Polynomial ℕ := InitialOrientation.clock s+(searchPolynomial s+publishPolynomial s)


theorem cap_eval (s : NormalSubspace.Spec) (m d : ℕ) : (capPolynomial s).eval (m+d)=capacity s m d := by
  simp [capPolynomial,capacity,SupportBundle.capacity,polyBound,Nat.add_assoc]

theorem query_time_le (s : NormalSubspace.Spec) (m d h : ℕ) (height : h ≤ m+1) :
    SupportBundle.callClock s h (m+1) (capacity s m d) ≤ (queryPolynomial s).eval (m+d) := by
  have time:=MaskedDecision.eval_mono (MaskedDecision.clockPolynomial s) (show h+(m+1) ≤ 2*((m+d)+1) by omega)
  unfold SupportBundle.callClock
  conv_rhs => simp [queryPolynomial,cap_eval]
  omega

theorem scan_time_le (s : NormalSubspace.Spec) (m d h : ℕ) (height : h ≤ m+1) :
    scanTime s h m (capacity s m d) ≤ (scanPolynomial s).eval (m+d) := by
  have query:=query_time_le s m d h height
  unfold scanTime
  conv_rhs => simp [scanPolynomial]
  gcongr <;>omega

private theorem address_work_bound (budget dimension : ℕ) (cap limit work : Polynomial ℕ)
    {capacity steps : ℕ} (cap_at : cap.eval dimension = capacity)
    (time : steps ≤ work.eval dimension) :
    max budget (2 * max capacity (limit.eval dimension) + 1) + steps ≤
      (C budget + 2 * (cap + limit) + 1 + work).eval dimension := by
  simp only [eval_add, eval_mul, eval_C, eval_ofNat, eval_one, cap_at]
  have combined : max capacity (limit.eval dimension) ≤ capacity + limit.eval dimension :=
    max_le (by omega) (by omega)
  exact Nat.add_le_add (max_le (by omega) (by omega)) time

theorem scan_limit_le (s : NormalSubspace.Spec) (m d h : ℕ) (height : h ≤ m+1) :
    scanLimit s h m (capacity s m d) ((InitialOrientation.finalAddresses s).eval (m+d)) ≤ (scanAddresses s).eval (m+d) := by
  unfold scanLimit nextLimit scanAddresses
  exact address_work_bound (scan s).localBudget (m+d) (capPolynomial s)
    (InitialOrientation.finalAddresses s) (scanPolynomial s) (cap_eval s m d)
    (scan_time_le s m d h height)

theorem search_time_le (s : NormalSubspace.Spec) (m d h : ℕ) (height : h ≤ m+1) :
    searchTime s h m (capacity s m d) ((InitialOrientation.finalAddresses s).eval (m+d)) ≤ (searchPolynomial s).eval (m+d) := by
  have scan:=scan_time_le s m d h height
  have receive:=MaskedDecision.eval_mono WitnessCall.receivePolynomial (scan_limit_le s m d h height)
  have solve:=MaskedDecision.eval_mono WitnessProgram.clockPolynomial (show h+(m+1) ≤ 2*((m+d)+1) by omega)
  unfold searchTime WitnessCall.numericalTime WitnessCall.receiveTime
  conv_rhs => simp [searchPolynomial,cap_eval]
  omega

theorem search_limit_le (s : NormalSubspace.Spec) (m d h : ℕ) (height : h ≤ m+1) :
    nextLimit (searchWitness s) (capacity s m d) ((InitialOrientation.finalAddresses s).eval (m+d))
      (searchTime s h m (capacity s m d) ((InitialOrientation.finalAddresses s).eval (m+d))) ≤ (searchAddresses s).eval (m+d) := by
  unfold nextLimit searchAddresses
  exact address_work_bound (searchWitness s).localBudget (m+d) (capPolynomial s)
    (InitialOrientation.finalAddresses s) (searchPolynomial s) (cap_eval s m d)
    (search_time_le s m d h height)

private theorem transpose_le (m d : ℕ) : uniformTableTime d m (InitialPair.readBound d m) ≤ transposePolynomial.eval (m+d) := by
  unfold uniformTableTime uniformEntryTime InitialPair.readBound
  conv_rhs => simp [transposePolynomial]
  rw [Nat.add_comm d m];gcongr <;>omega

theorem finish_time_le (s : NormalSubspace.Spec) (m d : ℕ) :
    finishTime m d (capacity s m d) ((searchAddresses s).eval (m+d)) ≤ (publishPolynomial s).eval (m+d) := by
  have tr:=transpose_le m d
  have odd_m : Publish.oddTime m ≤ 13*(m+d)+14:=by unfold Publish.oddTime;omega
  have odd_d : Publish.oddTime d ≤ 13*(m+d)+14:=by unfold Publish.oddTime;omega
  have out : WitnessExport.time d ≤ 21*(m+d)+18:=by unfold WitnessExport.time;omega
  unfold finishTime PrimalOutput.programTime PrimalOutput.assembleTime WitnessSolve.time WitnessSolve.callTime WitnessSolve.solverTime
  conv_rhs => simp [publishPolynomial,cap_eval]
  rw [Nat.add_comm d m]
  have order (v : ℕ) : 2*(10_000_000_000*v)=2*10_000_000_000*v:=by ring
  rw [order];omega

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
