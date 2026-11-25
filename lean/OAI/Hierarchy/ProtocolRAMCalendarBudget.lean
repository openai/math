import OAI.Hierarchy.ProtocolRAMCalendarSpend

namespace OAI
/-! # The signed terminal budget of the executed RAM probing calendar -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators
noncomputable section

variable {w q d : ℕ} {I : Type*} [Fintype I] {A : AccountColumns I} {C : Chart w q d}
    {mem : Memory w} {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward V G P Q : ℝ}

/-- The observed low-price advance can occur before the final trial of an
interval. Its retained stock persists through the remaining disabled trials,
so its measured score prices the actual feed at the end of the interval. -/
theorem CalendarReadbacks.regular_boundary (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (hn : 0 < n) (hm : 0 < m) (hw : m ≤ A.payloadWidth) (hs : 0 < s₀) (hs₁ : s₀ ≤ 1)
    (hV : 0 ≤ V) (hG : 0 ≤ G) (lv : V ≤ A.a*m) (lg : G ≤ s₀*A.a*m)
    (bound : OuterBounds A.bank n A.payloadWidth m cap s₀ V G P Q) {j : ℕ} (hj : j < m+m)
    (before : ¬ProbeCalendarLedger.past (observedMode C mem) C.mesh.outerFuel j)
    (miss : ¬ProbeCalendarLedger.exhaust (observedMode C mem) C.mesh.outerFuel j) :
    A.bank.normalized A.payloadWidth n m s₀ (j+1) (A.trial C mem (j+1) 0) ≤
      A.bank.normalized A.payloadWidth n m s₀ j (A.trial C mem j C.mesh.outerFuel) + regularCharge m A.payloadWidth s₀ r scale j := by
  obtain ⟨h,hh,hit⟩ := advance_when_regular C mem (m+m) j hj R.outerFuel R.law before miss
  have keep := R.stock_at_exit (j:=j) (h:=h) hj hh hit
  have same : A.bank.units A.payloadWidth (A.trial C mem j C.mesh.outerFuel) = A.bank.units A.payloadWidth (A.trial C mem j h) := by
    funext i
    change (((A.trial C mem j C.mesh.outerFuel).bits i:ℝ)/A.payloadWidth) = ((A.trial C mem j h).bits i:ℝ)/A.payloadWidth
    rw [keep]
  apply (R.feed j hj).regular hn hm hw hs hs₁ hV hG lv lg bound hj
  · intro early
    rw [same]
    exact R.payloadLow j early h hh hit
  · intro k eq
    rw [same]
    subst j
    exact R.coolLow k (by omega) h hh hit

/-- After all physical attempts and feeds have run, the cash already paid
plus the box price of all remaining bits is at most six times the population.
All repair modes and both boundary prices are read along this one execution. -/
theorem CalendarReadbacks.terminal
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (hn : 0 < n) (hm : 0 < m) (hw : m ≤ A.payloadWidth) (hK : 0 < K)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hρBuy : 0 < ρBuy) (hrw : 0 < reward)
    (hs : 0 < s₀) (hs₁ : s₀ ≤ 1) (hr : 0 < r) (hr₁ : r ≤ 1)
    (sc : 0 ≤ scale) (intg : scale*(1-Real.log r) ≤ 1)
    (hV : 0 ≤ V) (hG : 0 ≤ G) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (lv : V ≤ A.a*m) (lg : G ≤ s₀*A.a*m) (bound : OuterBounds A.bank n A.payloadWidth m cap s₀ V G P Q)
    (startPrice : A.bank.balance A.payloadWidth 1 (A.read (.outer 0 0) mem) ≤ n)
    (endScore : s₀*score A.a A.M A.coefficient A.box ≤ n)
    (fuel : 5-(C.mesh.outerFuel:ℝ)*repairGain K ρ γ ρBuy reward ≤ -(P+Q+1)) :
    let final := A.read (.outer (C.mesh.inject+C.mesh.cool) 0) (run C (events C.mesh) mem)
    A.bank.cash final + pairing (A.bank.units A.payloadWidth final) A.box ≤ 6*n := by
  let start := fun j => A.bank.normalized A.payloadWidth n m s₀ j (A.trial C mem j 0)
  let exit := fun j => A.bank.normalized A.payloadWidth n m s₀ j (A.trial C mem j C.mesh.outerFuel)
  have np : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have wp := hm.trans_le hw
  have ends := clock_endpoints (s₀:=s₀) hm
  have startTime : phaseTime s₀ m 0=1 := by simp [phaseTime,ends.1]
  have endTime : phaseTime s₀ m (m+m)=s₀ := by simp [phaseTime,ends.2]
  have startPaid : start 0 ≤ 1 := by
    change A.bank.balance A.payloadWidth (phaseTime s₀ m 0) (A.read (.outer 0 0) mem)/n ≤ 1
    rw [startTime,div_le_iff₀ np,one_mul]
    exact startPrice
  have attempts (j : ℕ) (hj : j < m+m) :=
    R.trial_prices hn hm hw hK hρ hγ hρBuy hrw hs hs₁ bound (j:=j) hj
  have regular := regular_spend hm wp hs hs₁ hr hr₁ sc intg
  have crude := crude_spend (C:=P) hm wp hs hQ
  have paid := ProbeCalendarLedger.calendar_paid (m+m) C.mesh.outerFuel (observedMode C mem)
    start exit (regularCharge m A.payloadWidth s₀ r scale) (crudeCharge m A.payloadWidth s₀ P Q)
    (upper:=(5:ℝ)) (floor:= -(P+Q+1)) (gain:=repairGain K ρ γ ρBuy reward)
    (fun _ hj => regularCharge_nonneg hm hw hs hs₁ hr sc hj)
    (fun j _ => crudeCharge_nonneg hm hw hs₁ hP hQ j)
    (by linarith only [startPaid,regular]) fuel (by linarith only [crude])
    (fun j hj => (attempts j hj).1) (fun j hj => (attempts j hj).2)
    (fun j hj => R.regular_boundary hn hm hw hs hs₁ hV hG lv lg bound (j:=j) hj)
    (fun j hj => (R.feed j hj).coarse hn hm hw hs hs₁ hV hG lv lg bound hj)
  let final := A.trial C mem (m+m) 0
  change A.bank.balance A.payloadWidth (phaseTime s₀ m (m+m)) final/n ≤ 5 at paid
  rw [endTime,div_le_iff₀ np] at paid
  have finish := finish_at_core A.coefficient A.box (A.bank.units A.payloadWidth final)
    bound.aPos bound.bNonneg bound.MNonneg hs (fun _ => by unfold units; positivity) bound.boxNonneg
  have finalState : A.read (.outer (C.mesh.inject+C.mesh.cool) 0) (run C (events C.mesh) mem) = final := by
    simp only [final,AccountColumns.trial,trial_zero,final_phase,R.injection,R.cooling]
  change A.bank.cash (A.read _ _) + pairing (A.bank.units A.payloadWidth (A.read _ _)) A.box ≤ 6*n
  rw [finalState]
  change A.bank.cash final + potential A.a A.M s₀ A.coefficient A.box (A.bank.units A.payloadWidth final) ≤ 5*n at paid
  change pairing (A.bank.units A.payloadWidth final) A.box ≤
    potential A.a A.M s₀ A.coefficient A.box (A.bank.units A.payloadWidth final) +
      s₀ * score A.a A.M A.coefficient A.box at finish
  calc
    A.bank.cash final + pairing (A.bank.units A.payloadWidth final) A.box
        ≤ A.bank.cash final +
            (potential A.a A.M s₀ A.coefficient A.box (A.bank.units A.payloadWidth final) +
             s₀ * score A.a A.M A.coefficient A.box) := add_le_add le_rfl finish
    _ = (A.bank.cash final + potential A.a A.M s₀ A.coefficient A.box (A.bank.units A.payloadWidth final)) +
          s₀ * score A.a A.M A.coefficient A.box := (add_assoc ..).symm
    _ ≤ 5*n+n := add_le_add paid endScore
    _ = 6*n := by linarith


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
