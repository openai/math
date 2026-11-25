import OAI.Hierarchy.ProtocolRAMCalendarLifetimes
import OAI.Hierarchy.ProtocolRAMCalendarThreshold
import OAI.Hierarchy.ProtocolRAMCalendarReplay
import OAI.Hierarchy.ProbeCalendarBoundary
import OAI.Hierarchy.ProbeCalendarLedger

namespace OAI
/-! # Chronological stock and signed payments read from the native probing calendar -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section

variable {w q d : ℕ} {I : Type*} [Fintype I]

/-- Prior saturation requires an entire actual interval of mode-two or
mode-three trials. Otherwise an unexhausted interval contains a mode-one advance. -/
theorem advance_when_regular (C : Chart w q d) (mem : Memory w) (total j : ℕ) (hj : j<total)
    (positive : 0<C.mesh.outerFuel) (laws : ∀ i<total, outerLaw C.mesh (observedHistory C mem) i)
    (before : ¬ProbeCalendarLedger.past (observedMode C mem) C.mesh.outerFuel j)
    (notAll : ¬ProbeCalendarLedger.exhaust (observedMode C mem) C.mesh.outerFuel j) :
    ∃ h<C.mesh.outerFuel, observedMode C mem j h=1 := by
  classical
  let H := observedHistory C mem
  have room : ¬ externalCap C.mesh H j := by
    rintro (zero | ⟨i, hi, last⟩)
    · omega
    · exact before ⟨i,hi,all_outer_paid_of_last C.mesh H i positive (laws i (hi.trans hj)) last⟩
  by_contra none
  apply notAll
  intro h hh
  have active : ¬ disabled C.mesh H (.outer j h) := by
    rintro (expired | ⟨b, hb, low⟩)
    · exact room expired
    · exact none ⟨b,hb.trans hh,low⟩
  have real := laws j hj h hh
  change (if disabled C.mesh H (.outer j h) then _ else _) at real
  rw [ite_eq_right active] at real
  exact real.resolve_left (fun hit => none ⟨h,hh,hit⟩)

theorem disabled_after_advance (C : Chart w q d) (mem : Memory w) (p h b : ℕ)
    (law : outerLaw C.mesh (observedHistory C mem) p) (hb : b<C.mesh.outerFuel)
    (earlier : h<b) (hit : observedMode C mem p h=1) : observedMode C mem p b=0 := by
  have disabledNow : disabled C.mesh (observedHistory C mem) (.outer p b) := Or.inr ⟨h,earlier,hit⟩
  have mode := law b hb
  change (if disabled C.mesh (observedHistory C mem) (.outer p b) then _ else _) at mode
  simpa only [ite_eq_left disabledNow,observedHistory] using mode

/-- Outside the acquisition branch the reserve starts empty. The inner clock
still runs every zero-mask repair and feeds the corresponding empty slice.
These readbacks concern individual native transitions only. -/
structure QuietCalendar (A : AccountColumns I) (C : Chart w q d) (mem : Memory w) : Prop where
  attempt : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps,
    ∀ b<C.mesh.innerFuel, observedMode C mem p h≠3 → observedInnerMode C mem p h j b=0 →
      A.inner C mem p h j (b+1)=A.inner C mem p h j b
  feed : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel, ∀ j<C.mesh.reserveSteps,
    observedMode C mem p h≠3 →
      A.inner C mem p h (j+1) 0=A.inner C mem p h j C.mesh.innerFuel
  «alias» : ∀ p<C.mesh.inject+C.mesh.cool, ∀ h<C.mesh.outerFuel,
    A.trial C mem p (h+1)=A.inner C mem p h C.mesh.reserveSteps 0

omit [Fintype I] in
theorem QuietCalendar.no_purchase {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    (Q : QuietCalendar A C mem) (archives : ArchiveRoom C mem (C.mesh.inject+C.mesh.cool))
    {p h : ℕ} (hp : p<C.mesh.inject+C.mesh.cool) (hh : h<C.mesh.outerFuel)
    (idle : observedMode C mem p h≠3) :
    A.trial C mem p (h+1)=A.inner C mem p h 0 0 := by
  have through (j : ℕ) (hj : j<C.mesh.reserveSteps) (b : ℕ) (bound : b≤C.mesh.innerFuel) :
      A.inner C mem p h j b=A.inner C mem p h j 0 := by
    induction b with
    | zero => rfl
    | succ b before =>
      have hb : b<C.mesh.innerFuel := by omega
      let H := observedHistory C mem
      have off : disabled C.mesh H (.inner p h j b) := Or.inl idle
      have mode := archives.inner_law p h j hp hh hj b hb
      change (if disabled C.mesh H (.inner p h j b) then _ else _) at mode
      rw [ite_eq_left off] at mode
      exact (Q.attempt p hp h hh j hj b hb idle mode).trans (before hb.le)
  have slices (j : ℕ) (bound : j≤C.mesh.reserveSteps) : A.inner C mem p h j 0=A.inner C mem p h 0 0 := by
    induction j with
    | zero => rfl
    | succ j before =>
      have here : j<C.mesh.reserveSteps := by omega
      exact (Q.feed p hp h hh j here idle).trans ((through j here _ le_rfl).trans (before here.le))
  exact (Q.alias p hp h hh).trans (slices _ le_rfl)

structure CalendarReadbacks (A : AccountColumns I) (C : Chart w q d) (mem : Memory w)
    (n m K cap : ℕ) (s₀ r scale ρ γ ρBuy reward : ℝ) : Prop where
  injection : C.mesh.inject=m
  cooling : C.mesh.cool=m
  outerFuel : 0<C.mesh.outerFuel
  lifetimes : ModeLifetimes C
  mounted : Calendar.mounted C (events C.mesh) mem
  quietTimeline : QuietCalendar A C mem
  idleHead : ∀ j < m+m, ∀ h<C.mesh.outerFuel, (observedMode C mem j h=0 ∨ observedMode C mem j h=1) →
    (A.inner C mem j h 0 0).bits=(A.trial C mem j h).bits ∧
      (A.inner C mem j h 0 0).paid≤(A.trial C mem j h).paid
  failedHead : ∀ j < m+m, ∀ h<C.mesh.outerFuel, observedMode C mem j h=2 →
    Nonempty (A.bank.FailedRows n A.payloadWidth K cap ρ γ (phaseTime s₀ m j) (A.trial C mem j h)
      (A.inner C mem j h 0 0))
  acquired : ∀ j < m+m, ∀ h<C.mesh.outerFuel, observedMode C mem j h=3 →
    Nonempty (Acquisition A C mem j h n K cap ρ γ ρBuy reward (phaseTime s₀ m j))
  feed : ∀ j < m+m, A.bank.BoundaryRead m A.payloadWidth cap j (A.trial C mem j C.mesh.outerFuel)
    (A.trial C mem (j+1) 0)
  scoreRoom : ∀ j < m+m, ∀ h<C.mesh.outerFuel, TestRoom (repair C (.outer j h)) w
  payloadWords : ∀ j < m, ∀ h<C.mesh.outerFuel,
    let a := Attempt.outer j h
    let B := repair C a
    let source := prepared C a (trialState C mem j h)
    Nonempty (SumCalibration B.tests.payload (B.tests.excess.after source)
      (pairing (fun i=>(A.payload i:ℝ)) (maximizer A.a A.M 1 A.coefficient A.box
        (A.bank.units A.payloadWidth (A.trial C mem j h)))) ((3/2:ℝ)*n))
  coolWords : ∀ k < m, ∀ h<C.mesh.outerFuel,
    let a := Attempt.outer (m+k) h
    let B := repair C a
    let source := prepared C a (trialState C mem (m+k) h)
    Nonempty (SumCalibration B.tests.excess source
      (score A.a A.M A.coefficient (maximizer A.a A.M (clockTime s₀ m k) A.coefficient A.box
        (A.bank.units A.payloadWidth (A.trial C mem (m+k) h))))
      ((scale*min (1/clockTime s₀ m k) (1/r)+1/2)*n))

theorem CalendarReadbacks.payloadLow {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (j : ℕ) (hj : j < m) (h : ℕ) (hh : h<C.mesh.outerFuel) (hit : observedMode C mem j h=1) :
    pairing (fun i=>(A.payload i:ℝ)) (maximizer A.a A.M 1 A.coefficient A.box
      (A.bank.units A.payloadWidth (A.trial C mem j h)))≤(3/2:ℝ)*n := by
  obtain ⟨rows⟩ := R.payloadWords j hj h hh
  exact rows.low ((observed_low C mem j h (R.scoreRoom j (by omega) h hh) hit).2 (by rwa [R.injection]))

theorem CalendarReadbacks.coolLow {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (k : ℕ) (hk : k < m) (h : ℕ) (hh : h<C.mesh.outerFuel) (hit : observedMode C mem (m+k) h=1) :
    score A.a A.M A.coefficient (maximizer A.a A.M (clockTime s₀ m k) A.coefficient A.box
      (A.bank.units A.payloadWidth (A.trial C mem (m+k) h)))≤(scale*min (1/clockTime s₀ m k) (1/r)+1/2)*n := by
  obtain ⟨rows⟩ := R.coolWords k hk h hh
  exact rows.low (observed_low C mem (m+k) h (R.scoreRoom (m+k) (by omega) h hh) hit).1

theorem CalendarReadbacks.archiveRoom {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward) : ArchiveRoom C mem (m+m) := by
  simpa only [R.injection,R.cooling] using R.lifetimes.archive R.mounted

theorem CalendarReadbacks.idle {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (j : ℕ) (hj : j < m+m) (h : ℕ) (hh : h<C.mesh.outerFuel)
    (off : observedMode C mem j h=0 ∨ observedMode C mem j h=1) :
    (A.trial C mem j (h+1)).bits=(A.trial C mem j h).bits ∧
      (A.trial C mem j (h+1)).paid≤(A.trial C mem j h).paid := by
  have bound : j<C.mesh.inject+C.mesh.cool := by rwa [R.injection,R.cooling]
  rw [R.quietTimeline.no_purchase (R.lifetimes.archive R.mounted) bound hh (by omega)]
  exact R.idleHead j hj h hh off

theorem CalendarReadbacks.failed {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (j : ℕ) (hj : j < m+m) (h : ℕ) (hh : h<C.mesh.outerFuel)
    (hit : observedMode C mem j h=2) :
    Nonempty (A.bank.FailedRows n A.payloadWidth K cap ρ γ (phaseTime s₀ m j) (A.trial C mem j h)
      (A.trial C mem j (h+1))) := by
  have bound : j<C.mesh.inject+C.mesh.cool := by rwa [R.injection,R.cooling]
  rw [R.quietTimeline.no_purchase (R.lifetimes.archive R.mounted) bound hh (by omega)]
  exact R.failedHead j hj h hh hit

theorem CalendarReadbacks.bought {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (j : ℕ) (hj : j < m+m) (h : ℕ) (hh : h<C.mesh.outerFuel) (hit : observedMode C mem j h=3) :
    A.purchase C mem j h n K cap ρ γ ρBuy reward (phaseTime s₀ m j) := by
  obtain ⟨q⟩ := R.acquired j hj h hh hit
  exact q.purchase R.archiveRoom hj hh hit

theorem CalendarReadbacks.law {A : AccountColumns I} {C : Chart w q d} {mem : Memory w}
    {n m K cap : ℕ} {s₀ r scale ρ γ ρBuy reward : ℝ}
    (R : CalendarReadbacks A C mem n m K cap s₀ r scale ρ γ ρBuy reward)
    (j : ℕ) (hj : j < m+m) : outerLaw C.mesh (observedHistory C mem) j := R.archiveRoom.outer_law j hj

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
