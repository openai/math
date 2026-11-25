import OAI.Computability.NearSquareRoot.FixedCandidateCRTJoint
import OAI.Computability.NearSquareRoot.SelectedKernelProfiles

/-! # Resource profiles of the jointly enumerated CRT procedures -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream.Joint

open Filter DigitPacking CandidateParameters SynchronizedPermutationBudget

/-- The physical kernel's arena and clock on an admitted reserve tuple are
compared with the emitted gather–mask–restore clock of one batch. -/
abbrev ProfileAt (tick arena : Guess → ℕ → ℕ) (j : ℕ) (p : Guess) : Prop :=
  ∃ a c : ℕ, ∀ᶠ n in atTop, arena p n ≤ a*(n+1) ∧
    tick p n ≤ c * max n (CRTBudget.batchClock (Generator.midExponent j) (addressBits n) (CRTBudget.volume n))

/-- The four numeric reserves required by the compiled good-profile theorem. -/
def Enough (need : ℕ → ℕ) (p : Guess) : Prop :=
  need (exponent p) ≤ positionLow p ∧ need (exponent p) ≤ positionHigh p ∧
    ⌈Generator.midExponent (exponent p)⌉₊ + 2 ≤ positionHigh p ∧ need (exponent p) ≤ exterior p

theorem eventually_enough (need : ℕ → ℕ) (j : ℕ) : EventuallyReserves j (Enough need) := by
  filter_upwards [eventually_ge_atTop (need j)] with a ha
  filter_upwards [eventually_ge_atTop (max (need j) (⌈Generator.midExponent j⌉₊+2))] with b hb
  filter_upwards [eventually_ge_atTop (need j)] with D hD
  exact ⟨ha,(le_max_left ..).trans hb,(le_max_right ..).trans hb,hD⟩

private theorem batch_dominates_input (ρ : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    n ≤ CRTBudget.batchClock ρ (addressBits n) (CRTBudget.volume n) :=
  (CRTBudget.input_le_volume hn).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

private theorem clock_le {ρ : ℝ} (tick : Guess → ℕ → ℕ) (p : Guess) (c n : ℕ) (hn : 2 ≤ n)
    (ht : tick p n ≤ c * max n (CRTBudget.batchClock ρ (addressBits n) (CRTBudget.volume n))) :
    clock tick p n ≤ (c+2)*CRTBudget.routeClock ρ 0 n := by
  let B := CRTBudget.batchClock ρ (addressBits n) (CRTBudget.volume n)
  let J := CRTBudget.batches (addressBits n)
  let T := CRTBudget.stageClock ρ 0 n
  have big : n ≤ B := batch_dominates_input ρ hn
  change tick p n ≤ c * max n B at ht
  rw [max_eq_right big] at ht
  have stage : J*B+B ≤ T := by
    change J*B+B ≤ (J+1)*(B+(addressBits n+1)^0)
    rw [pow_zero,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega
  have inside : J*tick p n+n+n ≤ (c+2)*(T+n) := by
    calc
      _ ≤ J*(c*B) + B+B := by gcongr
      _ ≤ (c+2)*(J*B+B) := by
        have h : 0 ≤ c*B+2*(J*B) := Nat.zero_le _
        nlinarith only [h]
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  calc
    _ ≤ count n*((c+2)*(T+n)) + (c+2)*n := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ inside) (Nat.le_mul_of_pos_left _ (by omega))
    _ = _ := by unfold CRTBudget.routeClock; dsimp only [T]; ring

/-- A comparison only on eventually accepted input sizes gives both of the
profile fields expected by the selector. Constants may depend on the tuple. -/
theorem bounds_of_profile {tick arena : Guess → ℕ → ℕ} (j : ℕ) (p : Guess)
    (good : ProfileAt tick arena j p) :
    LinearArena (peak arena p) ∧ RouteBound (Generator.targetExponent j) (clock tick p) := by
  obtain ⟨a,c,h⟩ := good
  constructor
  · refine ⟨a+2,?_⟩
    filter_upwards [h] with n bound
    unfold peak
    rw [Nat.add_mul]
    omega
  · have hρ : 0 ≤ Generator.midExponent j := by unfold Generator.midExponent; positivity
    have gap : Generator.midExponent j < Generator.targetExponent j := by
      unfold Generator.midExponent Generator.targetExponent
      gcongr
      linarith [Nat.cast_nonneg (α:=ℝ) j]
    obtain ⟨K,hK,rate⟩ := CRTBudget.routeClock_asymptotic hρ gap 0
    refine ⟨(c+2)*K,by positivity,?_⟩
    filter_upwards [h,rate,eventually_ge_atTop (2:ℕ)] with n bound hr hn
    have hc : (clock tick p n : ℝ) ≤ ((c:ℝ)+2)*(CRTBudget.routeClock (Generator.midExponent j) 0 n : ℝ) := by
      exact_mod_cast clock_le tick p c n hn bound.2
    calc
      _ ≤ ((c:ℝ)+2)*(K*n*logScale n^Generator.targetExponent j) :=
        hc.trans (mul_le_mul_of_nonneg_left hr (by positivity))
      _ = _ := by ring

/-- Joint acceptability across the reserve enumeration, allowing arbitrary
constant-factor comparisons on the eventual accepted input widths. -/
theorem good_of_profileAt (tick arena : Guess → ℕ → ℕ) (need : ℕ → ℕ) (inv : Bool)
    (profile : ∀ p, Enough need p → ProfileAt tick arena (exponent p) p) (j : ℕ) :
    EventuallyReserves j (fun p => LinearArena (peak arena p) ∧ GoodClock (.crt inv) j (clock tick p)) := by
  filter_upwards [eventually_enough need j] with a ha
  filter_upwards [ha] with b hb
  filter_upwards [hb] with D hd
  exact bounds_of_profile j (j,a,b,D) (profile _ hd)

/-- Apply the good-width equalities of the compiled kernel. The cutoff may
depend on the complete reserve tuple and need not be executable. -/
theorem good_of_profile (tick arena : Guess → ℕ → ℕ) (need : ℕ → ℕ) (cut : Guess → ℕ) (inv : Bool)
    (profile : ∀ p, Enough need p → ∀ n ≥ cut p, arena p n = n ∧
      tick p n = max n (CRTBudget.batchClock (Generator.midExponent (exponent p)) (addressBits n) (CRTBudget.volume n)))
    (j : ℕ) :
    EventuallyReserves j (fun p => LinearArena (peak arena p) ∧ GoodClock (.crt inv) j (clock tick p)) := by
  apply good_of_profileAt tick arena need inv _ j
  intro p hp
  refine ⟨1,1,?_⟩
  filter_upwards [eventually_ge_atTop (cut p)] with n hn
  obtain ⟨hs,ht⟩ := profile p hp n hn
  simp [hs,ht]

/-- Assemble one direction directly at the selector's source and profile
types from the joint physical command and its reserve-conditional estimates. -/
def procedure (degree : ℕ) (inv : Bool) (tick arena : Guess → ℕ → ℕ)
    (run : SourceRun degree (.crt inv) (peak arena) (clock tick)) (need : ℕ → ℕ) (cut : Guess → ℕ)
    (profile : ∀ p, Enough need p → ∀ n ≥ cut p, arena p n = n ∧
      tick p n = max n (CRTBudget.batchClock (Generator.midExponent (exponent p)) (addressBits n) (CRTBudget.volume n))) :
    Procedure degree (.crt inv) :=
  ⟨peak arena,clock tick,run,good_of_profile tick arena need cut inv profile⟩

end FixedCandidate.CRTStream.Joint

end NearSquareRoot
end Computability
end OAI
