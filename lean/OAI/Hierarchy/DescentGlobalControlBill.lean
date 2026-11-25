import OAI.Hierarchy.DescentGlobalClockEnvelope
import OAI.Hierarchy.DescentGlobalControlRoom
import OAI.Hierarchy.DescentGLPhysicalTrajectory
import OAI.Hierarchy.DescentGLControlCode

namespace OAI
/-! # Charging the physical GL search and its selected Nielsen control ROM -/
namespace Hierarchy.DescentCompiler
open Filter

theorem global_solver_clock (m base : ℕ) (bank : ℕ→ℕ) :
    DescentGL.PhysicalTrajectory.time m base bank m+DescentGLPermutationRAM.clock m ≤
      4000*2^(5*m) := by
  exact (DescentGL.PhysicalTrajectory.total_clock m base bank).trans (global_clock_envelope m)

/-- Both charges include a polynomial word-level implementation overhead, and
the result leaves an arbitrary fixed power of the stack width unspent. -/
theorem global_reset_controller (C b K f : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ J m M base : ℕ, ∀ bank : ℕ→ℕ,
      J ≤ Nat.log 2 h → m ≤ K*(J+1)^2 → 2^h ≤ M →
      C*(h+1)^b*(DescentGL.PhysicalTrajectory.time m base bank m+DescentGLPermutationRAM.clock m) ≤ M/(2^J)^f ∧
      C*(h+1)^b*(DescentGLControlCode.Count m*2^(m*m)) ≤ M/(2^J)^f := by
  filter_upwards [global_control_shared (C*4000) b (5*K) 2 f,
    dyadic_log_room (2*(K*K)) 4,global_control_shared C (b+1) 0 0 f] with h solver range table
  intro J m M base bank stages dim large
  have power : 5*m ≤ (5*K)*(J+1)^2 := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 5 dim
  have solve:=solver J (5*m) M stages power large
  have compute:=Nat.mul_le_mul_left (C*(h+1)^b) (global_solver_clock m base bank)
  constructor
  · apply compute.trans
    calc
      _ = (C*4000)*(h+1)^b*2^(5*m) := by ring
      _ ≤ _ := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (h/2))).trans solve
  · have norm : m*m ≤ (K*K)*(Nat.log 2 h+1)^4 := calc
      _ ≤ (K*(J+1)^2)*(K*(J+1)^2) := Nat.mul_le_mul dim dim
      _ = (K*K)*(J+1)^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ stages) _)
    have wide : 2*(m*m)≤h := (Nat.mul_le_mul_left 2 norm).trans (by simpa only [Nat.mul_assoc] using range)
    have fit : m*m≤h/2 := by omega
    have raw:=DescentGLControlCode.table_price m h fit
    have header : 2*m*m≤h+1 := by rw [Nat.mul_assoc];omega
    have bill:=table J 0 M stages (by simp) large
    simp only [pow_zero,Nat.mul_one] at bill
    apply (Nat.mul_le_mul_left (C*(h+1)^b) raw).trans
    calc
      _ ≤ (C*(h+1)^b)*((h+1)*2^(h/2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ header)
      _ = (C*(h+1)^(b+1))*2^(h/2) := by rw [pow_succ];ring
      _ ≤ _ := bill

/-- The actual search clock and actual table occupy one joint budget. Independent
slabs S and a positive packed input width p may be reinstated with the same rate. -/
theorem global_reset_total (C b K f : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ J m M base S p : ℕ, ∀ bank : ℕ→ℕ,
      J ≤ Nat.log 2 h → m ≤ K*(J+1)^2 → 2^h ≤ M → 0<p →
      let ticks:=DescentGL.PhysicalTrajectory.time m base bank m+DescentGLPermutationRAM.clock m
      let rom:=DescentGLControlCode.Count m*2^(m*m)
      S*(C*(h+1)^b*(ticks+rom)) ≤ (M*S*p)/(2^J)^f := by
  filter_upwards [global_reset_controller (2*C) b K f] with h budget
  intro J m M base S p bank stages dim ambient positive ticks rom
  obtain ⟨search,control⟩:=budget J m M base bank stages dim ambient
  change (2*C)*(h+1)^b*ticks ≤ M/(2^J)^f at search
  change (2*C)*(h+1)^b*rom ≤ M/(2^J)^f at control
  have joint : C*(h+1)^b*(ticks+rom) ≤ M/(2^J)^f := by nlinarith only [search,control]
  have den : 0<(2^J)^f := Nat.pow_pos (Nat.two_pow_pos J)
  have bill:=(Nat.le_div_iff_mul_le den).mp joint
  apply (Nat.le_div_iff_mul_le den).mpr
  calc
    _ = S*((C*(h+1)^b*(ticks+rom))*(2^J)^f) := Nat.mul_assoc ..
    _ ≤ S*M := Nat.mul_le_mul_left S bill
    _ ≤ M*S*p := by rw [Nat.mul_comm S M];exact Nat.le_mul_of_pos_right _ positive

/-- Charge the word width and the original T,log₂ R parameters separately.
Here T=2^J and log₂ R=τ(J+1) as in the terminal calibration. -/
theorem global_reset_mixed (C A b τ e K f : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ J W m M base S p : ℕ, ∀ bank : ℕ→ℕ,
      J ≤ Nat.log 2 h → W ≤ A*h → m ≤ K*(J+1)^2 → 2^h ≤ M → 0<p →
      let ticks:=DescentGL.PhysicalTrajectory.time m base bank m+DescentGLPermutationRAM.clock m
      let rom:=DescentGLControlCode.Count m*2^(m*m)
      S*((C*(W+1)^b*(2^J+τ*(J+1)+1)^e)*(ticks+rom)) ≤ (M*S*p)/(2^J)^f := by
  let D:=C*(A+1)^b*(τ+2)^e
  filter_upwards [global_reset_total D (b+e) K f,eventually_ge_atTop 1] with h budget hpos
  intro J W m M base S p bank stages words dim ambient pos ticks rom
  have age : J≤h := stages.trans (Nat.log_lt_self 2 (by omega : h≠0)).le
  have scale : 2^J≤h := (Nat.pow_le_pow_right (by decide : 0<2) stages).trans (Nat.pow_log_le_self 2 (by omega))
  have word : W+1≤(A+1)*(h+1) := calc
    _ ≤ A*(h+1)+(h+1) := Nat.add_le_add (words.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))) (by omega)
    _ = _ := by ring
  have tail : 2^J+τ*(J+1)+1 ≤ (τ+2)*(h+1) := calc
    _ ≤ (h+1)+τ*(h+1)+(h+1) := Nat.add_le_add (Nat.add_le_add (scale.trans (Nat.le_succ _))
      (Nat.mul_le_mul_left _ (Nat.succ_le_succ age))) (by omega)
    _ = _ := by ring
  have factor : C*(W+1)^b*(2^J+τ*(J+1)+1)^e≤D*(h+1)^(b+e) := calc
    _≤C*((A+1)*(h+1))^b*((τ+2)*(h+1))^e := Nat.mul_le_mul
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left word b)) (Nat.pow_le_pow_left tail e)
    _=_ := by dsimp only [D];rw [mul_pow,mul_pow,pow_add];ring
  apply (Nat.mul_le_mul_left S (Nat.mul_le_mul_right (ticks+rom) factor)).trans
  exact budget J m M base S p bank stages dim ambient pos

end Hierarchy.DescentCompiler

end OAI
