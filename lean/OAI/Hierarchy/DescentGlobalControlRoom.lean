import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Paying the shared reset solver and its once-per-reset lookup tables -/
namespace Hierarchy.DescentCompiler
open Filter

private theorem polynomial_below_binary (C d : ℕ) :
    ∀ᶠ x : ℕ in atTop, C*x^d ≤ 2^x := by
  have lim := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) d
    (by norm_num : (1:ℝ)<2)).const_mul_left (C:ℝ)
  filter_upwards [lim.def zero_lt_one] with x bound
  have h : (C:ℝ)*(x:ℝ)^d ≤ (2:ℝ)^x := by
    simpa [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (C:ℝ)*(x:ℝ)^d by positivity),
      abs_of_nonneg (show 0 ≤ (2:ℝ)^x by positivity)] using bound
  exact_mod_cast h

/-- Every fixed power of the number of dyadic stages is eventually smaller
than any fixed positive fraction of the physical word. -/
theorem dyadic_log_room (K d : ℕ) :
    ∀ᶠ h : ℕ in atTop, K*(Nat.log 2 h+1)^d ≤ h := by
  obtain ⟨n,event⟩:=eventually_atTop.mp (polynomial_below_binary (K*2^d) d)
  filter_upwards [eventually_ge_atTop (2^(n+1))] with h high
  let L:=Nat.log 2 h
  have enough : n+1 ≤ L := Nat.le_log_of_pow_le (by decide) high
  have nz : h≠0 := by have pos:=Nat.two_pow_pos (n+1);omega
  have shift : L+1 ≤ 2*L := by omega
  calc
    _ ≤ K*(2*L)^d := Nat.mul_le_mul_left K (Nat.pow_le_pow_left shift d)
    _ = (K*2^d)*L^d := by rw [mul_pow,Nat.mul_assoc]
    _ ≤ 2^L := event L (by omega)
    _ ≤ h := Nat.pow_log_le_self _ nz

/-- The height, number of resets and exponent of the solver table may vary.
All coefficients and degrees precede the height cutoff. -/
theorem global_control_quarter (C b K s : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ J u : ℕ, J ≤ Nat.log 2 h → u ≤ K*(J+1)^s →
      C*(h+1)^b*2^u ≤ 2^(h/4) := by
  filter_upwards [dyadic_log_room (4*(C+b+K)) (s+1)] with h room
  intro J u stages exponent
  let L:=Nat.log 2 h
  let P:=(L+1)^(s+1)
  have Ppos : 0<P := Nat.pow_pos (Nat.succ_pos L)
  have lin : L+1 ≤ P := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L) (show 1≤s+1 by omega)
  have powcap : (J+1)^s ≤ P := (Nat.pow_le_pow_left (Nat.succ_le_succ stages) s).trans
    (Nat.pow_le_pow_right (Nat.succ_pos L) (Nat.le_succ s))
  have cap : C+(L+1)*b+u ≤ (C+b+K)*P := by
    have one := Nat.le_mul_of_pos_right C Ppos
    have two := Nat.mul_le_mul_right b lin
    have three := exponent.trans (Nat.mul_le_mul_left K powcap)
    calc
      _ ≤ C*P+(P*b)+K*P := Nat.add_le_add (Nat.add_le_add one two) three
      _ = _ := by ring
  have address : C+(L+1)*b+u ≤ h/4 := by
    have four := Nat.mul_le_mul_left 4 cap
    change (4*(C+b+K))*P ≤ h at room
    rw [Nat.mul_assoc] at room
    omega
  have hw : h+1 ≤ 2^(L+1) := Nat.lt_pow_succ_log_self (by decide) h
  have hc : C ≤ 2^C := (Nat.lt_pow_self (n:=C) (a:=2) (by decide)).le
  calc
    _ ≤ 2^C*(2^(L+1))^b*2^u := Nat.mul_le_mul_right _ (Nat.mul_le_mul hc (Nat.pow_le_pow_left hw b))
    _ = 2^(C+(L+1)*b+u) := by simp only [pow_add,pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) address

/-- A shared half-word lookup ROM, its polynomial-in-height wiring and all
solver tables fit the requested fraction of the smallest genuine ambient matrix.
An arbitrary fixed multiplier is absorbed in C. -/
theorem global_control_shared (C b K s f : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ J u M : ℕ, J ≤ Nat.log 2 h → u ≤ K*(J+1)^s → 2^h ≤ M →
      (C*(h+1)^b*2^u)*2^(h/2) ≤ M/(2^J)^f := by
  filter_upwards [global_control_quarter C (b+f) K s,eventually_ge_atTop 1] with h charged hpos
  intro J u M stages exponent ambient
  have T : 2^J ≤ h+1 := (Nat.pow_le_pow_right (by decide : 0<2) stages).trans
    ((Nat.pow_log_le_self 2 (by omega : h≠0)).trans (Nat.le_succ h))
  apply (Nat.le_div_iff_mul_le (Nat.pow_pos (Nat.two_pow_pos J))).mpr
  calc
    _ ≤ ((C*(h+1)^b*2^u)*2^(h/2))*(h+1)^f :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left T f)
    _ = (C*(h+1)^(b+f)*2^u)*2^(h/2) := by rw [pow_add];ring
    _ ≤ 2^(h/4)*2^(h/2) := Nat.mul_le_mul_right _ (charged J u stages exponent)
    _ ≤ M := by rw [←pow_add];exact (Nat.pow_le_pow_right (by decide) (show h/4+h/2 ≤ h by omega)).trans ambient

/-- A matrix index of m² bits at m ≤ K(J+1)², including the selected Nielsen
control table, satisfies the previous shared bound uniformly. -/
theorem global_control_matrix (C b K f : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ J m M : ℕ, J ≤ Nat.log 2 h → m ≤ K*(J+1)^2 → 2^h ≤ M →
      (C*(h+1)^b*2^(m*m))*2^(h/2) ≤ M/(2^J)^f := by
  filter_upwards [global_control_shared C b (K*K) 4 f] with h good
  intro J m M stages dim amb
  apply good J (m*m) M stages _ amb
  calc
    m*m ≤ (K*(J+1)^2)*(K*(J+1)^2) := Nat.mul_le_mul dim dim
    _ = (K*K)*(J+1)^4 := by ring

end Hierarchy.DescentCompiler

end OAI
