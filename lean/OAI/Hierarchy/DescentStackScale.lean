import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI
/-! # Choosing the real stack width and age for one finite compiler menu -/

namespace Hierarchy.DescentCompiler
open Filter
open scoped Classical

/-- The common physical cable unit after j applications. Each earlier
grain is an exact b-fold multiple of its successor. -/
def stageGrain (b power last j : ℕ) := power*b^(last-j)

theorem grain_step {b p last j : ℕ} (inRange : j<last) :
    stageGrain b p last j=stageGrain b p last (j+1)*b := by
  unfold stageGrain
  rw [Nat.mul_assoc,←pow_succ]
  congr 2
  omega

theorem grain_positive {b p last j : ℕ} (hb : 0<b) (hp : 0<p) :
    0<stageGrain b p last j := Nat.mul_pos hp (Nat.pow_pos hb)

/-- The actual integer p gives genuine full-width rows. Its initial width
p₀ is chosen before the row payload is wired and is divisible at every round. -/
theorem packing_width {h U q : ℕ} (hU : 0<U) (hq : 0<q) (large : 32*(q*U)≤h) :
    let p := h/(16*(q*U))
    let p₀ := p*U
    0<p ∧ 0<p₀ ∧ 16*(q*p₀)≤h ∧ h≤32*(q*p₀) := by
  let d := 16*(q*U)
  let p := h/d
  have hd : 0<d := by dsimp [d];positivity
  have two : 2*d≤h := by dsimp [d];omega
  have positive : 0<p := Nat.div_pos (by omega) hd
  have low := Nat.div_mul_le_self h d
  have high : h<p*d+d := by
    have decomposition := Nat.mod_add_div h d
    have m := Nat.mod_lt h hd
    dsimp [p]
    nlinarith only [decomposition,m]
  have spent : d≤p*d := by simpa using Nat.mul_le_mul_right d (show 1≤p from positive)
  refine ⟨positive,Nat.mul_pos positive hU,?_,?_⟩
  · change 16*(q*(p*U))≤h
    simpa only [p,d,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using low
  · change h≤32*(q*(p*U))
    calc
      h ≤ 2*(p*d) := by omega
      _ = _ := by dsimp [d]; ring

/-- Any fixed number of powers of T fits below h simultaneously with
the ROM constraints by choosing the integer logarithmic age denominator. -/
theorem age_room (B : ℕ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop, let J := Nat.log 2 h/(2*B);
      0<J ∧ 32*(2^J)^B≤h := by
  filter_upwards [eventually_ge_atTop (2^(2*B+10))] with h large
  have nz : h≠0 := ((Nat.two_pow_pos _).trans_le large).ne'
  have exponent : 2*B+10≤Nat.log 2 h :=
    (Nat.le_log_iff_pow_le (by decide) nz).mpr large
  let J := Nat.log 2 h/(2*B)
  have used : J*(2*B)≤Nat.log 2 h := Nat.div_mul_le_self _ _
  have pos : 0<J := Nat.div_pos (by omega) (by omega)
  have bitlen : 5+J*B≤Nat.log 2 h := by nlinarith only [used,exponent,Nat.zero_le B]
  refine ⟨pos,?_⟩
  change 2^5*(2^J)^B≤h
  rw [←pow_mul,←pow_add]
  exact (Nat.le_log_iff_pow_le (by decide) nz).mp bitlen

/-- Integer age rounding costs one factor of two in the final power saving. -/
theorem age_saving (h B : ℕ) (hh : 0<h) (hB : 0<B) :
    (h:ℝ)^(1/(B:ℝ)) ≤ 2*(2:ℝ)^(Nat.log 2 h/B) := by
  let J := Nat.log 2 h/B
  have upper := Nat.lt_pow_succ_log_self (by decide : 1<2) h
  have rem := Nat.mod_lt (Nat.log 2 h) hB
  have div := Nat.mod_add_div (Nat.log 2 h) B
  have steps : Nat.log 2 h+1≤(J+1)*B := by dsimp [J];nlinarith only [div,rem]
  have nh : h≤(2^(J+1))^B := by
    rw [←pow_mul]
    exact upper.le.trans (Nat.pow_le_pow_right (by decide) steps)
  have real : (h:ℝ)≤((2:ℝ)^(J+1))^B := by exact_mod_cast nh
  calc
    _ ≤ (((2:ℝ)^(J+1))^B)^(1/(B:ℝ)) := Real.rpow_le_rpow (by positivity) real (by positivity)
    _ = (2:ℝ)^(J+1) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity),
        show (B:ℝ)*(1/(B:ℝ))=1 by field_simp,Real.rpow_one]
    _ = _ := by rw [pow_succ]; ring

end Hierarchy.DescentCompiler

end OAI
