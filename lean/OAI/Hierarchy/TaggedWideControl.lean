import OAI.Hierarchy.TaggedWideControlHeight
import OAI.Hierarchy.TaggedWidthInduction

namespace OAI
/-! # Width-one control prices over all wide integer parent formats -/

noncomputable section
namespace Hierarchy.Tagged
open Filter Real
open scoped BigOperators
/-- The uniform filter ranges over every integer payload allowed at a height. -/
abbrev WideParent (κ A : ℝ) := {x : ℕ × ℕ // inRange A x.1 x.2 ∧ 1+κ ≤ logb x.1 x.2}

namespace WideParent

def h {κ A : ℝ} (x : WideParent κ A) := x.val.1
def w {κ A : ℝ} (x : WideParent κ A) := x.val.2
def large (κ A : ℝ) : Filter (WideParent κ A) := comap h atTop

theorem formats {κ A : ℝ} (x : WideParent κ A) :
    1 < (x.h:ℝ) ∧ 0 < x.w ∧ logb x.h x.w ∈ Set.Icc (1+κ) A := by
  obtain ⟨⟨two,hw,wp⟩,lo⟩ := x.property
  have hh : 1 < (x.h:ℝ) := by exact_mod_cast (show 1<x.val.1 by omega)
  have ww : 0 < x.w := by change 0<x.val.2; omega
  exact ⟨hh,ww,lo,(logb_le_iff_le_rpow hh (Nat.cast_pos.mpr ww)).mpr wp⟩

end WideParent

theorem control_padding {h rows : ℕ} {R : ℝ} (hh : 0<h) (one : 1 ≤ R)
    (small : R ≤ (2:ℝ)^h) (count : (rows:ℝ) ≤ (2:ℝ)^h*R) :
    h ≤ controlHeight h rows ∧ rows ≤ 2^controlHeight h rows ∧ controlHeight h rows ≤ 2*h ∧
      (2:ℝ)^controlHeight h rows ≤ 2*(2:ℝ)^h*R := by
  let m := max (2^h) rows
  let t := Nat.clog 2 m
  have hm : (m:ℝ) ≤ (2:ℝ)^h*R := by
    dsimp [m]
    push_cast
    exact max_le (le_mul_of_one_le_right (by positivity) one) count
  have high : 1 < m := (Nat.one_lt_two_pow hh.ne').trans_le (le_max_left ..)
  have pos : 1 ≤ t := Nat.clog_pos (by decide) high
  have up : m ≤ 2^t := Nat.le_pow_clog (by decide) m
  have room : (m:ℝ) ≤ (2:ℝ)^(2*h) := by
    refine hm.trans ?_
    rw [two_mul,pow_add]
    exact mul_le_mul_of_nonneg_left small (by positivity)
  have top : t ≤ 2*h := Nat.clog_le_of_le_pow (by exact_mod_cast room)
  have lower := Nat.clog_mono_right 2 (le_max_left (2^h) rows)
  rw [Nat.clog_pow 2 h (by decide)] at lower
  have doubled : 2^t ≤ 2*m := calc
    2^t = 2^(t-1)*2 := by rw [←pow_succ,Nat.sub_add_cancel pos]
    _ ≤ m*2 := Nat.mul_le_mul_right 2 (Nat.pow_pred_clog_lt_self (by decide) high).le
    _ = 2*m := Nat.mul_comm ..
  refine ⟨lower,(le_max_right ..).trans up,top,?_⟩
  calc
    (2:ℝ)^t ≤ 2*(m:ℝ) := by exact_mod_cast doubled
    _ ≤ 2*((2:ℝ)^h*R) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

/-- A control can be padded to any larger power of two. Its price follows
from its actual row count and address length. A fixed number of such controls
therefore has the ordinary polylogarithmic bill used by the wide menu. -/
theorem control_work {n h : ℕ} (t : Fin n → ℕ) {r L D power : ℝ}
    (hr : 0 ≤ r) (hL : 0 ≤ L) (hD : 0 ≤ D) (hh : 1 < (h:ℝ))
    (rows : ∀ i,(2:ℝ)^(t i) ≤ L*((2:ℝ)^h*(log (h:ℝ))^power))
    (addresses : ∀ i,(t i:ℝ) ≤ D*(h:ℝ)) :
    (∑ i, work (t i) (t i) r) ≤
      ((n:ℝ)*L*D^(1+r))*((2:ℝ)^h*(h:ℝ)^(1+r)*(log (h:ℝ))^power) := by
  have per (i : Fin n) : work (t i) (t i) r ≤
      (L*D^(1+r))*((2:ℝ)^h*(h:ℝ)^(1+r)*(log (h:ℝ))^power) := by
    have toPow (v : ℕ) : (v:ℝ)*(v:ℝ)^r = (v:ℝ)^(1+r) := by
      rw [add_comm,Real.rpow_add_one' (Nat.cast_nonneg v) (by linarith : r+1 ≠ 0)]
      ring
    calc
      work (t i) (t i) r = (2:ℝ)^(t i)*(t i:ℝ)^(1+r) := by
        rw [work,mul_assoc,toPow]
      _ ≤ (L*((2:ℝ)^h*(log (h:ℝ))^power))*(D*h)^(1+r) := by
        apply mul_le_mul (rows i) (Real.rpow_le_rpow (Nat.cast_nonneg _) (addresses i) (by linarith))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        exact mul_nonneg hL (mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_pos hh).le _))
      _ = _ := by rw [Real.mul_rpow hD (Nat.cast_nonneg _)]; ring
  calc
    _ ≤ ∑ _i : Fin n, (L*D^(1+r))*((2:ℝ)^h*(h:ℝ)^(1+r)*(log (h:ℝ))^power) :=
      Finset.sum_le_sum fun i _ => per i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring


end Hierarchy.Tagged

end
end OAI
