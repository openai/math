import OAI.Hierarchy.TaggedWidthInduction
import OAI.Hierarchy.TaggedExactFeasible
import OAI.Hierarchy.TaggedExact

namespace OAI
/-! # Finite exact seeds and closure of the exposed width recurrence -/

noncomputable section
namespace Hierarchy.Tagged

open Catalyst Filter Real

private theorem exact_seed {F : Type*} [Field F] {k h w cutoff : ℕ}
    {A C s : ℝ} {u : ℝ → ℝ} (hu : TaggedWidthProfile.Admissible s u)
    (hw : inRange A h w) (low : h ≤ cutoff) :
    Bounded F k h w u (25000*((cutoff:ℝ)+1)^2) C := by
  let X := Exact.atOrigin k (Exact.network F h w)
  have hh := hw.1
  have large := hw.2.1
  refine ⟨X,?_,?_⟩
  · have fit : w+h+1 ≤ 3*w := by omega
    have bill := Exact.network_size F h w
    have hc := Nat.pow_le_pow_left (Nat.succ_le_succ low) 2
    have bc := Nat.mul_le_mul (Nat.mul_le_mul_right (2^h) (Nat.mul_le_mul_left 8192 fit)) hc
    have data : pins h w ≤ 3*(2^h*w) := calc
      _ = 2^h*(2*w+h) := by unfold pins; ring
      _ ≤ 2^h*(3*w) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
    have cost : X.size ≤ 25000*(cutoff+1)^2*(2^h*w) := by
      dsimp only [X]
      rw [Exact.size_atOrigin]
      have slack := Nat.mul_le_mul_right (2^h*w) (show 1≤(cutoff+1)^2 from Nat.one_le_pow 2 _ (Nat.succ_pos cutoff))
      nlinarith only [bill,bc,data,slack]
    have hH : (1:ℝ)<h := by exact_mod_cast (show 1<h by omega)
    have base : 1≤Real.logb h w := by
      apply (Real.le_logb_iff_rpow_le hH (by exact_mod_cast (show 0<w by omega))).mpr
      simpa only [Real.rpow_one] using (show (h:ℝ)≤w by exact_mod_cast large)
    have scale := Real.one_le_rpow hH.le (hu.positive _ base).le
    calc
      (X.size:ℝ) ≤ 25000*((cutoff:ℝ)+1)^2*((2:ℝ)^h*w) := by exact_mod_cast cost
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        change (2:ℝ)^h*w ≤ ((2:ℝ)^h*w)*(h:ℝ)^_
        exact le_mul_of_one_le_right (by positivity) scale) (by positivity)
  · have exact_ := Exact.gap_atOrigin k (Exact.network F h w) (gap C h)
    simpa only [show (Exact.network F h w).eval=coeff F h w from funext (Exact.network_eval F h w)]
      using exact_

theorem Bounded.enlarge {F : Type*} [Field F] {k h w : ℕ} {u : ℝ → ℝ} {B B' C : ℝ}
    (hX : Bounded F k h w u B C) (le : B ≤ B') : Bounded F k h w u B' C := by
  obtain ⟨X,hs,hg⟩ := hX
  refine ⟨X,hs.trans (mul_le_mul_of_nonneg_right le ?_),hg⟩
  unfold unitWork work
  positivity

/-- Only the sufficiently large integer formats need physical shorter calls.
All finite exceptions are covered by the actual bitonic verifier. -/
theorem feasible_of_reductions {F : Type*} [Field F] {k : ℕ} {s A C a : ℝ} {u : ℝ→ℝ}
    (hu : TaggedWidthProfile.Admissible s u) (ha : 1 ≤ a) (haA : a+1 ≤ A) (hC : 0<C)
    (step : ∀ᶠ h : ℕ in atTop, ∀ w, inRange A h w →
      Bounded F k h w u 1 C ∨ ∃ r : ShorterCalls F k h w A C, FitsWork u r) :
    Feasible F k a (u a) := by
  obtain ⟨cut,after⟩ := eventually_atTop.1 step
  let B : ℝ := 25000*((cut:ℝ)+1)^2
  have B1 : 1 ≤ B := by
    have := sq_nonneg (cut:ℝ)
    dsimp [B]
    nlinarith [Nat.cast_nonneg (α:=ℝ) cut]
  apply feasible_of_uniform hu ha haA (zero_lt_one.trans_le B1) hC
  apply uniform_of_shorter B1
  intro h w range
  by_cases big : cut≤h
  · exact (after h big w range).imp (fun hx => hx.enlarge B1) id
  · exact Or.inl (exact_seed hu range (Nat.le_of_not_ge big))

end Hierarchy.Tagged

end
end OAI
