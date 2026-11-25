import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.TaggedData
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI
/-! # The exposed width profile of physical tagged approximations -/

noncomputable section
namespace Hierarchy.Tagged

open Filter

def width (h : ℕ) (a : ℝ) : ℕ := ⌈(h : ℝ)^a⌉₊

@[simp] theorem width_one (h : ℕ) : width h 1 = h := by
  simp [width]

def gap (C : ℝ) (h : ℕ) : ℝ :=
  (2:ℝ)^h * (2:ℝ)^(-C * (Real.logb 2 (2*(h:ℝ)))^2)

def work (h w : ℕ) (r : ℝ) : ℝ := (2:ℝ)^h * w * (h:ℝ)^r

def Feasible (F : Type*) [Field F] (k : ℕ) (a r : ℝ) : Prop :=
  ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ᶠ h : ℕ in atTop,
    ∃ X : Catalyst.Approximation F k (pins h (width h a)),
      (X.size : ℝ) ≤ A * work h (width h a) r ∧ X.Gap (coeff F h (width h a)) (gap C h)

theorem Feasible.mono {F : Type*} [Field F] {k : ℕ} {a r t : ℝ}
    (f : Feasible F k a r) (hrt : r ≤ t) : Feasible F k a t := by
  obtain ⟨A,C,hA,hC,ok⟩ := f
  refine ⟨A,C,hA,hC,?_⟩
  filter_upwards [ok, eventually_ge_atTop (1 : ℕ)] with h hh hpos
  obtain ⟨X,hs,hg⟩ := hh
  refine ⟨X,hs.trans ?_,hg⟩
  have hp : (h:ℝ)^r ≤ (h:ℝ)^t :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) hrt
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) hA.le

def rates (F : Type*) [Field F] (k : ℕ) (a : ℝ) : Set ℝ :=
  {r | 0 ≤ r ∧ Feasible F k a r}

def profile (F : Type*) [Field F] (k : ℕ) (a : ℝ) : ℝ := sInf (rates F k a)

theorem profile_nonneg {F : Type*} [Field F] {k : ℕ} {a : ℝ}
    (h : (rates F k a).Nonempty) : 0 ≤ profile F k a :=
  le_csInf h (fun _ hr => hr.1)

theorem profile_le {F : Type*} [Field F] {k : ℕ} {a r : ℝ}
    (hr : 0 ≤ r) (hf : Feasible F k a r) : profile F k a ≤ r :=
  csInf_le ⟨0,fun _ he => he.1⟩ ⟨hr,hf⟩

theorem feasible_of_profile_lt {F : Type*} [Field F] {k : ℕ} {a r : ℝ}
    (h : (rates F k a).Nonempty) (hr : profile F k a < r) : Feasible F k a r := by
  obtain ⟨t,ht,htr⟩ := exists_lt_of_csInf_lt h hr
  exact ht.2.mono htr.le

/-- At width equal to the address length, rate zero gives actual exposed
trivalent networks for every positive overhead, with their original catalysts. -/
theorem cheap_of_profile_zero {F : Type*} [Field F] {k : ℕ}
    (nonempty : (rates F k 1).Nonempty) (zero : profile F k 1 = 0) (r : ℝ) (hr : 0 < r) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ᶠ h : ℕ in atTop,
      ∃ X : Catalyst.Approximation F k (pins h h),
        (X.size : ℝ) ≤ A * work h h r ∧ X.Gap (coeff F h h) (gap C h) := by
  obtain ⟨A,C,hA,hC,ok⟩ := feasible_of_profile_lt nonempty (zero ▸ hr)
  refine ⟨A,C,hA,hC,?_⟩
  filter_upwards [ok] with h hh
  let atWidth (w : ℕ) := ∃ X : Catalyst.Approximation F k (pins h w),
    (X.size:ℝ) ≤ A * work h w r ∧ X.Gap (coeff F h w) (gap C h)
  exact Eq.mp (congrArg atWidth (width_one h)) hh

end Hierarchy.Tagged

end
end OAI
