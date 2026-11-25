import OAI.Hierarchy.TaggedApproximation
import OAI.Hierarchy.TaggedWidthProfile

namespace OAI
/-! # Strong induction on the address length of physical tagged networks -/

noncomputable section
namespace Hierarchy.Tagged

open Filter
open scoped BigOperators

def unitWork (u : ℝ → ℝ) (h w : ℕ) : ℝ := work h w (u (Real.logb h w))
def inRange (A : ℝ) (h w : ℕ) : Prop := 2 ≤ h ∧ h ≤ w ∧ (w:ℝ) ≤ (h:ℝ)^A

/-- An address-reducing construction on actual table networks. Each index
accounts for all installed copies of one child format or slice. The fixed work
includes local tables, padding, and current-height control calls. -/
structure ShorterCalls (F : Type*) [Field F] (k h w : ℕ) (A C : ℝ) where
  types : ℕ
  height : Fin types → ℕ
  payload : Fin types → ℕ
  smaller : ∀ i, height i < h
  within : ∀ i, inRange A (height i) (payload i)
  multiplicity : Fin types → ℕ
  fixedWork : ℝ
  assemble : (∀ i, Catalyst.Approximation F k (pins (height i) (payload i))) →
    Catalyst.Approximation F k (pins h w)
  size_le : ∀ inputs, ((assemble inputs).size : ℝ) ≤ fixedWork +
    ∑ i, (multiplicity i : ℝ)*((inputs i).size:ℝ)
  gap_le : ∀ inputs, (∀ i, (inputs i).Gap (coeff F (height i) (payload i)) (gap C (height i))) →
    (assemble inputs).Gap (coeff F h w) (gap C h)

def FitsWork {F : Type*} [Field F] {k h w : ℕ} {A C : ℝ}
    (u : ℝ → ℝ) (r : ShorterCalls F k h w A C) : Prop :=
  r.fixedWork ≤ unitWork u h w/2 ∧
    (∑ i, (r.multiplicity i : ℝ)*unitWork u (r.height i) (r.payload i)) ≤ unitWork u h w/2

theorem ShorterCalls.size_of_budget {F : Type*} [Field F] {k h w : ℕ} {A C : ℝ}
    {u : ℝ → ℝ} (r : ShorterCalls F k h w A C) (budget : FitsWork u r)
    {B : ℝ} (hB : 1 ≤ B) (inputs : ∀ i, Catalyst.Approximation F k (pins (r.height i) (r.payload i)))
    (hs : ∀ i, ((inputs i).size : ℝ) ≤ B * unitWork u (r.height i) (r.payload i)) :
    ((r.assemble inputs).size : ℝ) ≤ B * unitWork u h w := by
  have hnon : 0 ≤ unitWork u h w := by unfold unitWork work; positivity
  have weighted : (∑ i, (r.multiplicity i : ℝ)*((inputs i).size:ℝ)) ≤
      B*∑ i, (r.multiplicity i : ℝ)*unitWork u (r.height i) (r.payload i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc _ ≤ (r.multiplicity i:ℝ)*(B*unitWork u (r.height i) (r.payload i)) :=
           mul_le_mul_of_nonneg_left (hs i) (Nat.cast_nonneg _)
         _ = _ := by ring
  apply (r.size_le inputs).trans
  have hmajor := mul_le_mul_of_nonneg_left budget.2 (zero_le_one.trans hB)
  have scale := mul_le_mul_of_nonneg_right hB (show 0 ≤ unitWork u h w/2 by linarith)
  linarith [budget.1]

def Bounded (F : Type*) [Field F] (k h w : ℕ) (u : ℝ → ℝ) (B C : ℝ) : Prop :=
  ∃ X : Catalyst.Approximation F k (pins h w),
    (X.size : ℝ) ≤ B*unitWork u h w ∧ X.Gap (coeff F h w) (gap C h)

/-- A parent's independent size bound follows from genuinely smaller address
lengths. The left alternative handles integer seeds and payload slicing near
the address width. -/
theorem uniform_of_shorter {F : Type*} [Field F] {k : ℕ} {A B C : ℝ} {u : ℝ → ℝ}
    (hB : 1 ≤ B)
    (cover : ∀ h w, inRange A h w → Bounded F k h w u B C ∨
      ∃ r : ShorterCalls F k h w A C, FitsWork u r) :
    ∀ h w, inRange A h w → Bounded F k h w u B C := by
  classical
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro w hw
    obtain direct | ⟨r,budget⟩ := cover h w hw
    · exact direct
    have children (i : Fin r.types) := ih (r.height i) (r.smaller i) (r.payload i) (r.within i)
    choose child sizes gaps using children
    exact ⟨r.assemble child, r.size_of_budget budget hB child sizes, r.gap_le child gaps⟩

/-- Integer ceiling in the target width can only decrease the cost exponent
of an admissible majorant. Increasing the uniform interval by one absorbs
the ceiling for every height at least two. -/
theorem feasible_of_uniform {F : Type*} [Field F] {k : ℕ} {A B C a s : ℝ} {u : ℝ → ℝ}
    (hu : TaggedWidthProfile.Admissible s u) (ha : 1 ≤ a) (haA : a+1 ≤ A)
    (hB : 0 < B) (hC : 0 < C)
    (bound : ∀ h w, inRange A h w → Bounded F k h w u B C) :
    Feasible F k a (u a) := by
  refine ⟨B,C,hB,hC,?_⟩
  filter_upwards [eventually_ge_atTop (2:ℕ)] with h hh
  have htwo : (2:ℝ) ≤ h := by exact_mod_cast hh
  have hpos : (1:ℝ) < h := by linarith
  have hp : 1 ≤ (h:ℝ)^a := Real.one_le_rpow hpos.le (zero_le_one.trans ha)
  have hw : (h:ℝ)^a ≤ width h a := Nat.le_ceil _
  have hw₁ : (h:ℝ) ≤ width h a := (by
    simpa using Real.rpow_le_rpow_of_exponent_le hpos.le ha : (h:ℝ) ≤ (h:ℝ)^a).trans hw
  have hw₂ : ((width h a:ℕ):ℝ) ≤ (h:ℝ)^A := calc
    _ ≤ (h:ℝ)^a+1 := (Nat.ceil_lt_add_one (zero_le_one.trans hp)).le
    _ ≤ (h:ℝ)^a*(h:ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr htwo)]
    _ = (h:ℝ)^(a+1) := by rw [Real.rpow_add (zero_lt_one.trans hpos),Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hpos.le haA
  obtain ⟨X,hsize,hgap⟩ := bound h (width h a) ⟨hh,by exact_mod_cast hw₁,hw₂⟩
  refine ⟨X,hsize.trans ?_,hgap⟩
  have incl : a ≤ Real.logb h (width h a) :=
    (Real.le_logb_iff_rpow_le hpos (zero_lt_one.trans_le (hp.trans hw))).mpr hw
  have anti : AntitoneOn u (Set.Ici 1) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 1) hu.smooth.continuous.continuousOn
      (hu.smooth.differentiable (by simp)).differentiableOn fun x hx =>
        neg_nonneg.mp (hu.slope x (interior_subset hx)).1
  have hu' := anti ha (ha.trans incl) incl
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hpos.le hu') (by positivity)) hB.le

end Hierarchy.Tagged

end
end OAI
