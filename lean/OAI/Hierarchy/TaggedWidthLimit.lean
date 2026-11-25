import OAI.Hierarchy.TaggedWidthClosure
import OAI.Hierarchy.TaggedRadixPrice
import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # The limiting overhead of shorter calls and stable radix packing -/

noncomputable section
namespace Hierarchy.Tagged

open Filter Catalyst

variable {F : Type*} [Field F] {k : ℕ}

/-- A stable radix construction, expressed on individual realizable rates. -/
def RadixBound (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ {a B x y : ℝ}, 1 < a → 1 < B → 0 ≤ x → 0 ≤ y →
    Feasible F k a x → Feasible F k B y → Feasible F k 1 (1-1/a+max (x/a) y)

/-- The simultaneous physical reduction needs to cover only finite intervals
of widths and sufficiently large address heights. Each recursive use mentions
only actually installed, strictly shorter address formats. -/
def WidthReductions (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ u : ℝ → ℝ, TaggedWidthProfile.Admissible (profile F k 1) u → ∀ a : ℝ, 1 ≤ a →
    ∃ A C : ℝ, a+1 ≤ A ∧ 0<C ∧ ∀ᶠ h : ℕ in atTop, ∀ w, inRange A h w →
      Bounded F k h w u 1 C ∨ ∃ r : ShorterCalls F k h w A C, FitsWork u r

theorem profile_zero_of_reductions (radix : RadixBound F k) (reduce : WidthReductions F k) :
    profile F k 1 = 0 := by
  let r := profile F k
  have rge (a : ℝ) : 0 ≤ r a := profile_nonneg (Exact.rates_nonempty F k a)
  apply TaggedWidthProfile.squeeze r (sInf (r '' Set.Ici 1)) (rge 1)
  · intro a ha
    exact csInf_le ⟨0,fun _ ⟨b,_,e⟩ => e ▸ rge b⟩ (Set.mem_image_of_mem r ha)
  · intro a ha
    apply Radix.packing_infimum r ha
    intro B hB e he
    have hx : 0≤r a+e := by linarith [rge a]
    have hy : 0≤r B+e := by linarith [rge B]
    have input (t : ℝ) : Feasible F k t (r t+e) :=
      feasible_of_profile_lt (Exact.rates_nonempty F k t) (lt_add_of_pos_right _ he)
    have build := radix ha hB hx hy (input a) (input B)
    have a1 : 0≤1-1/a := sub_nonneg.mpr ((div_le_one (zero_lt_one.trans ha)).mpr ha.le)
    exact profile_le (add_nonneg a1 (hy.trans (le_max_right _ _))) build
  · intro u hu a ha
    obtain ⟨A,C,haA,hC,steps⟩ := reduce u hu a ha
    exact profile_le (hu.positive a ha).le (feasible_of_reductions hu ha haA hC steps)

theorem feasible_at_one_of_reductions (radix : RadixBound F k) (reduce : WidthReductions F k)
    {r : ℝ} (hr : 0<r) : Feasible F k 1 r :=
  feasible_of_profile_lt (Exact.rates_nonempty F k 1)
    ((profile_zero_of_reductions radix reduce).trans_lt hr)

/-- The square-root estimate can use the same witnesses as the sharper
log-squared estimate at every sufficiently large integer height. -/
theorem cheap_of_reductions (radix : RadixBound F k) (reduce : WidthReductions F k)
    {r : ℝ} (hr : 0<r) :
    ∃ A C : ℝ, 0<A ∧ 0<C ∧ ∀ᶠ h : ℕ in atTop,
      ∃ X : Approximation F k (pins h h), (X.size:ℝ) ≤ A*work h h r ∧
        X.Gap (coeff F h h) (gap C h) ∧
        X.Gap (coeff F h h) ((2:ℝ)^h*(2:ℝ)^(-Real.sqrt h)) := by
  have z := profile_zero_of_reductions radix reduce
  obtain ⟨A,C,hA,hC,ok⟩ := cheap_of_profile_zero (Exact.rates_nonempty F k 1) z r hr
  refine ⟨A,C,hA,hC,?_⟩
  filter_upwards [ok,GapScale.eventual_sqrt_gap C (zero_lt_one : (0:ℝ)<1)] with h witness cheap
  obtain ⟨X,sz,g⟩ := witness
  exact ⟨X,sz,g,Approximation.Gap.mono _ g (by simpa using cheap)⟩


end Hierarchy.Tagged

end
end OAI
