import OAI.Hierarchy.TaggedWideBanks
import OAI.Hierarchy.TaggedWideFormats
import OAI.Hierarchy.TaggedShorterProfile
import OAI.Hierarchy.TaggedNarrowStrip
import OAI.Hierarchy.TaggedWidthLimit

namespace OAI
/-! # The wide and narrow cases of the tagged address induction -/

noncomputable section
namespace Hierarchy.Tagged

open Catalyst CatalystSubstitution Filter Real TaggedWidthProfile
open scoped Topology BigOperators

/-- The protocol's raw evidence contains the unfilled physical host, evaluated
only with ideal shorter targets, and its ordinary and width-one control bills.
All inductive and approximation estimates follow downstream. -/
structure WideLayout (F : Type*) [Field F] (k : ℕ) (u : ℝ → ℝ)
    (κ A r ε baseline : ℝ) extends WideMenu κ A where
  controls : ℕ
  controlHeight : WideParent κ A → Fin controls → ℕ
  fraction : ℝ
  exponent : ℝ
  ρ : ℝ
  ordinary : ℝ
  power : ℝ
  fraction_pos : 0 < fraction
  exponent_pos : 0 < exponent
  outer_pos : 0 < ρ
  ordinary_pos : 0 < ordinary
  allocation : ∀ᶠ x in WideParent.large κ A, ∀ i,
    0 < payload i x ∧ 0 < copies i x ∧
    fraction*(2:ℝ)^x.h ≤ (copies i x:ℝ)*2^(height i x) ∧
    logb 2 (copies i x) ≤ (height i x:ℝ)^exponent
  weighted : ∀ᶠ x in WideParent.large κ A, let a := logb x.h x.w;
    ∑ i, slotFraction x.h (height i x) (copies i x) *
      (T i^(u a-a*deriv u a) * Y i^(1+deriv u a)) ≤ ε
  taller : ∀ᶠ x in WideParent.large κ A, ∀ j,x.h ≤ controlHeight x j
  board : ∀ᶠ x in WideParent.large κ A,
    ∃ host : ∀ (Y : ∀ i,(toWideMenu.bank x i).Output F k)
      (Z : ∀ j,Approximation F k (pins (controlHeight x j) (controlHeight x j))),
      Host F k (pins x.h x.w) (Sockets (bankCalls (toWideMenu.bank x) Y (controlCalls (controlHeight x) Z))),
      ∀ Y Z,
        (hostSize (host Y Z):ℝ) + baseline * (∑ j,work (controlHeight x j) (controlHeight x j) r) ≤
          ordinary*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^power +
            (2:ℝ)^x.h*(x.h:ℝ)^(1+r)*(log (x.h:ℝ))^power) ∧
        (tableApprox (host Y Z).width (exactValue _ (host Y Z))).Gap (coeff F x.h x.w)
          (ρ*(2:ℝ)^x.h*x.w)

/-- Every physical layout of the indicated price yields the recursive alternative
of the address induction uniformly over its entire width interval. -/
theorem WideLayout.reductions {F : Type*} [Field F] {k K : ℕ}
    {s κ A r ε baseline C C₀ start : ℝ} {u : ℝ → ℝ} (L : WideLayout F k u κ A r ε baseline)
    (hu : Admissible s u) (hk : 0<κ) (hA : 1+κ ≤ A) (hs : 1 < start)
    (hc : start < A) (flat : ∀ a,start ≤ a → u a=u start)
    (make : SliceAmplifier F K) (tiny : (K:ℝ)*ε ≤ 1/4)
    (rlo : r < u 1) (Cpos : 6 ≤ C) (hC₀ : 0 < C₀) (room : C₀ < C)
    (base : ∀ᶠ t : ℕ in atTop, ∃ Z : Approximation F k (pins t t),
      (Z.size:ℝ) ≤ baseline*work t t r ∧ Z.Gap (coeff F t t) (gap C₀ t)) :
    ∀ᶠ x in WideParent.large κ A, ∃ calls : ShorterCalls F k x.h x.w A C, FitsWork u calls := by
  classical
  let l := WideParent.large κ A
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) l atTop := tendsto_comap
  have highR : Tendsto (fun x : WideParent κ A => (x.h:ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp high
  have formats := Eventually.of_forall (@WideParent.formats κ A) (f:=l)
  have hp := L.allocation
  have positive (i : Fin L.types) := hp.mono (fun _ all => (all i).1)
  obtain ⟨bound,parts⟩ := eventually_wide_formats hk (by linarith : 1<A)
    WideParent.h WideParent.w L.height L.payload L.T L.Y L.ratios L.tall L.heightRatio L.widthRatio formats
  have budget := eventually_menu_fit (hu.smooth.of_le (by simp)) hA
    (by linarith : 0 ≤ start) hc flat (Nat.cast_nonneg K) tiny
    WideParent.h WideParent.w L.height L.payload L.copies L.T L.Y
    (fun i => ⟨(L.ratios i).1,(L.ratios i).2.2⟩)
    L.tall L.heightRatio L.widthRatio formats positive L.weighted
  let fixed (x : WideParent κ A) := L.ordinary*((2:ℝ)^x.h*x.w*(log (x.h:ℝ))^L.power +
    (2:ℝ)^x.h*(x.h:ℝ)^(1+r)*(log (x.h:ℝ))^L.power)
  have smallerFormats := formats.mono (fun x fmt =>
    And.intro fmt.1 (And.intro fmt.2.1
      (Set.Icc_subset_Icc (by linarith : (1:ℝ) ≤ 1+κ) le_rfl fmt.2.2)))
  have ordinary := eventually_fixed_work hu rlo L.ordinary_pos WideParent.h WideParent.w fixed
    highR smallerFormats (Eventually.of_forall (fun _ => le_rfl))
  obtain ⟨h₀,t₀,build⟩ := make k Cpos L.fraction_pos L.exponent_pos
  have ages := eventually_all.mpr (fun i : Fin L.types =>
    (L.tall i).eventually_ge_atTop (max 2 (t₀:ℝ)))
  have cuts := high.eventually (GapScale.eventual_polynomial C
    (2*(k:ℝ)*((bound:ℝ)+L.types+L.controls)) 0 (by norm_num))
  have outer := high.eventually (GapScale.eventual_mass (by linarith : 0<C) L.outer_pos 2)
  have controlPrices := high.eventually (GapScale.eventual_taller_polynomial hC₀.le room
    (b:=0) le_rfl 2)
  have controlSizes := high.eventually (eventually_forall_ge_atTop.mpr base)
  filter_upwards [parts,budget,ordinary,ages,hp,L.taller,L.board,high.eventually_ge_atTop h₀,cuts,
    outer,controlPrices,controlSizes] with x split paid cheap ages allocated taller board hh loss out cg cs
  obtain ⟨host,book⟩ := board
  have widthOne (j : Fin L.controls) := cs (L.controlHeight x j) (taller j)
  choose Z sz sc using widthOne
  let B := L.toWideMenu.bank x
  let ctrl := controlCalls (L.controlHeight x) Z
  have loss₀ : 2*(k:ℝ)*((bound:ℝ)+L.types+L.controls) ≤ gap C x.h := by
    simpa only [Real.rpow_zero,mul_one] using loss
  refine shorterCalls_of_banks (K:=K) (fixed:=fixed x) u B ctrl ?_ ?_ ?_ (fun Y => host Y Z)
    ?_ ?_ ?_ ?_ cheap paid
  · intro i
    have sh := (split i).1
    have pos := x.property.1.1
    change L.height i x < x.val.1
    change 3*L.height i x ≤ 2*x.val.1 at sh
    omega
  · exact fun i => (split i).2.2
  · intro i
    obtain ⟨wp,copies,mass,logs⟩ := allocated i
    have age := ages i
    have ht : t₀ ≤ L.height i x := by exact_mod_cast (le_max_right _ _).trans age
    have baseOne : (1:ℝ) ≤ L.height i x := by linarith [((le_max_left _ _).trans age : (2:ℝ) ≤ _)]
    apply build x.h (B i) hh ht (split i).1 copies mass logs wp
    · exact Nat.floor_pos.mpr (Real.one_le_rpow baseOne (by linarith))
    · have cnt : ((B i).slices:ℝ) ≤ bound := by exact_mod_cast (split i).2.1
      have enlarged : ((B i).slices:ℝ) ≤ (bound:ℝ)+L.types+L.controls := by
        linarith only [cnt,Nat.cast_nonneg (α:=ℝ) L.types,Nat.cast_nonneg (α:=ℝ) L.controls]
      exact (mul_le_mul_of_nonneg_left enlarged (show 0≤2*(k:ℝ) by positivity)).trans loss₀
  · intro Y
    have sums := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => sz j)
    have eq : ((ctrl.map (·.replacement.size)).sum:ℝ) = ∑ j,((Z j).size:ℝ) := by
      simp [ctrl,controlCalls,List.map_ofFn,List.sum_ofFn,Function.comp_def]
    rw [eq]
    exact (add_le_add (le_refl (hostSize (host Y Z):ℝ)) (sums.trans_eq (Finset.mul_sum ..).symm)).trans (book Y Z).1
  · intro Y
    have width : (1:ℝ) ≤ x.w := by exact_mod_cast (WideParent.formats x).2.1
    have mass : 2*gap C x.h ≤ L.ρ*(2:ℝ)^x.h*x.w :=
      out.trans (le_mul_of_one_le_right (mul_nonneg L.outer_pos.le (by positivity)) width)
    exact Approximation.Gap.mono _ (book Y Z).2 mass
  · intro o mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    have rate : 2*gap C x.h ≤ gap C₀ (L.controlHeight x i) := by
      simpa only [Real.rpow_zero,mul_one] using cg _ (taller i)
    exact Approximation.Gap.mono _ (sc i) rate
  · simp only [ctrl,controlCalls,List.length_ofFn]
    have enlarged : (L.types:ℝ)+L.controls ≤ (bound:ℝ)+L.types+L.controls := by
      linarith only [Nat.cast_nonneg (α:=ℝ) bound]
    exact (mul_le_mul_of_nonneg_left enlarged (show 0≤2*(k:ℝ) by positivity)).trans loss₀

/-- Choose the width-one control rate and narrow strip, then choose the
protocol only after fixing the amplification tolerance. The sole protocol
interface is a native layout constructed using that protocol's physical
allocation. Its specification contains no recursive approximation bound. -/
theorem widthReductions_of_cofinal_layouts {F : Type*} [Field F] {k : ℕ}
    {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (protocols : ∀ A : ℝ,1<A → TaggedShorterBudget.Cofinal (P A))
    (emit : ∀ {u : ℝ → ℝ} {κ A r ε baseline p q Q σ L δ η ξ : ℝ},
      Admissible (profile F k 1) u → 0 < κ → 1+κ ≤ A → 0 ≤ r → r < u 1 → 0 < ε → 0 < baseline →
      P A p q Q σ L → TaggedShorterBudget.Choice u A (ε/2) p q Q σ L δ η ξ →
      Nonempty (WideLayout F k u κ A r ε baseline)) :
    WidthReductions F k := by
  classical
  obtain ⟨K,hK,amplify⟩ := ShorterBank.amplified_slices F
  let ε := 1/(4*(K:ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have tiny : (K:ℝ)*ε ≤ 1/4 := by
    apply le_of_eq
    dsimp [ε]
    field_simp [show (K:ℝ)≠0 from (Nat.cast_pos.mpr hK).ne']
  intro u hu a ha
  let r := (profile F k 1+u 1)/2
  have lower : profile F k 1 < r := by dsimp [r]; linarith [hu.initial]
  have margin : r < u 1 := by dsimp [r]; linarith [hu.initial]
  have base := feasible_of_profile_lt (Exact.rates_nonempty F k 1) lower
  obtain ⟨κ,Cn,hκ,hCn,narrow⟩ := bounded_narrow_strip hu base margin
  obtain ⟨D,C₀,hD,hC₀,control⟩ := base
  obtain ⟨start,hs,flat⟩ := hu.plateau
  let A := max (max (a+1) (1+κ)) (start+1)
  have requested : a+1 ≤ A := (le_max_left ..).trans (le_max_left ..)
  have hA : 1+κ ≤ A := (le_max_right ..).trans (le_max_left ..)
  have hc : start < A := lt_of_lt_of_le (by linarith : start < start+1) (le_max_right ..)
  let C := max 6 (max Cn C₀+1)
  have roomN : Cn < C := (lt_of_le_of_lt (le_max_left ..)
    (by linarith : max Cn C₀ < max Cn C₀+1)).trans_le (le_max_right ..)
  have roomC : C₀ < C := (lt_of_le_of_lt (le_max_right ..)
    (by linarith : max Cn C₀ < max Cn C₀+1)).trans_le (le_max_right ..)
  obtain ⟨δ,η,ξ,p,q,Q,σ,L,hP,purchase⟩ := TaggedShorterBudget.choose (A:=A) hu
    (half_pos hε) (protocols A (hs.trans hc))
  have rpos : 0 ≤ r := (profile_nonneg (Exact.rates_nonempty F k 1)).trans lower.le
  obtain ⟨layout⟩ := emit hu hκ hA rpos margin hε hD hP purchase
  have wide := layout.reductions hu hκ hA hs hc flat amplify tiny margin (le_max_left ..)
    hC₀ roomC (by
      filter_upwards [control] with t ht
      let atWidth (w : ℕ) := ∃ Z : Approximation F k (pins t w),
        (Z.size : ℝ) ≤ D * work t w r ∧ Z.Gap (coeff F t w) (gap C₀ t)
      exact Eq.mp (congrArg atWidth (width_one t)) ht)
  refine ⟨A,C,requested,hC₀.trans roomC,?_⟩
  filter_upwards [narrow C roomN,eventually_comap.mp wide] with h small big
  intro w bounds
  by_cases near : logb h w ≤ 1+κ
  · exact Or.inl (small w bounds.2.1 near)
  · exact Or.inr (big ⟨(h,w),bounds,(le_of_not_ge near)⟩ rfl)

end Hierarchy.Tagged

end
end OAI
