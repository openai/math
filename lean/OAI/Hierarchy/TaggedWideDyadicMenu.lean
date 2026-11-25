import OAI.Hierarchy.TaggedDyadicBanks
import OAI.Hierarchy.ProbeStageWidthRatio
import OAI.Hierarchy.TaggedWideMenu
import OAI.Hierarchy.TaggedMenuFit

namespace OAI
/-! # An address-induction menu from the protocol supergroup geometry -/

namespace Hierarchy.Tagged
open Filter Real Set Finset TaggedShorterBudget
open scoped Topology BigOperators
noncomputable section

/-- Numbering the distinct scale/width pairs and recording the actual dyadic
supergroup addresses before the fixed batch offset is subtracted. -/
structure DyadicGeometry (κ A : ℝ) (N : ℕ) where
  index : Fin N ↪ ℕ×ℕ
  positive : ∀ j,0<(index j).1
  supergroup : ℕ×ℕ → WideParent κ A → ℕ
  offset : ℕ×ℕ → ℕ
  scale : ∀ j,Tendsto (fun x=>(supergroup (index j) x:ℝ)/x.h)
    (WideParent.large κ A) (𝓝 (dyadic (index j).1))

variable {κ A : ℝ} {N : ℕ}

/-- The concrete nine-digit protocol supplies its own supergroup geometry.
Fixed role multiplicities and the chosen batch fractions enter as address
offsets independent of the current parent width. -/
def DyadicGeometry.of_stages (index : Fin N ↪ ℕ×ℕ) (positive : ∀ j,0<(index j).1)
    (pad offset : ℕ×ℕ→ℕ) : DyadicGeometry κ A N :=
  ⟨index,positive,(fun i x=>ProbeStage.superAddress i.1 (pad i) x.h),offset,
    (fun j=>ProbeStage.superAddress_ratio (index j).1 (pad (index j)) WideParent.h tendsto_comap)⟩

private theorem parent_high : Tendsto (fun x : WideParent κ A=>(x.h:ℝ)) (WideParent.large κ A) atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_comap

/-- Physical height, ceiling width and twice the actual number of purchased
modules per type, in the enumeration used by WideLayout. -/
def DyadicGeometry.menu (g : DyadicGeometry κ A N) (u : ℝ→ℝ) (δ ξ : ℝ) : WideMenu κ A := by
  let ht := fun i (x : WideParent κ A) => g.supergroup i x-g.offset i
  let wp := fun (i : ℕ×ℕ) (x : WideParent κ A) => ⌈dyadic (i.2 : ℕ)*x.w⌉₊
  have wlarge : Tendsto (fun x : WideParent κ A=>(x.w:ℝ)) (WideParent.large κ A) atTop :=
    tendsto_atTop_mono' _ (Eventually.of_forall fun x => Nat.cast_le.mpr x.property.1.2.1) parent_high
  have lim (j : Fin N) := bank_limits (dyadic_pos _) (dyadic_pos (g.index j).2).le
    WideParent.h WideParent.w (g.supergroup (g.index j)) (g.offset (g.index j))
    parent_high wlarge (g.scale j)
  exact ⟨N,(fun j=>ht (g.index j)),(fun j=>wp (g.index j)),
    (fun j x=>bankCopies (typeFraction u δ ξ (logb x.h x.w) (g.index j)) x.h (ht (g.index j) x)),
    (fun j=>dyadic (g.index j).1),(fun j=>dyadic (g.index j).2),
    (fun j=>⟨dyadic_pos _,dyadic_le_half (g.positive j),dyadic_pos _⟩),
    (fun j=>(lim j).1),(fun j=>(lim j).2.1),(fun j=>(lim j).2.2)⟩

/-- The menu constructed from the supergroups satisfies the two numerical
fields of a WideLayout with fraction 36ξ and exponent two. -/
theorem DyadicGeometry.paid (g : DyadicGeometry κ A N) {u : ℝ→ℝ} {s ε p q Q σ L δ η ξ : ℝ}
    (hu : TaggedWidthProfile.Admissible s u) (hk : 0≤κ)
    (h : Choice u A (ε/2) p q Q σ L δ η ξ) :
    let m := g.menu u δ ξ
    ∀ᶠ x in WideParent.large κ A,
      (∀ j,0<m.payload j x ∧ 0<m.copies j x ∧
        36*ξ*(2:ℝ)^x.h≤(m.copies j x:ℝ)*2^(m.height j x) ∧
        logb 2 (m.copies j x)≤(m.height j x:ℝ)^(2:ℝ)) ∧
      ∑ j,slotFraction x.h (m.height j x) (m.copies j x)*
        (m.T j^(u (logb x.h x.w)-(logb x.h x.w)*deriv u (logb x.h x.w))*
         m.Y j^(1+deriv u (logb x.h x.w)))≤ε := by
  classical
  intro m
  let menu := Finset.univ.map g.index
  let ht (j : ℕ×ℕ) (x : WideParent κ A) := g.supergroup j x-g.offset j
  let a (x : WideParent κ A) := logb x.h x.w
  have fmt (x : WideParent κ A) : a x ∈ Icc 1 A :=
    ⟨(show (1:ℝ)≤1+κ by linarith).trans x.formats.2.2.1,x.formats.2.2.2⟩
  have small (j : Fin N) := eventually_bank_small (m.ratios j).1 (m.ratios j).2.1
    (show 0<3*ξ by linarith [h.xi_pos]) WideParent.h (m.height j) parent_high (m.heightRatio j)
  have logged (j : Fin N) : ∀ᶠ x in WideParent.large κ A,
      0<m.copies j x ∧ logb 2 (m.copies j x)≤(m.height j x:ℝ)^(2:ℝ) := by
    obtain ⟨U,hU,top⟩ := typeFraction_bounded hu A δ ξ (g.index j)
    exact eventually_bank_log (m.ratios j).1 hU WideParent.h (m.height j)
      (fun x=>typeFraction u δ ξ (a x) (g.index j)) parent_high (m.heightRatio j)
      (Eventually.of_forall fun x=>⟨fraction_pos h.xi_pos _ _ _ _,top _ (fmt x)⟩)
  filter_upwards [Filter.eventually_all.mpr small,Filter.eventually_all.mpr logged] with x size logSize
  have scale : ∀ i∈menu,((2^ht i x:ℕ):ℝ)≤3*ξ*(2:ℝ)^x.h := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    exact size j
  obtain ⟨lower,weighted⟩ := h.bank_menu (fmt x) x.h menu (fun i=>ht i x) scale
  constructor
  · intro j
    have pay : 0<dyadic (g.index j).2*(x.w:ℝ) := mul_pos (dyadic_pos _) (Nat.cast_pos.mpr x.formats.2.1)
    exact ⟨Nat.ceil_pos.mpr pay,(logSize j).1,lower _ (Finset.mem_map.mpr ⟨j,mem_univ _,rfl⟩),(logSize j).2⟩
  · change ∑ j : Fin N,
      ((bankCopies (typeFraction u δ ξ (a x) (g.index j)) x.h (ht (g.index j) x):ℝ)*
        2^(ht (g.index j) x)/(2:ℝ)^x.h)*
      (dyadic (g.index j).1^(u (a x)-a x*deriv u (a x))*
       dyadic (g.index j).2^(1+deriv u (a x))) ≤ ε
    simpa only [menu,Finset.sum_map] using weighted

end
end Hierarchy.Tagged

end OAI
