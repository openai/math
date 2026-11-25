import OAI.Hierarchy.TaggedWideMenuFractions
import OAI.Hierarchy.TaggedWidePortBill

namespace OAI
/-! # Exposed sockets of the two actual tagged modules at every dyadic type -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterBudget Real Filter Set
open scoped Classical Topology BigOperators

theorem purchased_pin_volumes {u : ℝ→ℝ} {s κ A ε p q Q σ L δ η ξ : ℝ}
    (profile : TaggedWidthProfile.Admissible s u) (price : Choice u A ε p q Q σ L δ η ξ)
    (W n k attempts ell short : ℕ) (hW : 0<W) (hk : 0≤κ) :
    let menu := (typeMenu κ A W n k attempts ell hW (fun _=>short+ell)).menu u δ ξ
    ∃ C : ℝ,0≤C ∧ ∀ᶠ x in WideParent.large κ A,∀i : Fin (n+1),
      (menu.copies i x:ℝ)*pins (menu.height i x) (menu.payload i x)≤C*((2:ℝ)^x.h*x.w) := by
  intro menu
  obtain ⟨U,upper⟩ := menu_fractions profile price W n
  let bound := max U 0
  have pos : 0<3*ξ := by linarith [price.xi_pos]
  let high : Tendsto (fun x : WideParent κ A=>(x.h:ℝ)) (WideParent.large κ A) atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_comap
  have small (i : Fin (n+1)) := eventually_bank_small (menu.ratios i).1 (menu.ratios i).2.1
    pos WideParent.h (menu.height i) high (menu.heightRatio i)
  have low (i : Fin (n+1)) := eventually_bank_small (menu.ratios i).1 (menu.ratios i).2.1
    (c:=1) zero_lt_one WideParent.h (menu.height i) high (menu.heightRatio i)
  refine ⟨42*bound,mul_nonneg (by norm_num) (le_max_right ..),?_⟩
  filter_upwards [eventually_all.mpr small,eventually_all.mpr low] with x tiny below i
  let t := menu.height i x
  let c := typeFraction u δ ξ (logb x.h x.w) (W,i.val)
  have hc : 3*ξ≤c ∧ c≤U := upper (logb x.h x.w) ⟨by linarith [x.formats.2.2.1],x.formats.2.2.2⟩ i
  have csmall : ((2^t:ℕ):ℝ)≤c*(2:ℝ)^x.h :=
    (tiny i).trans (mul_le_mul_of_nonneg_right hc.1 (by positivity))
  have slot := (installed_bounds (pos.le.trans hc.1) (show 0≤(2:ℝ)^x.h by positivity)
    (Nat.two_pow_pos t) csmall).2
  have maxPrice : c*(2:ℝ)^x.h≤bound*(2:ℝ)^x.h :=
    mul_le_mul_of_nonneg_right (hc.2.trans (le_max_left ..)) (by positivity)
  have copies : (menu.copies i x:ℝ)*(2:ℝ)^t≤(14*bound)*(2:ℝ)^x.h := by
    change (bankCopies c x.h t:ℝ)*(2:ℝ)^t≤_
    rw [bank_slots,Nat.cast_mul,Nat.cast_ofNat]
    linarith only [slot,maxPrice]
  have lev : (2:ℕ)^t≤2^x.h := by exact_mod_cast (show ((2^t:ℕ):ℝ)≤(2:ℝ)^x.h by simpa only [one_mul] using below i)
  have ht := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp lev
  have width : menu.payload i x≤x.w := by
    change ⌈dyadic i.val*x.w⌉₊≤x.w
    exact Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg _) (dyadic_le_one _))
  exact (bank_port_bill t _ _ x.w (ht.trans x.property.1.2.1) width copies).trans_eq (by ring)

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
