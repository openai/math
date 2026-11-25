import OAI.Hierarchy.TaggedWideMenuFractions
import OAI.Hierarchy.ProbeReportPool

namespace OAI
/-! # The actual common physical directory across all width types -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterBudget TaggedShorterSupergroups TaggedShorterPacking Real Filter Set
open scoped Classical BigOperators

/-- The actual nine-digit stage chart uses the same next-fit directory
for every code, parent width exponent and selector. The exact output
format of the certified dyadic menu is the one paid for by this purchase. -/
theorem purchased_menu {u : ℝ→ℝ} {s κ A ε p q Q σ L δ η ξ : ℝ}
    (profile : TaggedWidthProfile.Admissible s u) (price : Choice u A ε p q Q σ L δ η ξ)
    (W m k attempts ell : ℕ) (stage : 0<W) (wide : 0≤κ) :
    ∃ short : ℕ,∃ K U : ℝ, ∀ᶠ x in WideParent.large κ A,∀ i : Fin (m+1),
      let roles := copies k attempts
      let pad := 2*roles
      let dir := stageDir x.h W roles pad (show 2*roles≤2^pad from Nat.lt_two_pow_self.le)
      let g := superAddress W pad x.h
      let size : ℕ := 2^g*2^ell
      let menu := (typeMenu κ A W m k attempts ell stage (fun _=>short+ell)).menu u δ ξ
      let t := menu.height i x
      let c := typeFraction u δ ξ (logb x.h x.w) (W,i.val)
      let half : ℕ := 2^(t-1)
      let modules := ⌈6*c*(2:ℝ)^x.h/(2:ℝ)^t⌉₊
      t=g-short ∧ menu.payload i x=⌈dyadic i.val*x.w⌉₊ ∧ menu.copies i x=2*modules ∧
        0<half ∧ 2*half=2^t ∧ 0 < modules ∧ (dir.groups:ℝ)*(2*half)≤c*(2:ℝ)^x.h ∧
        ((max modules (dir.groups*batches size half):ℕ):ℝ)*size≤K*(2:ℝ)^x.h ∧
        (modules:ℝ)*(2*half)≤(7*U)*(2:ℝ)^x.h := by
  obtain ⟨U,uniform⟩ := menu_fractions profile price W m
  obtain ⟨short,K,pool⟩ := aligned_fixed W k attempts ell stage (U:=U) (c₀:=3*ξ) (by have := price.xi_pos;positivity)
  refine ⟨short,K,U,?_⟩
  filter_upwards [(tendsto_comap (f:=WideParent.h (κ:=κ) (A:=A))).eventually pool] with x ready i
  intro roles pad dir g size menu t c half modules
  have hx := x.formats.2.2
  have bounds := uniform (logb x.h x.w) ⟨by linarith [hx.1],hx.2⟩ i
  obtain ⟨height,hB,whole,hM,admitted,near,far⟩ := ready c bounds.1 bounds.2
  have ht : t=g-short := height
  refine ⟨ht,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [half,modules]
  all_goals rw [ht]
  all_goals assumption

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
