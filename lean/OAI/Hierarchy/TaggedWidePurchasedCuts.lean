import OAI.Hierarchy.TaggedWidePurchasedMenu
import OAI.Hierarchy.TaggedWideCutParts
import OAI.Hierarchy.TaggedWidePoolReady

namespace OAI
/-! # Purchasing both physical compactors for every code of the reported menu -/
noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterBudget TaggedShorterPacking TaggedShorterSupergroups
open ThreeFlat Routing Spill TaggedShorterCompaction TaggedShorterNetwork Real Filter
open scoped Classical Topology BigOperators

/-- One pair of sparse compactors is purchased before any wires are attached.
The cell bill includes every candidate, every idle module, and both calls per
module. The candidate length is computed on the expanded public directory. -/
theorem purchased_cuts (F : Type*) [Field F] {u : ℝ→ℝ} {s κ A ε p q Q σ Λ δ η ξ : ℝ}
    (profile : TaggedWidthProfile.Admissible s u) (price : Choice u A ε p q Q σ Λ δ η ξ)
    (W m k attempts ell : ℕ) (hW : 0<W) (hk : 0≤κ) :
    ∃ short : ℕ,∃ C : ℝ,∀ᶠ x in WideParent.large κ A,∀ i : Fin (m+1),
      let roles := copies k attempts
      let pad := 2*roles
      let dir := stageDir x.h W roles pad (show 2*roles≤2^pad from Nat.lt_two_pow_self.le)
      let menu := (typeMenu κ A W m k attempts ell hW (fun _=>short+ell)).menu u δ ξ
      let t := menu.height i x
      let width := menu.payload i x
      let D : ℕ := 2^(superAddress W pad x.h)*2^ell
      let B : ℕ := 2^(t-1)
      let c := typeFraction u δ ξ (logb x.h x.w) (W,i.val)
      let M := ⌈6*c*(2:ℝ)^x.h/(2:ℝ)^t⌉₊
      let S := max M (dir.groups*batches D B)
      menu.copies i x=2*M ∧ 0<B ∧ 2*B=2^t ∧ (dir.groups:ℝ)*(2*B)≤c*(2:ℝ)^x.h ∧
      ∃ (near : Compactor F D (2^t) (t+width)) (far : Compactor F S M (Width (2^t) (t+width))),
      ∀ {V : Type} (read : Input S D (t+width)→V),
        ((CutFormat.mk S D M t width near far read).cost:ℝ)≤C*((2:ℝ)^x.h*x.w) := by
  obtain ⟨short,K,U,pool⟩ := purchased_menu profile price W m k attempts ell hW hk
  obtain ⟨cutoff,b,make⟩ := TaggedShorterCost.exists_boards_raw F
  let pad := 2*copies k attempts
  let child := fun h=>superAddress W pad h-short
  let H : Tendsto (fun h : ℕ=>(h:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have scale := superAddress_ratio W pad id tendsto_id
  have ht := (bank_limits (dyadic_pos W) zero_le_one id id (superAddress W pad) short H H scale).2.1
  have minPrice := show 0<3*ξ by linarith [price.xi_pos]
  have ready := eventually_pool_ready cutoff K minPrice (dyadic_pos W) (dyadic_le_half hW) child ht
  have low := eventually_bank_small (dyadic_pos W) (dyadic_le_half hW) (c:=1) zero_lt_one id
    (superAddress W (pad+ell)) H (superAddress_ratio W (pad+ell) id tendsto_id)
  let G := 4*(5*(b:ℝ)*max K 0+177000*max (7*U) 0)
  refine ⟨short,10*G+1,?_⟩
  filter_upwards [pool,tendsto_comap.eventually (ready.and low)] with x paid sizes
  intro i roles padding dir menu t width D B c M S
  obtain ⟨height,payload,copiesEq,halfPos,whole,hm,admitted,candidates,modules⟩ := paid i
  have localHeight : t=child x.h := height
  have pc : 3*ξ≤c := by
    obtain ⟨_,_,slope,_,paid',_,_,_,_⟩ := price.exponents (logb x.h x.w)
      ⟨by linarith [x.formats.2.2.1],x.formats.2.2.2⟩
    exact fraction_lower price.xi_pos.le paid'
      (show 0 ≤ 1-(-deriv u (logb x.h x.w))-δ by linarith) W i.val
  have posD : 0<D := by positivity
  have ceiling : D≤2^x.h := by
    have address : superAddress W (pad+ell) x.h=superAddress W pad x.h+ell := by unfold superAddress; omega
    have bound := sizes.2
    rw [address,pow_add] at bound
    exact_mod_cast (show (D:ℝ)≤(2:ℝ)^x.h by simpa [D,pad,roles,padding] using bound)
  have enough : 2^t≤D := by
    have := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.sub_le (superAddress W pad x.h) short)
    rw [localHeight]
    exact this.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos ell))
  have parameters := sizes.1 c S D pc posD ceiling candidates
  rw [←localHeight] at parameters
  obtain ⟨hth,hnear,hfar,logS,logD⟩ := parameters
  obtain ⟨near,far,bill⟩ := make S D M t t width (2*x.h) enough hnear hm (le_max_left ..) hfar logS logD
  refine ⟨copiesEq,halfPos,whole,admitted,near,far,?_⟩
  intro V read
  let cut := CutFormat.mk S D M t width near far read
  have hc : cut.cost ≤ 4*TaggedShorterCost.cost S D M (2^t) b (2*x.h+t+t+width+5)+1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 4 bill) 1
  have hw : width≤x.w := by
    change width=⌈dyadic i.val*(x.w:ℝ)⌉₊ at payload
    rw [payload]
    exact Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg _) (dyadic_le_one _))
  have parent := show x.h≤x.w from x.property.1.2.1
  have wp := x.formats.2.1
  let scalarCut := CutFormat.mk S D M t width near far (fun _=>())
  have cost := scalarCut.cost_of_volumes b (2*x.h) (N:=(2:ℝ)^x.h) (P:=max K 0) (Q:=max (7*U) 0)
    (T:=10*(x.w:ℝ)) (by positivity) (le_max_right ..) (le_max_right ..) hc
    (candidates.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)))
    (by
      have volume : (M:ℝ)*(2:ℝ)^t≤(7*U)*(2:ℝ)^x.h := by
        have same : (2:ℝ)^t=2*(B:ℝ) := by exact_mod_cast whole.symm
        simpa only [same] using modules
      exact volume.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)))
    (by exact_mod_cast (show 2*x.h+t+t+width+5≤10*x.w by omega))
  have npos := one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n:=x.h)
  have w1 : (1:ℝ)≤x.w := by exact_mod_cast wp
  have unit : (1:ℝ)≤(2:ℝ)^x.h*x.w := le_mul_of_one_le_right (by positivity) w1 |>.trans' npos
  change (cut.cost:ℝ)≤(10*G+1)*((2:ℝ)^x.h*x.w)
  change (cut.cost:ℝ)≤G*(2:ℝ)^x.h*(10*x.w)+1 at cost
  linarith only [cost,unit]

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
