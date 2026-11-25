import OAI.Hierarchy.ProtocolRAMCoreCatalogueRowBudget
import OAI.Hierarchy.TaggedWidePoolPrice
import OAI.Hierarchy.TaggedShorterStageDirectory
import OAI.Hierarchy.TaggedDyadicBanks

namespace OAI
/-! # Paid next-fit candidate arrays on the actual nine-digit probe template -/

noncomputable section
namespace Hierarchy.TaggedShorterSupergroups
open ProbeStage

end Hierarchy.TaggedShorterSupergroups

namespace Hierarchy.Tagged
open ProbeStage TaggedShorterSupergroups TaggedShorterPacking TaggedShorterBudget Filter
open scoped Classical Topology BigOperators

set_option maxHeartbeats 500000 in
/-- Choose the fixed dyadic shortening from the actual reserved stage volume.
The same choice pays the directory's slack and all idle near and far modules
for every permitted price of this type at every sufficiently large height. -/
theorem purchase_stage_pool_fixed (W roles pad : ℕ) (hW : 0<W) (padding : 2*roles≤2^pad)
    {c₀ U : ℝ} (hc₀ : 0<c₀) :
    ∃ offset : ℕ, ∃ K : ℝ, ∀ᶠ h : ℕ in atTop, ∀ c : ℝ, c₀≤c → c≤U →
      let g := superAddress W pad h
      let t := g-offset
      let D : ℕ := 2^g
      let B : ℕ := 2^(t-1)
      let M := ⌈6*c*(2:ℝ)^h/(2:ℝ)^t⌉₊
      let dir := stageDir h W roles pad padding
      0<B ∧ 2*B=2^t ∧ 0<M ∧
        (dir.groups:ℝ)*(2*B)≤c*(2:ℝ)^h ∧
        ((max M (dir.groups*batches D B):ℕ):ℝ)*D≤K*(2:ℝ)^h ∧
        (M:ℝ)*(2*B)≤(7*U)*(2:ℝ)^h := by
  let C := (2*rounds (2^W)+1)*4^(rounds (2^W)+1)*roles
  obtain ⟨d,fixPad⟩ := choose_fraction (C:=(C:ℝ)) (Nat.cast_nonneg _) hc₀
  let J := (2:ℝ)^d
  let K := max 1 ((4*(C:ℝ)+2)/(3*c₀))*J*(7*U)
  refine ⟨d,K,?_⟩
  have high : Tendsto (fun i : ℕ=>(i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ratio := superAddress_ratio W pad id tendsto_id
  have grows := high.num (dyadic_pos W) ratio
  have small := eventually_bank_small (dyadic_pos W) (dyadic_le_half hW) hc₀
    id (superAddress W pad) high ratio
  have bounded := eventually_bank_small (dyadic_pos W) (dyadic_le_half hW) (c:=1) zero_lt_one
    id (superAddress W pad) high ratio
  filter_upwards [grows.eventually_gt_atTop (d:ℝ),small,bounded] with h late small bounded
  intro c lo hi g t D B M dir
  have hd : d<g := by exact_mod_cast late
  have ht : 0<t := Nat.sub_pos_of_lt hd
  have hb : 0<B := pow_pos (by decide) _
  have whole : 2*B=2^t := by
    have hts : t=t-1+1 := by omega
    calc 2*B = 2^(t-1+1) := by simp [B,pow_succ,Nat.mul_comm]
         _ = 2^t := congrArg (2^·) hts.symm
  have dcap : D≤2^h := by
    have bound : (D:ℝ)≤(2:ℝ)^h := by simpa only [one_mul,id_eq] using bounded
    exact_mod_cast bound
  have stageBound : (bits : ℕ) → bits≤D → (bits:ℝ)≤c*(2:ℝ)^h := by
    intro bits b
    exact (Nat.cast_le.mpr b).trans (small.trans
      (mul_le_mul_of_nonneg_right lo (by positivity)))
  have child : 2^t ≤ D := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have part : B≤D := by omega
  have scale : (((2^t:ℕ):ℝ)) = (D:ℝ)*(1/2:ℝ)^d := by
    simpa only [t,D,Nat.cast_pow,Nat.cast_ofNat] using shorter_address d g hd.le
  have cover : (D:ℝ)=J*(2*(B:ℝ)) := by
    change ((2^g:ℕ):ℝ)=(2:ℝ)^d*(2*(B:ℝ))
    have orig : (2:ℕ)^g = (2:ℕ)^d*(2*B) := by
      rw [whole,←pow_add]
      congr 1
      dsimp [t]
      omega
    exact_mod_cast orig
  have mEq : M=⌈6*c*((2^h:ℕ):ℝ)/(2*(B:ℝ))⌉₊ := by
    have hk : (2:ℝ)^t=2*(B:ℝ) := by exact_mod_cast whole.symm
    simp [M,hk]
  have cp : 0<c := hc₀.trans_le lo
  have pm : 0<M := by
    dsimp [M]
    apply Nat.ceil_pos.mpr
    positivity
  have dirCap := (purchase_stages h W roles pad padding).choose_spec
  have count : dir.groups*D≤2*(C*2^h)+D := dirCap.trans_eq (by
    change 2*((((2*rounds (2^W)+1)*4^(rounds (2^W)+1))*2^h)*roles)+D=2*(C*2^h)+D
    dsimp only [C]
    rw [Nat.mul_right_comm ((2*rounds (2^W)+1)*4^(rounds (2^W)+1)) (2^h) roles])
  have sites : ((C*2^h:ℕ):ℝ) ≤ (C:ℝ)*((2^h:ℕ):ℝ) := by push_cast; rfl
  have free := fixPad dir.groups D (2^t) (C*2^h) (2^h) count sites dcap scale.le
  have padBound : (dir.groups:ℝ)*(2*B)≤c*(2:ℝ)^h := by
    have lower : (dir.groups:ℝ)*((2^t:ℕ):ℝ)≤c₀*(2:ℝ)^h := by simpa using free
    have convert : ((2^t:ℕ):ℝ)=2*(B:ℝ) := by exact_mod_cast whole.symm
    rw [convert] at lower
    exact lower.trans (mul_le_mul_of_nonneg_right lo (by positivity))
  have bankSmall : 2*(B:ℝ)≤c*((2^h:ℕ):ℝ) := by
    have nd := stageBound (2^t) child
    simpa only [←whole,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using nd
  have bill := pool_volume dir.groups D B (C*2^h) (2^h) hb part dcap (Nat.cast_nonneg C) hc₀
    lo hi (show 0≤J by positivity) count sites cover.le bankSmall
  refine ⟨hb,whole,pm,padBound,?_,?_⟩
  · simpa only [mEq,K,Nat.cast_pow,Nat.cast_ofNat] using bill.2
  · simpa only [mEq,Nat.cast_pow,Nat.cast_ofNat] using bill.1

theorem purchase_stage_pool (W roles pad : ℕ) (hW : 0<W) (padding : 2*roles≤2^pad)
    {c₀ U : ℝ} (hc₀ : 0<c₀) :
    ∃ offset : ℕ, ∃ K : ℝ, ∀ᶠ h : ℕ in atTop, ∀ c : ℝ, c₀≤c → c≤U →
      let g := superAddress W pad h
      let t := g-offset
      let D : ℕ := 2^g
      let B : ℕ := 2^(t-1)
      let M := ⌈6*c*(2:ℝ)^h/(2:ℝ)^t⌉₊
      ∃ dir : Directory (reserved h W roles) D,
        0<B ∧ 2*B=2^t ∧ 0<M ∧
        (dir.groups:ℝ)*(2*B)≤c*(2:ℝ)^h ∧
        ((max M (dir.groups*batches D B):ℕ):ℝ)*D≤K*(2:ℝ)^h ∧
        (M:ℝ)*(2*B)≤(7*U)*(2:ℝ)^h := by
  obtain ⟨short,K,paid⟩ := purchase_stage_pool_fixed W roles pad hW padding hc₀ (U:=U)
  refine ⟨short,K,?_⟩
  filter_upwards [paid] with h bill c lo hi
  exact ⟨stageDir h W roles pad padding,bill c lo hi⟩

end Hierarchy.Tagged

end
end OAI
