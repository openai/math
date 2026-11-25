import OAI.Hierarchy.ProbeReportSockets
import OAI.Hierarchy.TaggedWideStagePool

namespace OAI
/-! # Paying for the transport subslots of the fixed positive port directory -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterSupergroups TaggedShorterPacking Filter
open scoped Classical Topology

theorem batches_scaled (D B lanes : ℕ) (pos : 0<B) :
    batches (D*lanes) B≤lanes*batches D B := by
  have covers : D*lanes≤(lanes*batches D B)*B := by
    simpa only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using
      Nat.mul_le_mul_right lanes (batch_bounds D pos).1
  change (D*lanes+B-1)/B≤lanes*batches D B
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul pos).2
  rw [Nat.succ_mul]
  omega

/-- The bank purchased by the shortening proof stores per-port rows in a
single directory. Expanding each port into 2^ell subslots preserves its
child address by adding ell to the shortening offset. Both near and far
modules are now billed at their true expanded sizes. -/
theorem aligned_fixed (W k attempts ell : ℕ) (hW : 0<W) {c₀ U : ℝ} (positive : 0<c₀) :
    let roles := copies k attempts
    let pad := 2*roles
    ∃ short : ℕ, ∃ K : ℝ, ∀ᶠ h : ℕ in atTop, ∀ c : ℝ, c₀≤c → c≤U →
      let g := superAddress W pad h
      let D : ℕ := 2^g
      let t := g-short
      let B : ℕ := 2^(t-1)
      let M := ⌈6*c*(2:ℝ)^h/(2:ℝ)^t⌉₊
      let dir := stageDir h W roles pad (show 2*roles≤2^pad from Nat.lt_two_pow_self.le)
      superAddress W (pad+ell) h-(short+ell)=t ∧
        0<B ∧ 2*B=2^t ∧ 0<M ∧ (dir.groups:ℝ)*(2*B)≤c*(2:ℝ)^h ∧
        ((max M (dir.groups*batches (D*2^ell) B):ℕ):ℝ)*(D*2^ell:ℕ)≤K*(2:ℝ)^h ∧
        (M:ℝ)*(2*B)≤(7*U)*(2:ℝ)^h := by
  intro roles pad
  obtain ⟨short,K,paid⟩ := purchase_stage_pool_fixed W roles pad hW
    (show 2*roles≤2^pad from Nat.lt_two_pow_self.le) (U:=U) positive
  refine ⟨short,K*((2:ℝ)^ell)^2,?_⟩
  filter_upwards [paid] with h atHeight
  intro c lc hc g D t B M dir
  obtain ⟨hB,whole,hM,padding,near,far⟩ := atHeight c lc hc
  have shift : superAddress W (pad+ell) h=g+ell := by dsimp [g,superAddress]; omega
  refine ⟨by rw [shift]; dsimp only [t]; omega,hB,whole,hM,padding,?_,far⟩
  let lanes := (2:ℕ)^ell
  let old := max M (dir.groups*batches D B)
  have scaled : max M (dir.groups*batches (D*lanes) B)≤old*lanes := by
    apply max_le
    · have cover : old≤old*lanes := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left old (show 1≤lanes from Nat.one_le_two_pow)
      exact (le_max_left ..).trans cover
    · calc
        _ ≤ dir.groups*(lanes*batches D B) := Nat.mul_le_mul_left _ (batches_scaled D B lanes hB)
        _ = (dir.groups*batches D B)*lanes := by ac_rfl
        _ ≤ old*lanes := Nat.mul_le_mul_right _ (le_max_right ..)
  have cost : (old:ℝ)*D≤K*(2:ℝ)^h := near
  have upper : ((max M (dir.groups*batches (D*lanes) B):ℕ):ℝ)≤(old:ℝ)*lanes := by exact_mod_cast scaled
  change ((max M (dir.groups*batches (D*lanes) B):ℕ):ℝ)*((D*lanes:ℕ):ℝ) ≤
    (K*((2:ℝ)^ell)^2)*(2:ℝ)^h
  rw [Nat.cast_mul]
  calc
    _ ≤ ((old:ℝ)*lanes)*(D*lanes) := mul_le_mul_of_nonneg_right upper (by positivity)
    _ = ((old:ℝ)*D)*(lanes:ℝ)^2 := by ring
    _ ≤ (K*(2:ℝ)^h)*(lanes:ℝ)^2 := mul_le_mul_of_nonneg_right cost (sq_nonneg _)
    _ = (K*((2:ℝ)^ell)^2)*(2:ℝ)^h := by
      simp only [lanes,Nat.cast_pow,Nat.cast_ofNat]
      ring

theorem aligned_pool (W k attempts ell : ℕ) (hW : 0<W) {c₀ U : ℝ} (positive : 0<c₀) :
    let roles := copies k attempts
    let pad := 2*roles
    ∃ short : ℕ, ∃ K : ℝ, ∀ᶠ h : ℕ in atTop, ∀ c : ℝ, c₀≤c → c≤U →
      let g := superAddress W pad h
      let D : ℕ := 2^g
      let t := g-short
      let B : ℕ := 2^(t-1)
      let M := ⌈6*c*(2:ℝ)^h/(2:ℝ)^t⌉₊
      ∃ dir : Directory (reserved h W roles) D,
        superAddress W (pad+ell) h-(short+ell)=t ∧
        0<B ∧ 2*B=2^t ∧ 0<M ∧ (dir.groups:ℝ)*(2*B)≤c*(2:ℝ)^h ∧
        ((max M (dir.groups*batches (D*2^ell) B):ℕ):ℝ)*(D*2^ell:ℕ)≤K*(2:ℝ)^h ∧
        (M:ℝ)*(2*B)≤(7*U)*(2:ℝ)^h := by
  intro roles pad
  obtain ⟨short,K,paid⟩ := aligned_fixed W k attempts ell hW (U:=U) positive
  refine ⟨short,K,?_⟩
  filter_upwards [paid] with h bill c lo hi
  exact ⟨stageDir h W roles pad (show 2*roles≤2^pad from Nat.lt_two_pow_self.le),bill c lo hi⟩

end Hierarchy.ProbeStage.ReportSockets
end

end OAI
