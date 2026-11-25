import OAI.Hierarchy.DescentBaseDepth
import OAI.Hierarchy.DescentBaseVariance
import OAI.Hierarchy.DescentBaseReservations
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Shared reset reservations computed from the original old-block traffic -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V]

/-- A dyadic decay large enough to pay twice the incident degree. Its exponent
depends only on the current host degree. -/
def decayExponent (Δ : ℕ) := Nat.log 2 (2*Δ)+1

theorem decay_degree (Δ : ℕ) : 2*Δ≤2^decayExponent Δ :=
  (Nat.lt_pow_succ_log_self (by decide : 1<2) (2*Δ)).le

/-- The physical reset uses D=32 ceil(log₂(2Δ)) and K₁=Δ 2^D. The smoothing
exponent fits half of D, so these concrete values pay all reservations. -/
theorem decay_parameters {Δ : ℕ} (branch : 0<Δ) :
    2*decayExponent Δ≤32*Nat.clog 2 (2*Δ) ∧
    Δ*2^decayExponent Δ≤Δ*2^(32*Nat.clog 2 (2*Δ)) := by
  have p := Nat.clog_pos (by decide : 1<2) (show 1<2*Δ by omega)
  have l := Nat.log_le_clog 2 (2*Δ)
  have half : 2*decayExponent Δ≤32*Nat.clog 2 (2*Δ) := by unfold decayExponent;omega
  exact ⟨half,Nat.mul_le_mul_left Δ (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- The mean per old block, keeping the block identifiers in the function. -/
def blockMean (L : ℕ) (a : Fin (2^L) → ℝ) := (∑i,a i)/(2:ℝ)^L

/-- The normalized bin mean at the deeper intersection depth plus the overflow
cushion is exactly the native absolute pair reservation divided by its scale. -/
theorem normalized_capacity {A : Type*} [Fintype A] {L d e K : ℕ} (dL : d≤L) (eL : e≤L)
    (old : A ≃ Fin (2^L)) (core : Fin (2^L) → ℝ) {scale : ℝ} (positive : 0<scale) :
    (∑i,core (old i)/scale)/(2:ℝ)^max d e+1/K=
      pairCapacity L d e (blockMean L core) scale K / scale := by
  rw [←Finset.sum_div,old.sum_comp]
  have exp : (2:ℝ)^L = (2:ℝ)^(L-max d e)*(2:ℝ)^max d e := by
    rw [←pow_add,show L-max d e+max d e=L by omega]
  unfold pairCapacity blockMean
  rw [exp]
  by_cases zero : K=0
  · subst K
    simp
    field_simp
  · have nonzero : (K:ℝ)≠0 := by exact_mod_cast zero
    field_simp


theorem normalized_mean_capacity {A Q : Type*} [Fintype A] [Fintype Q] {L d e K : ℕ}
    (dL : d≤L) (eL : e≤L) (old : A ≃ Fin (2^L)) (bins : Fintype.card Q=2^max d e)
    (core : Fin (2^L) → ℝ) {scale : ℝ} (positive : 0<scale) :
    DescentBaseVariance.mean (fun i=>core (old i)/scale) Q + 1/K =
      pairCapacity L d e (blockMean L core) scale K / scale := by
  simpa only [DescentBaseVariance.mean,bins,Nat.cast_pow,Nat.cast_ofNat] using
    normalized_capacity (K:=K) dL eL old core positive

/-- Joint construction of shared dyadic bases and all actual touching-pair
reservations. The hub rows have exactly the minimal permitted base length
whenever each of their old blocks has the maximal load. -/
theorem reset_bases (near : V → Finset V) (sym : ∀v w,w∈near v↔v∈near w)
    {Δ L r f K : ℕ} (degree : ∀v,(near v).card≤Δ)
    (quota : Δ*2^decayExponent Δ≤K) (kPos : 0<K) (fr : f≤r) (rL : r≤L)
    {B ε : ℝ} (Bpos : 0<B)
    (wt : V → Fin (2^L) → ℝ) (core : V → V → Fin (2^L) → ℝ)
    (pos : ∀v i,0≤wt v i) (room : ∀v i,wt v i≤B)
    (traffic : ∀v i,∑ w∈near v,core v w i≤wt v i)
    (slack : (Fintype.card V:ℝ)*(2:ℝ)^(L-r)*((2:ℝ)^f*B)≤ε) :
    ∃ b : V → ℕ,
      (∀v,L-r≤b v ∧ b v≤L-f ∧ (2:ℝ)^(L-b v)*blockMean L (wt v)≤(2:ℝ)^f*B) ∧
      (∀ v w,w∈near v → b w≤b v+decayExponent Δ) ∧
      ((2:ℝ)^f*B)*(∑v,(2:ℝ)^b v)≤4*(ε+∑v,∑i,wt v i) ∧
      (∀ v id,(∑ w∈near v,∑ _j∈touching (b v) (b w) id,
        pairCapacity L (b v) (b w) (blockMean L (core v w)) ((2:ℝ)^f*B) K) ≤
        2*((2:ℝ)^f*B)) ∧
      (∀ v,(∀i,wt v i=B) → b v=L-f) := by
  let μ := fun v => blockMean L (wt v)
  have denom : 0<(2:ℝ)^L := by positivity
  have bound (v : V) : μ v≤B := by
    apply (div_le_iff₀ denom).2
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => room v i)
    simpa [mul_comm] using h
  have posμ (v : V) : 0≤μ v := div_nonneg (Finset.sum_nonneg (fun i _ => pos v i)) denom.le
  obtain ⟨b,fit,smooth,total⟩ := exists_base_depth near sym degree (decay_degree Δ)
    (Nat.zero_lt_succ _) fr rL Bpos μ posμ bound
  have width (v : V) : b v≤L := (fit v).2.1.trans (Nat.sub_le _ _)
  have restoration : (2:ℝ)^L*(∑v,μ v)=∑v,∑i,wt v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [μ,blockMean]
    field_simp
  refine ⟨b,fit,smooth,?_,?_,?_⟩
  · rw [restoration] at total
    linarith
  · apply reservation_budget near b width smooth degree quota kPos _ (by positivity)
      (fun v w => blockMean L (core v w)) μ _ (fun v => (fit v).2.2)
    intro v
    simpa [μ,blockMean] using mean_incidence near wt core traffic v
  · intro v saturated
    have exactMean : μ v=B := by
      simp [μ,blockMean,saturated,denom.ne']
    have cap := (fit v).2.2
    rw [exactMean] at cap
    have exp : L-b v≤f := (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
      (le_of_mul_le_mul_right cap Bpos)
    have upper := (fit v).2.1
    omega

end
end Hierarchy.DescentBaseProfile

end OAI
