import OAI.Computability.BorderVNP.PackedHistorySeedExecution
import OAI.Computability.BorderVNP.PackedCompleteBoundary
import OAI.Computability.BorderVNP.PackedEnrichedHistoryDecay

/-! # Decay of the actual signed verifier grid at the selected batch length -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Cover Crossing BorderVNP.Epoch Shortening Packing PhysicalEpochs DeckGrid GridPlacement
open Diagonal.ExternalSew TeamContraction PreparedBins TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {R r t pins link inner n d : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (pos : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (copies : ℕ)
local notation "axes" => Fintype.card (Cube D)
local notation "N" => seedBundle G axes d order pos copies

/-- The signed seed's active directions are precisely the channels between distinct cells. -/
theorem seed_exactCrossings (table : (N).Tables K) : (seedRoutes S G d order pos copies table).ExactCrossings := by
  intro c
  rw [seed_origin,seed_origin]
  let coord := GridShape.coordinate (d := d+1) (factorEnum D).symm
  constructor
  · intro h eq
    exact (of_decide_eq_true h) (coord.injective eq)
  · intro h
    exact decide_eq_true fun eq => h (congrArg coord eq)

/-- Initial potential per verifier copy, computed on the signed seed's own stored route. -/
theorem seed_initialPotential {τ : ℝ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hc : 0 < copies) (hτ : 0 ≤ τ)
    (site : (CoverScale.sites (Cube D) (d+1):ℝ) ≤ r*(n:ℝ)^(9/10:ℝ))
    (parse : (batchVolume n r:ℝ) ≤ volume τ r n) (table : (N).Tables K) :
    (seedRoutes S G d order pos copies table).potential S.weight / copies ≤
      ((1+2*S.weight)*Fintype.card (Direction axes)*(96*(4*axes+1)+1):ℝ) *
        volume τ r n*(logWidth r n:ℝ)^3 := by
  let V := CoverScale.sites (Cube D) (d+1)
  let H := seedChannelWidth n r axes d
  let J := Fintype.card (Direction axes)
  have h := (seedGeometry G d order pos copies).potential_le_of_reduction (factorEnum D).symm table
    (seedRoutes S G d order pos copies table) (seed_origin S G d order pos copies table) S.weight_pos.le
    (W := copies*H) (fun _ => le_rfl)
  have vq : CoverScale.sites (Fin axes) (d+1) = V := by
    simp only [V,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]
  have site' : (CoverScale.sites (Fin axes) (d+1):ℝ) ≤ r*(n:ℝ)^(9/10:ℝ) := by rw [vq]; exact site
  have raw := grid_width_budget (q := axes) (Fin axes) hn hr hτ site' parse
  have width : (V:ℝ)*H ≤ (96*(4*axes+1)+1:ℝ)*volume τ r n*(logWidth r n:ℝ)^3 := by
    rw [← vq]
    simpa only [H,seedChannelWidth,GridHosts.tileCount,CoverScale.sites,GridPlacement.cableWidth,← Nat.card_eq_fintype_card] using raw
  apply (div_le_iff₀ (by exact_mod_cast hc : 0 < (copies:ℝ))).mpr
  apply h.trans
  rw [Nat.cast_mul]
  have hw : 0 ≤ 1+2*S.weight := by linarith [S.weight_pos]
  have total := mul_le_mul_of_nonneg_left width (mul_nonneg (mul_nonneg hw (Nat.cast_nonneg J)) (Nat.cast_nonneg copies))
  change (1+2*S.weight)*V*J*(copies*H) ≤ ((1+2*S.weight)*J*_) * _ * _ * copies
  linarith only [total]

private theorem log_cube_le {τ : ℝ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (parse : (batchVolume n r:ℝ) ≤ volume τ r n) : (logWidth r n:ℝ)^3 ≤ (n:ℝ)^(τ/20) := by
  have npos : 0 < (n:ℝ) := by exact_mod_cast hn
  have rpos : 0 < (r:ℝ) := by exact_mod_cast hr
  apply le_of_mul_le_mul_left _ (mul_pos rpos npos)
  calc
    (r:ℝ)*n*(logWidth r n:ℝ)^3 ≤ (batchVolume n r:ℝ) := by
      have budget : r*n*logWidth r n^3 ≤ batchVolume n r := by
        rw [PublicCapacity.public_logWidth]
        unfold batchVolume
        rw [Nat.mul_comm r n]
        exact Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (by decide)) (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
      exact_mod_cast budget
    _ ≤ (r:ℝ)*n*(n:ℝ)^(τ/20) := by simpa only [volume,Real.rpow_add npos,Real.rpow_one,mul_assoc] using parse

/-- The original parse-volume fit already controls the cubic logarithm from the grid routing.
Thus every batch with that fit shares the signed width threshold, including a previously chosen
stretched sequence of batches. -/
theorem eventually_seed_decay {τ : ℝ} (hτ : 0 < τ) (small : τ < 1/2) (A B δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (batchVolume n r:ℝ) ≤ volume τ r n →
      A*volume τ r n*(logWidth r n:ℝ)^3 / 2^epochs τ n + 2*B*r*(n:ℝ)^(9/10:ℝ) ≤
        δ*exterior (τ/5) r n := by
  have hex : 0 < 1-τ/5 := by linarith
  have part := eventually_le_rounded_width (show (1+τ/20+τ/20)+(-τ) < 1-τ/5 by linarith)
    hex (show 0 < δ/2 by positivity) (2*A)
  have sites := eventually_le_rounded_width (show 9/10 < 1-τ/5 by linarith)
    hex (show 0 < δ/2 by positivity) (2*B)
  filter_upwards [part,sites,eventually_ge_atTop 1] with n first second hn
  intro r hr parse
  have npos : 0 < (n:ℝ) := by exact_mod_cast hn
  have charged : A*volume τ r n*(logWidth r n:ℝ)^3 / 2^epochs τ n ≤ (r:ℝ)*(δ/2*width n (1-τ/5)) := by
    calc
      _ = (A*volume τ r n*(logWidth r n:ℝ)^3)*(1/2^epochs τ n) := by ring
      _ ≤ (A*((r:ℝ)*(n:ℝ)^(1+τ/20))*(n:ℝ)^(τ/20))*(2*(n:ℝ)^(-τ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (log_cube_le hn hr parse) (by unfold volume; positivity))
          (VPVNP.Compression.inv_two_pow_blockCount τ hn) (by positivity) (by positivity)
      _ = (r:ℝ)*((2*A)*(n:ℝ)^((1+τ/20+τ/20)+(-τ))) := by
        rw [Real.rpow_add npos (1+τ/20+τ/20) (-τ),Real.rpow_add npos (1+τ/20) (τ/20)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left first (Nat.cast_nonneg _)
  have rest := mul_le_mul_of_nonneg_left second (Nat.cast_nonneg r : 0 ≤ (r:ℝ))
  simp only [exterior,Nat.cast_mul]
  linarith only [charged,rest]

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
