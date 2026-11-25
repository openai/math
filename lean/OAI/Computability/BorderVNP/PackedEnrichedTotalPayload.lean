import OAI.Computability.BorderVNP.PackedEnrichedHistoryRecords
import OAI.Computability.BorderVNP.PackedSelectedRecordRanges
import OAI.Computability.BorderVNP.ShortenTotalPayload

/-! # Total box payload on a true selected shortening history

Expanded records charge each original or newly installed box at its physical
tile. On the calibrated cover the number of occupied tiles is at most the
bottom slot count and the propagated local cap fits within the input length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs

open Crossing Epoch Epoch.Round Cover Shortening
open scoped Classical

/-- Sum of the payload stored in all physical boxes, counted by their reduced site. -/
theorem SiteCap.sum_payload_le {D d : ℕ} {K : Type*} {P I : Type} [Fintype P] [Fintype I]
    {bits : P → ℕ} {p : Pack D P bits K} {L : ℝ} {r : SiteRoutes p I d L}
    {fields : RecordData p.layout} {B : ℕ} (h : SiteCap r fields true B) :
    ∑ v, fields.payload v ≤ CoverScale.sites I d * B := by
  have loc (tile : I → Deck (d+1)) := h tile
  exact (payload_sum_le_tiles fields.prior fields.payload (fun v => reduceMove d (r.origin v)) B
    (fun tile => (Nat.le_add_left _ _).trans (loc tile))).trans_eq
    (congrArg (· * B) (card_eq_sites I d _))

end Packing.PhysicalEpochs

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing PhysicalEpochs
open PublicCapacity Diagonal TeamScales
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
variable {start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape} {W : ℕ → Type}
variable [∀ t, Fintype (W t)] {deep : S.floor+1+S.drop*T ≤ start}
variable {good : ∀ t, State S start P bits shape W t → Prop}
variable {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
variable (M : Machine.{_,u} deep good V w) (bottom : Admissible good 0)
    (fields : RecordData bottom.val.pack.layout)

set_option maxHeartbeats 900000 in
/-- Total physical host payload on each genuine selected history. -/
theorem historyFields_total_payload_le (B : ℕ) (hbase : SiteCap bottom.val.route fields true B)
    (t : ℕ) (q : (packHistory bottom M.epoch t).Index) :
    ∑ v, (M.historyFields bottom fields t q).payload v ≤
      CoverScale.sites (Cube D) (depth S start t) * (S.recordFactor^t * B) :=
  (M.historyFields_bound bottom fields true B hbase t q).sum_payload_le

/-- The selected schedule's cover and calibrated growth give a quadratic
bound for every terminal host payload together, on the same history. -/
theorem historyFields_total_payload_at_scale {a x : ℕ} (scales : EpochScales S a x)
    {n r B : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hsite : (CoverScale.sites (Cube D) start : ℝ) ≤ r*(n : ℝ)^(9/10 : ℝ))
    (small : 1+B ≤ width n (1/2:ℝ)) (hbase : SiteCap bottom.val.route fields true B)
    (t : ℕ) (ht : t ≤ epochs scales.τ n) (q : (packHistory bottom M.epoch t).Index) :
    ∑ v, (M.historyFields bottom fields t q).payload v ≤ (r*n+1)^2 := by
  have expo : (n:ℝ)^(9/10:ℝ) ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1≤(n:ℝ))
      (by norm_num : (9/10:ℝ) ≤ 1)
  have hstart : CoverScale.sites (Cube D) start ≤ r*n := by
    exact_mod_cast hsite.trans (mul_le_mul_of_nonneg_left expo (Nat.cast_nonneg _))
  have tiles : CoverScale.sites (Cube D) (depth S start t) ≤ r*n :=
    (PublicCapacity.tiles_mono (Cube D) (Nat.succ_le_succ (Nat.sub_le start (S.drop*t)))).trans hstart
  have cap := (SelectedSchedule.caps_le_length S scales hn small).1 t ht
  rw [SelectedSchedule.boundary_add] at cap
  have per : S.recordFactor^t * B ≤ n := (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)).trans cap
  have bound := (M.historyFields_total_payload_le bottom fields B hbase t q).trans (Nat.mul_le_mul tiles per)
  have rn : n ≤ r*n := by simpa only [one_mul] using Nat.mul_le_mul_right n hr
  exact bound.trans ((Nat.mul_le_mul (Nat.le_add_right ..) (rn.trans (Nat.le_add_right ..))).trans_eq (sq _).symm)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
