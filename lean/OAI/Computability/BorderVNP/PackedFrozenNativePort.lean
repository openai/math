import OAI.Computability.BorderVNP.PackedGroupedPortFrame
import OAI.Computability.BorderVNP.PackedHistoryScheduleBudget

/-! # Physical numbering of the true grouped seed ports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover BorderVNP.Epoch TeamContraction Packing Shortening Shortening.PublicCapacity
open Diagonal Diagonal.ExternalSew TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

variable {D : ℕ}

/-- The original finite array has one grouped port per tile of the selected cover. -/
theorem seedPortCount (d : ℕ) : GridHosts.tileCount (Fintype.card (Cube D)) d = CoverScale.sites (Cube D) (d+1) := by
  simp only [GridHosts.tileCount,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]

variable {m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The initial cable directory and its logarithmic words fit at the actual
selected cover, uniformly in the number of teams. -/
theorem eventually_native_bottom_range {a x : ℕ} (scales : EpochScales S a x) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let L := logWidth r n
      1≤L ∧ (boundaryShape S start 0).edges ≤ 2^(60*L) := by
  filter_upwards [eventually_boundaries S scales,eventually_ge_atTop 1] with n rows hn
  intro r hr start L
  have log : 1≤L := by
    rw [show L=Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact (Nat.clog_mono_right 2 (by nlinarith only [Nat.mul_le_mul hn hr] : 2≤2*n*r)).trans' (by decide)
  have pow : 2*n*r ≤ 2^L := by
    rw [show L=Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact Nat.le_pow_clog (by decide) _
  have fit : r*n ≤ 2^(60*L) := (show r*n ≤ 2*n*r by nlinarith).trans
    (pow.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  exact ⟨log,(show (boundaryShape S start 0).edges ≤ (boundaryShape S start 0).volume (CoverScale.sites (Cube D) start)
    by dsimp only [Shape.volume]; omega).trans (((rows r hr).1 0 (Nat.zero_le _)).trans fit)⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
