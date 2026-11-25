import OAI.Hierarchy.TaggedWideFullRates

namespace OAI
/-! # Strict native word room at the rank, corrected ballot, and final turn boundaries -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged
open WideControlJoin Filter
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A s : ℝ} (m ell short : ℕ) {u : ℝ→ℝ} (hu : TaggedWidthProfile.Admissible s u)
  (δ ξ : ℝ) (unitCost : ℕ)

include hu in
theorem cofinal_full_spill_space :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A,
      let g := v.wideDated x.h x.w ell unitCost
      let l := v.wideInstalledLayout x m ell short u δ ξ unitCost g
      let first := l.pruneScratch+l.pruneRows+1
      let W := wordBits x.h (2^v.W) copies
      let S := v.wideInstalledSize x m ell unitCost g
      let R := v.wideInstalledRoot x
      let rank := v.wideSpillRankEnd x.h x.w v.maxBits first
      let dates := v.wideSpillDates x.h x.w ell unitCost v.maxBits first
      let stop := v.wideCorrectedSpillEnd x.h x.w ell unitCost v.maxBits R S
        (g.romEnd R) (g.workEnd S) first
      rank ≤ dates.endAt rank ∧ dates.endAt rank ≤ stop ∧ stop < 2^W := by
  obtain ⟨B,fits⟩ := v.cofinal_full_hardware (κ:=κ) (A:=A) m ell short hu δ ξ unitCost
  let N := B+1
  have enough := Mounted.original_ready (κ:=κ) (A:=A) (2^v.W) N (N:ℝ) 0 (by positivity) le_rfl
  filter_upwards [fits,enough] with x data ready
  intro g l first W S R rank dates stop
  have paid : v.wideFullRows x m ell short δ ξ unitCost (u:=u)≤B*2^x.h := data.1
  have rate : ((N*2^x.h:ℕ):ℝ)≤(N:ℝ)*((2:ℝ)^x.h*(Real.log (x.h:ℝ))^(0:ℝ)) := by simp
  have square := (ready (N*2^x.h) rate).1
  have wide : 2*x.h≤W := by dsimp only [W];rw [wordBits_linear];omega
  have word := square.trans (Nat.pow_le_pow_right (by decide) wide)
  let tt := v.wideFullTicks x m ell short u δ ξ unitCost
  have rows : S+max (tt.1+3+1) (tt.2+3+max first stop)≤N*2^x.h :=
    paid.trans (Nat.mul_le_mul_right _ (Nat.le_succ B))
  have right := (Nat.add_le_add_left (le_max_right (tt.1+3+1) (tt.2+3+max first stop)) S).trans rows
  have old := le_max_right first stop
  refine ⟨?_,Nat.le_add_right _ _,by omega⟩
  simp only [WideCPU.SpillDates.endAt,WideCPU.Dated.maskStart,WideCPU.Dated.controlStart,
    WideCPU.Dated.rolesEnd,WideCPU.SpillDates.roleRoot,WideCPU.endOf]
  omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
