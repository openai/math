import OAI.Hierarchy.TaggedWideInstalledBudget
import OAI.Hierarchy.TaggedWideInstalledGates
import OAI.Hierarchy.TaggedWideInstalledCheap

namespace OAI
/-! # A single public price coefficient for the authentic pair of mounted CPU circuits -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged
open WideControlJoin ThreeFlat.RAM PhysicalProcedure Filter
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A s : ℝ} (m ell short : ℕ) {u : ℝ→ℝ} (hu : TaggedWidthProfile.Admissible s u)
  (δ ξ : ℝ) (unitCost : ℕ)

set_option maxHeartbeats 1200000 in
include hu in
theorem cofinal_mounted_pair :
    ∃ N : ℕ,∀ᶠ x : WideParent κ A in WideParent.large κ A,
      let g:=v.wideDated x.h x.w ell unitCost
      let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost g
      let S:=v.wideInstalledSize x m ell unitCost g
      let W:=wordBits x.h (2^v.W) copies
      ∃ (room : v.GateRoom x.h x.w v.maxBits l S) (a b : Mounted x.h N),
        (v.wideGates x.h x.w v.maxBits l S room)=(a.gate,b.gate) ∧
        a.rows≤N*2^x.h ∧ b.rows≤N*2^x.h ∧ S+2*2^x.h<2^W := by
  obtain ⟨N,bill⟩:=v.cofinal_width_hardware (κ:=κ) (A:=A) m ell short hu δ ξ unitCost
  have ok:=Mounted.original_ready (κ:=κ) (A:=A) (2^v.W) N (N:ℝ) 0 (by positivity) le_rfl
  refine ⟨N,?_⟩
  filter_upwards [bill,ok] with x bill ready
  intro g l S W
  let times:=v.wideProgramTicks x.h x.w v.maxBits l
  let rows:=v.wideGateRows x.h x.w v.maxBits l S
  let n:=2^x.h
  have money : rows≤N*n:=bill.1
  have rate : ((N*n:ℕ):ℝ)≤(N:ℝ)*((2:ℝ)^x.h*(Real.log (x.h:ℝ))^(0:ℝ)):=by
    simp only [Nat.cast_mul,Real.rpow_zero,mul_one,Nat.cast_pow,Nat.cast_ofNat,n,le_refl]
  obtain ⟨square,tall⟩:=ready (N*n) rate
  obtain ⟨a,b,eqn,left,right⟩:=v.wide_mounted_pair x.h x.w v.maxBits l N S bill.2.1 bill.2.2.1
    (v.wide_installed_cheap x m ell short u δ ξ unitCost g).1
    (v.wide_installed_cheap x m ell short u δ ξ unitCost g).2 (money.trans square) tall
  refine ⟨_,a,b,eqn,?_,?_,?_⟩
  · rw [left]
    exact (Nat.add_le_add_left (le_max_left ..) S).trans money
  · rw [right]
    exact (Nat.add_le_add_left (le_max_right ..) S).trans money
  · have wider : 2*x.h≤W:=by dsimp only [W];rw [wordBits_linear];omega
    exact (Nat.lt_of_succ_le bill.2.2.2).trans_le (square.trans (Nat.pow_le_pow_right (by decide) wider))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
