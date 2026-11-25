import OAI.Hierarchy.TaggedWideFullMount
import OAI.Hierarchy.TaggedWideCorrectedSpillRate
import OAI.Hierarchy.TaggedWideWidthRoom
import OAI.Hierarchy.TaggedWideInstalledCheap

namespace OAI
/-! # Cofinal finite hardware for the complete paid parent control and its spill pages -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged
open WideControlJoin ThreeFlat.RAM PhysicalProcedure Filter
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A s : ℝ} (m ell short : ℕ) {u : ℝ→ℝ} (hu : TaggedWidthProfile.Admissible s u) (δ ξ : ℝ) (unitCost : ℕ)

attribute [local irreducible] CheapCode widePrograms wideProgramTicks wideCorrectedSpillProgram
  wideCorrectedSpillTicks wideCorrectedSpillEnd wideInstalledSize wideInstalledLayout wideDated

include hu
set_option maxHeartbeats 1000000 in
theorem cofinal_full_hardware :
    ∃N : ℕ,∀ᶠ x : WideParent κ A in WideParent.large κ A,
      let g:=v.wideDated x.h x.w ell unitCost
      let S:=v.wideInstalledSize x m ell unitCost g
      let progs:=v.wideFullPrograms x m ell short u δ ξ unitCost
      v.wideFullRows x m ell short δ ξ unitCost (u:=u)≤N*2^x.h ∧
      text progs.1≤N ∧ text progs.2≤N ∧ CheapCode progs.1 ∧ CheapCode progs.2 ∧ S+2*2^x.h+1≤N*2^x.h := by
  obtain ⟨b,previous⟩:=v.cofinal_width_hardware (κ:=κ) (A:=A) m ell short hu δ ξ unitCost
  obtain ⟨c,spills⟩:=v.wide_corrected_spill_rate ell unitCost v.maxBits
  refine ⟨b+c+c,?_⟩
  filter_upwards [previous,WideParent.fixed_mul_width (κ:=κ) (A:=A) 1] with x before small
  intro g S progs
  let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost g
  let start:=l.pruneScratch+l.pruneRows+1
  let root:=v.wideInstalledRoot x
  let n:=2^x.h
  let body:=v.widePrograms x.h x.w v.maxBits l
  let tick:=v.wideProgramTicks x.h x.w v.maxBits l
  let P:=v.wideCorrectedSpillProgram x.h x.w ell unitCost v.maxBits root S (g.romEnd root) (g.workEnd S) start
  let cost:=v.wideCorrectedSpillTicks x.h x.w ell unitCost v.maxBits root S (g.romEnd root) (g.workEnd S) start
  let stop:=v.wideCorrectedSpillEnd x.h x.w ell unitCost v.maxBits root S (g.romEnd root) (g.workEnd S) start
  have size_le : x.w≤2^x.h:=by simpa using (Nat.le_of_lt (show 1*x.w<2^x.h from small))
  obtain ⟨extraCode,extraTime,extraRoom⟩:=spills x.h x.w root S (g.romEnd root) (g.workEnd S) start size_le
  obtain ⟨oldRows,firstCode,oldCode,tagRoom⟩:=before
  have text₀ : text progs.1≤b:=firstCode
  have text₁ : text body.2≤b:=oldCode
  have text₂ : text P≤c:=extraCode
  have time : cost≤c*n:=extraTime
  have room : stop ≤ start+c*n:=extraRoom
  have maxRoom : max start stop ≤ start+c*n:=max_le (Nat.le_add_right ..) room
  have age : S+max (tick.1+3+1) (tick.2+3+start)≤b*n:=oldRows
  have left : S+(tick.1+3+1)≤b*n:=(Nat.add_le_add_left (le_max_left ..) S).trans age
  have right : S+(tick.2+3+start)≤b*n:=(Nat.add_le_add_left (le_max_right ..) S).trans age
  have fresh : S+max (tick.1+3+1) ((tick.2+cost)+3+max start stop)≤(b+c+c)*n := by
    rcases le_total (tick.1+3+1) ((tick.2+cost)+3+max start stop) with hfirst|hlast
    · rw [max_eq_right hfirst]
      simp only [Nat.add_mul]
      omega
    · rw [max_eq_left hlast]
      simp only [Nat.add_mul]
      omega
  have oldCheap:=v.wide_installed_cheap x m ell short u δ ξ unitCost g
  have extraCheap:=v.wide_corrected_spill_cheap x.h x.w ell unitCost v.maxBits root S (g.romEnd root) (g.workEnd S) start
  refine ⟨fresh,by omega,?_,oldCheap.1,cheap_seq oldCheap.2 extraCheap,?_⟩
  · change text (body.2.seq P)≤_
    rw [text_seq]
    omega
  · exact tagRoom.trans (Nat.mul_le_mul_right (2^x.h)
      ((Nat.le_add_right b c).trans (Nat.le_add_right (b+c) c)))

set_option maxHeartbeats 1000000 in
theorem cofinal_full_mounted_pair :
    ∃N : ℕ,∀ᶠ x : WideParent κ A in WideParent.large κ A,
      let g:=v.wideDated x.h x.w ell unitCost
      let S:=v.wideInstalledSize x m ell unitCost g
      let W:=wordBits x.h (2^v.W) copies
      ∃ (lim : v.FullGateRoom x m ell short u δ ξ unitCost) (a b : Mounted x.h N),
        v.wideFullGates x m ell short u δ ξ unitCost lim=(a.gate,b.gate) ∧
        a.rows≤N*2^x.h ∧ b.rows≤N*2^x.h ∧ S+2*2^x.h<2^W := by
  obtain ⟨B,fits⟩:=v.cofinal_full_hardware (κ:=κ) (A:=A) m ell short hu δ ξ unitCost
  let N:=B+1
  have ok:=Mounted.original_ready (κ:=κ) (A:=A) (2^v.W) N (N:ℝ) 0 (by positivity) le_rfl
  refine ⟨N,?_⟩
  filter_upwards [fits,ok] with x data ready
  intro g S W
  let n:=2^x.h
  have rate : ((N*n:ℕ):ℝ)≤(N:ℝ)*((2:ℝ)^x.h*(Real.log (x.h:ℝ))^(0:ℝ)):=by
    simp only [Nat.cast_mul,Real.rpow_zero,mul_one,Nat.cast_pow,Nat.cast_ofNat,n,le_refl]
  obtain ⟨square,tall⟩:=ready (N*n) rate
  have c : B≤N:=Nat.le_succ B
  have nc:=Nat.mul_le_mul_right n c
  have money:=data.1.trans nc
  obtain ⟨lim,a,b,eqn,ar,br⟩:=v.wide_full_mounted_pair x m ell short (u:=u) δ ξ unitCost N
    (data.2.1.trans c) (data.2.2.1.trans c) data.2.2.2.1 data.2.2.2.2.1 (money.trans square) tall
  refine ⟨lim,a,b,eqn,?_,?_,?_⟩
  · rw [ar];exact (Nat.add_le_add_left (le_max_left ..) S).trans money
  · rw [br];exact (Nat.add_le_add_left (le_max_right ..) S).trans money
  · have wide : 2*x.h≤W:=by dsimp only [W];rw [wordBits_linear];omega
    exact (Nat.lt_of_succ_le (data.2.2.2.2.2.trans nc)).trans_le (square.trans (Nat.pow_le_pow_right (by decide) wide))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
