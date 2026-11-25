import OAI.Hierarchy.TaggedWideWindowProgramLayout
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Linear advice space for the genuine thirty-way reads of every purchased format -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles Tagged Filter
open ProtocolRAMFrozenWindow ProtocolRAMPackedRanked ProtocolRAMSupergroupDirectory
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def wideROMFactor (m ell cap : ℕ) :=
  let B:=10*v.rowFactor*cap+v.widePackedFactor*(2^ell+1)+1
  4*v.widePackedFactor+2*(siteFactor (2^v.W) k+1)+(m+1)*(26*(B+1)+4*v.widePackedFactor)

theorem original_window_advice {κ A : ℝ} (m ell cap : ℕ) :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A,∀dated : WideCPU.Dated (events v.mesh).length,∀bits start:ℕ,
      v.wideFormatEnd x m ell cap dated bits start≤v.wideGroupROM x dated bits start+v.wideROMFactor m ell cap*2^x.h := by
  filter_upwards [WideParent.fixed_mul_width (κ:=κ) (A:=A) cap] with x small
  intro dated bits start
  let n:=2^x.h
  change cap*x.w+1 ≤ n at small
  let H:=WideMemory.H x.h v.W k v.wideJobs
  let G:=(WideMemory.dir x.h v.W k v.wideJobs).groups
  let N:=(v.widePlacement x.h x.w).catalogue.rows
  let D:=v.wideWindowDemand x ell cap
  let B:=10*v.rowFactor*cap+v.widePackedFactor*(2^ell+1)+1
  have npos : 1≤n:=Nat.one_le_two_pow
  have hpos : 1≤H:=Nat.one_le_two_pow
  have packed : (G+1)*H≤v.widePackedFactor*n:=v.wide_group_space x.h
  have groups : G+1≤v.widePackedFactor*n:=by
    have mono:=Nat.mul_le_mul_left (G+1) hpos
    simpa only [Nat.mul_one] using mono.trans packed
  have rectangle : (G+1)*(H*2^ell+1)≤v.widePackedFactor*n*(2^ell+1):=by
    have a:=(Nat.mul_le_mul_right (2^ell) packed)
    nlinarith only [a, groups]
  have rows : N≤v.rowFactor*n:=v.wideCatalogueRows x.h x.w
  have demand : D≤B*n:=by
    change 10*(N*cap)+(G+1)*(H*2^ell+1)+cap*x.w+1≤_
    dsimp [B]
    nlinarith only [Nat.mul_le_mul_right (10*cap) rows,rectangle,small]
  have stride : v.wideWindowStride x ell cap≤(26*(B+1)+4*v.widePackedFactor)*n:=by
    have a:=bias_words D
    have b:=bias_words G
    change 13*2^groupBits D+2*2^groupBits G≤_
    nlinarith only [a,b,demand,groups,npos]
  have layerCount : siteLast x.h (2^v.W) k+1 ≤ siteFactor (2^v.W) k*n :=
    site_count x.h (2^v.W) k Nat.one_le_two_pow
  have layer : 2^groupBits (siteLast x.h (2^v.W) k+1)≤2*(siteFactor (2^v.W) k+1)*n:=by
    nlinarith only [bias_words (siteLast x.h (2^v.W) k+1),layerCount,npos]
  have groupArea : 2*span G≤4*v.widePackedFactor*n:=by
    change 2*2^groupBits G≤_
    nlinarith only [bias_words G,groups]
  change (v.wideGroupROM x dated bits start+2*span G+2^groupBits (siteLast x.h (2^v.W) k+1))+
    (m+1)*v.wideWindowStride x ell cap≤_
  change _≤v.wideGroupROM x dated bits start+(4*v.widePackedFactor+2*(siteFactor (2^v.W) k+1)+
    (m+1)*(26*(B+1)+4*v.widePackedFactor))*n
  nlinarith only [groupArea,layer,Nat.mul_le_mul_left (m+1) stride]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
