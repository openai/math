import OAI.Hierarchy.TaggedWideEconomicTariff
import OAI.Hierarchy.ProtocolRAMCatalystChargedSlab

namespace OAI
/-! # Fixed linear space for the complete original calendar and its public terminal archive -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripDirectory StripChart CoreBoard CatalystArchive
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "d" => 2^v.W

def wideCharges (N : ℕ) := 2*((v.wideMenuCard N).1+2)+2*((v.wideMenuCard N).2+2)

theorem selector_end (P : v.Placement) (h width : ℕ) :
    (v.emptyReserve P h width).base≤(v.publicHeader P h width).stop+v.wideCharges (publicStages v.W) := by
  let m:=charges F (v.sized (v.seed P h width) width) v.cost (v.publicHeader P h width).stop
  have left:=m.payload.charged_size
  have right:=m.purchase.charged_size
  simp only [pow_one,one_mul] at left right
  change m.payload.stop≤(v.publicHeader P h width).stop+2*(((v.wideMenuCard (Stages h d)).1+1)+1) at left
  change m.purchase.stop≤ m.payload.stop+2*(((v.wideMenuCard (Stages h d)).2+1)+1) at right
  change m.purchase.stop≤_
  have stages : Stages h d=publicStages v.W:=fixed_stage_count h v.W
  rw [congrArg v.wideMenuCard stages] at left right
  unfold wideCharges
  omega

def prefixExtra := v.wideCharges (publicStages v.W)+2*(GlobalTests.kinds (publicStages v.W) k+1)+
  2^GlobalTests.kinds (publicStages v.W) k

theorem initial_slab (P : v.Placement) (h width : ℕ) :
    let s:=v.sized (v.seed P h width) width
    let H:=v.publicHeader P h width
    (chargedSlab F s v.cost H (ProtocolRAMPurchaseSampler.bits v.keepLimit)).headerEnd≤H.stop+v.prefixExtra*2^h := by
  let N:=publicStages v.W
  let n:=2^h
  have nn : 1≤n:=Nat.two_pow_pos _
  let K:=GlobalTests.kinds N k
  let base:=v.emptyReserve P h width
  have a:=v.selector_end P h width
  have b:=ProtocolRAMPurchaseSampler.span_le (PurchaseInventory.footprint h (Stages h d) k)
  have stages : Stages h d=N:=fixed_stage_count h v.W
  have size : base.size≤2*(K*n+1):=by
    change ProtocolRAMPurchaseSampler.span _≤_
    simpa only [stages,PurchaseInventory.footprint,GlobalTests.kinds,K,n] using b
  change base.base+base.size+2^GlobalTests.bits h (Stages h d) k≤_
  rw [GlobalTests.bits,congrArg (fun n => GlobalTests.kinds n k) stages,pow_add]
  change base.base≤(v.publicHeader P h width).stop+v.wideCharges N at a
  have bound : 2*(K*n+1)≤(2*(K+1))*n:=by nlinarith only [nn]
  have fee := Nat.le_mul_of_pos_right (v.wideCharges N) nn
  change base.base+base.size+n*2^K≤(v.publicHeader P h width).stop+
    (v.wideCharges N+2*(K+1)+2^K)*n
  nlinarith only [a,size,bound,fee]

theorem wideFirst :
    ∃c:ℕ,∀ h width,v.keepLimit*width+1≤2^h →
      (v.privateArena (v.widePlacement h width) h width).first≤c*2^h := by
  obtain ⟨C,bound⟩:=v.wideEconomicHeight
  let head:=C+v.prefixExtra
  let R:=v.rowFactor
  refine ⟨head+8*stripRecordFactor v.mesh d k v.sampler.degree v.depth+
    20*CatalystArchive.slotFactor d k+16*R+16,fun h width fit=>?_⟩
  let P:=v.widePlacement h width
  let s:=v.sized (v.seed P h width) width
  let H:=v.publicHeader P h width
  let prior:=chargedSlab F s v.cost H (ProtocolRAMPurchaseSampler.bits v.keepLimit)
  have low : prior.headerEnd≤head*2^h:=by
    rw [show head*2^h=C*2^h+v.prefixExtra*2^h from Nat.add_mul ..]
    exact (v.initial_slab P h width).trans (Nat.add_le_add_right (bound h width fit) _)
  exact Slab.enlarged_header_bound prior v.mesh s P.catalogue P.routes F head R low (v.wideCatalogueRows h width)

def nativeStrideFactor (N alphabet : ℕ) :=
  let a:=(N*(2*k))*v.sampler.degree^v.depth
  let b:=(N*(2*k))*PurchaseFrozen.factor d v.sampler.degree v.depth
  let g:=1+N*(2*k)
  let D:=max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
  let digits:=max (Fintype.card (PayloadStrip.Quotes N k)) (Fintype.card (ChainStrip.Axes v.depth k))
  2^(alphabet*a)+2^a+2^ProtocolRAMPurchaseSampler.bits v.keepLimit+b+2*v.sampler.degree^v.depth+
    (21+3*D+digits)*a+10*g+2^a+5*(a*D)+15

theorem wideArena :
    ∃c:ℕ,∀ h width,v.keepLimit*width+1≤2^h →
      (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤c*2^h := by
  obtain ⟨C,bound⟩:=v.wideFirst
  refine ⟨C+(events v.mesh).length*v.nativeStrideFactor (publicStages v.W) v.menu.alphabet,?_⟩
  intro h width fit
  let P:=v.widePlacement h width
  let src:=v.seed P h width
  let s:=v.sized src width
  let a:=v.slab src P width
  have low : a.headerEnd≤C*2^h:=bound h width fit
  have size:=Slab.size_linear a s v.mesh low
  let q:=(catalogue F (v.configured src) v.cost).alphabet
  change (v.privateArena P h width).endAddress v.mesh≤(C+(events v.mesh).length*
    v.nativeStrideFactor (Stages h d) q)*2^h at size
  have st : Stages h d=publicStages v.W:=fixed_stage_count h v.W
  have menu : q=v.menu.alphabet:=(v.catalogue_words src width).1
  simpa only [st,menu] using size

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
