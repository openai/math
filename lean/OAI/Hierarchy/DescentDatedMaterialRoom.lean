import OAI.Hierarchy.DescentDatedMaterialPhase

namespace OAI
/-! Address and word-width conditions for the same ordinary material program on every input. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "n" => (e).sourceRows
local notation "P₀" => breadth (fmt).degree
local notation "L" => (e).oldLanes
local notation "H" => (e).oldHosts
local notation "G₀" => (e).oldGroups
local notation "N" => DepotRAM.Material.Sheets.count fmt

structure MaterialRoom (base : ℕ) (parts reverseBank : Bank) (w : ℕ) : Prop where
  sameReach : (e).reach=P₀
  source : parts.Fits w base
  sourceSize : n≤parts.size
  reverse : reverseBank.Fits w base
  reverseSize : H*(e).reach≤reverseBank.size
  purchase : L*max (e).jointBits (e).fieldBits≤w/2
  range : (e).endAddress base<2^w

theorem materials_count : N=(e).fields :=by
  change 15*((fmt).blocks*((fmt).cap*11))=15*((fmt).blocks*(fmt).cap*11)
  rw [Nat.mul_assoc (fmt).blocks (fmt).cap]

theorem material_chartEnd (base : ℕ) (h : (e).reach=P₀) :
    DonorChartBook.endAddr H G₀ L P₀ base=(e).joinBase base :=by
  simp only [MaterialExtent.joinBase,MaterialExtent.chartGuard,MaterialExtent.chartWords,
    MaterialExtent.sourceRows,MaterialExtent.chartStep,DonorChartBook.endAddr,DonorChartBook.words,
    DonorChartBook.pages,h,Nat.add_assoc]

theorem material_addresses (base : ℕ) : (v.joinBank base).base=(e).jointStart base ∧
    (v.joinBank base).base+(v.joinBank base).size=(e).observationsStart base ∧
    (v.materialJob base).src.base=(e).valuesStart base ∧
    (v.materialJob base).src.base+(v.materialJob base).src.size=(e).overlapStart base ∧
    (v.materialJob base).limit ((e).overlapStart base)=(e).projectionStart base :=by
  have total:=v.materials_count
  refine ⟨rfl,rfl,?_,?_,rfl⟩
  · change RoleScans.home _ _ _ _ N _=_
    simp only [RoleScans.home,RoleScans.pitch,MaterialExtent.valuesStart,MaterialExtent.pageWords,
      MaterialExtent.keyBits,MaterialExtent.sourceRows,DepotRAM.Material.Sheets.bits,total]
    rfl
  · change RoleScans.home _ _ _ _ N _+2^Nat.clog 2 (N*(H*chunks G₀ L)+1)=_
    simp only [RoleScans.home,RoleScans.pitch,MaterialExtent.overlapStart,MaterialExtent.valuesStart,
      MaterialExtent.pageWords,MaterialExtent.keyBits,MaterialExtent.sourceRows,DepotRAM.Material.Sheets.bits,total]
    rfl

theorem stampedRoof (base : ℕ) : DepotRAM.Material.Route.Projection.roof (e).fieldBits (e).blocks (e).lanes (e).hosts
    (e).groups (e).reach ((e).projectionStart base)=(e).endAddress base :=by
  simp only [DepotRAM.Material.Route.Projection.roof,DepotRAM.Material.Route.Projection.markBase,
    DepotRAM.Material.Route.Projection.mapBase,DepotRAM.Material.Route.Projection.width,MaterialExtent.endAddress,
    MaterialExtent.mapsStart,MaterialExtent.socketBits,MaterialExtent.nextRows]
  ring

variable {base w : ℕ} {parts reverse : Bank} (ok : v.MaterialRoom base parts reverse w)
theorem material_order : base≤(e).joinBase base ∧ (e).joinBase base≤(e).jointStart base ∧
    (e).jointStart base+n≤(e).observationsStart base ∧
    (e).observationsStart base≤(e).valuesStart base ∧
    (e).valuesStart base+(e).fields*n≤(e).overlapStart base ∧
    (e).overlapStart base≤(e).projectionStart base ∧ (e).projectionStart base≤(e).endAddress base :=by
  have row:n≤2^Nat.clog 2 (n+1):=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  have all:(e).fields*n≤2^Nat.clog 2 ((e).fields*n+1):=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _)
  refine ⟨Nat.le_add_right ..,Nat.le_add_right ..,Nat.add_le_add_left row _,Nat.le_add_right ..,
    Nat.add_le_add_left all _,?_,?_⟩
  · rw [←(v.material_addresses base).2.2.2.2];exact (v.materialJob base).advances _
  · unfold MaterialExtent.endAddress MaterialExtent.mapsStart;omega

include ok in
theorem material_header_fit : Fits (v.rankHeader base reverse) H G₀ L w ((e).joinBase base) :=by
  have ord:=v.material_order (base:=base)
  obtain ⟨_,h₁,h₂,h₃,h₄,h₅,h₆⟩:=ord
  have lim:(e).joinBase base<2^w:=by have:=ok.range;omega
  have previous:reverse.base≤base:=(Nat.le_add_right ..).trans ok.reverse.2.2
  have addr:=v.material_chartEnd base ok.sameReach
  have code:=DonorChartBook.geometry H G₀ L P₀ base reverse.base ((e).joinBase base) previous addr.le lim
  exact ⟨⟨ok.reverse.1,ok.reverse.2.1,ok.reverse.2.2.trans (Nat.le_add_right ..)⟩,code.block,code.live,code.spread,
    by change H * P₀ ≤ reverse.size; rw [←ok.sameReach]; exact ok.reverseSize,code.blockSize,code.liveSize,code.spreadSize⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
