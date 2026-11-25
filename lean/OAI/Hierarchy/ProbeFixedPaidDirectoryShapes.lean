import OAI.Hierarchy.ProbeFixedPaidEconomicRows
import OAI.Hierarchy.ProbeFixedCatalystStaticEnd
import OAI.Hierarchy.ProtocolRAMPaidRouteCard

namespace OAI
/-! # Ordinary and catalyst width slices use physically bounded pre-calendar pair pages -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockBound StockCommit
open CoreRoute CatalystArchive StripDirectory
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
set_option quotPrecheck false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
local notation "D" => 2^v.W
local notation "N" => Stages z D
local notation "W" => wordBits z D copies
local notation "r" => Fintype.card (Slots z D k)
local notation "G" => v.privateArena P z width
local notation "fmt" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "tre" => v.nativeTrees P z width
local notation "O" => v.catalystPairOwners P z width
local notation "T" => v.catalystPairParity P z width

def paidSpillPath (recipe : Recipes) (x : Source) (order : Orders z D k) (_a : Attempt) : Traversals :=
  earlyTraversal recipe x v.sampler z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel) order O T

def paidFeedPath (x : Source) (layout : Boundary→FeedLayout z N k) (b : Boundary) (c : CommodityColumn) : Traversals :=
  boundaryTraversal x v.sampler z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel) (layout b) O T c

private theorem header_count (h : PortHeader) : h.count≤h.stop := by
  have bound:=ProtocolRAMPurchaseSampler.lt_span (2*h.count)
  change h.count≤h.parity.base+ProtocolRAMPurchaseSampler.span (2*h.count)
  omega

theorem paid_pair_sizes : 2*r≤(O).size ∧ 2*r≤(T).size := by
  have room := (Nat.lt_log2_self (n:=2*r))
  change 2*r≤2^((2*r).log2+1) ∧ 2*r≤2^((2*r).log2+1)
  exact ⟨room.le,room.le⟩

theorem paid_pair_ends : (O).base+(O).size≤v.catalystStaticStart P z width ∧ (T).base+(T).size≤v.catalystStaticStart P z width := by
  change (O).base+(O).size≤((O).base+(O).size)+(T).size ∧ _≤_
  exact ⟨Nat.le_add_right ..,le_rfl⟩

set_option maxHeartbeats 800000 in
/-- Each input pair page lies below the first write of the settlement reporter. -/
theorem paid_pair_geometry {n edges : ℕ} (sink : Sink n edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))→Expr)
    (feeds : Boundary→List CommodityColumn) (recipe : Recipes) (x : Source) (order : Orders z D k)
    (layout : Boundary→FeedLayout z N k) (maxBits limit : ℕ)
    (initial : (G).first≤limit) (staticAt : v.catalystStaticStart P z width≤limit) (routes : r≤limit) :
    ∀ s∈paidSlices v.mesh fmt feeds sink idBase role ids tre (v.paidSpillPath P z width recipe x order)
      (v.paidFeedPath P z width x layout) maxBits,
      s.owner.base+s.owner.size≤limit ∧ s.parity.base+s.parity.size≤limit ∧ s.count≤limit := by
  let shape (o t : Bank) (n : ℕ) := o.base+o.size≤limit ∧ t.base+t.size≤limit ∧ n≤limit
  apply PaidEventDirectory.all_shapes v.mesh fmt feeds sink idBase role ids tre
    (v.paidSpillPath P z width recipe x order) (v.paidFeedPath P z width x layout) maxBits shape
  · intro a live
    have ends:=paid_economic_bank_ends v P z width a live
    have row:=(paid_economic_headers v P z width a live).1
    exact ⟨ends.1.trans initial,ends.2.1.trans initial,
      row.2.2.1.le.trans ((header_count ((H).ports.header 0)).trans (row.2.2.2.trans initial))⟩
  · intro a live
    have ends:=paid_economic_bank_ends v P z width a live
    have row:=(paid_economic_headers v P z width a live).2
    exact ⟨ends.2.2.1.trans initial,ends.2.2.2.trans initial,
      row.2.2.1.le.trans ((header_count (paidTreeHeader v P z width a live)).trans (row.2.2.2.trans initial))⟩
  · intro a _
    obtain ⟨owner,tag⟩:=paid_pair_ends v P z width
    exact ⟨owner.trans staticAt,tag.trans staticAt,(early_positions_le_card recipe x v.sampler _ order O T).trans routes⟩
  · intro b _ c _
    obtain ⟨owner,tag⟩:=paid_pair_ends v P z width
    exact ⟨owner.trans staticAt,tag.trans staticAt,(boundary_positions_le_card x v.sampler _ (layout b) O T c).trans routes⟩

/-- Original economic headers and the two added immutable route pages survive the same
checked execution. All four constructors of actual paid slices read their own directory. -/
theorem paid_pair_rows {edges : ℕ} (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))→Expr)
    (feeds : Boundary→List CommodityColumn) (recipe : Recipes) (x : Source) (order : Orders z D k)
    (layout : Boundary→FeedLayout z N k) (maxBits : ℕ)
    (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank) (flag : ℕ) (m : Memory W)
    (pub : (H).Resident m) (ready : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) m)
    (after : (G).first≤flag) (room : 2*r≤2^W) (wide : 0<W)
    (stored : PaidPairDirectory.Reads O T r (checkedOut (v.nativeChart P z width r banks src tab dst owners) flag m)) :
    let final:=checkedOut (v.nativeChart P z width r banks src tab dst owners) flag m
    ∀ s∈paidSlices v.mesh fmt feeds sink idBase role ids tre (v.paidSpillPath P z width recipe x order)
      (v.paidFeedPath P z width x layout) maxBits,PaidEventDirectory.Rows s.owner s.parity final s.count := by
  intro final
  obtain ⟨ordinary,tree⟩:=paid_economic_rows v P z width r banks src tab dst owners flag m pub ready after
  obtain ⟨ownersRoom,tagsRoom⟩:=paid_pair_sizes v P z width
  have paired:=PaidEventDirectory.of_reads O T final r stored room ownersRoom tagsRoom wide
  apply PaidEventDirectory.all_rows _ _ _ _ _ _ _ _ _ _ _ final ordinary tree
  · intro a _
    exact paired.restrict (early_positions_le_card recipe x v.sampler _ order O T)
  · intro b _ c _
    exact paired.restrict (boundary_positions_le_card x v.sampler _ (layout b) O T c)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
