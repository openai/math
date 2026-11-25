import OAI.Hierarchy.ProbeFixedFailurePlacement
import OAI.Hierarchy.ProbeFixedStripFunds

namespace OAI
/-! # Applying the actual payload and selected DFS placements to signed settlement -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing
variable {w z d k D q : ℕ} {F : Type*} [Field F] [Nonempty (Fin k)]
section payload
open ProbeStage StripDirectory PurchaseFrozen
local notation "stages" => (permutationFabric z d).shapes.length
variable [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)]
  (hk : 0<k) (M : ℝ) (hM : 0≤M) (eps : ℝ) (he : 0<eps) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ)
  (board : StripDirectory.Boards z d k q (Fintype.card (PayloadStrip.Quotes (permutationFabric z d).shapes.length k)) (Fintype.card (PayloadRole (permutationFabric z d).shapes.length k)))
  (prior start : ℕ) (mem : Memory w)
local instance : Nonempty (PayloadRole stages k) := ⟨.catalyst (PayloadStrip.first stages 0) (Classical.choice inferInstance)⟩
local notation "sourceP" => board.build (payloadFormat F z d k q hk M hM eps he tree ht minimum) prior
variable (size :
  let stageCount := (permutationFabric z d).shapes.length
  let packetMenu := payloadMenu F stageCount k hk M hM eps he tree ht minimum
  let rawBoard := board.build (payloadFormat F z d k q hk M hM eps he tree ht minimum) prior
  StripSizes rawBoard (payloadChannels z stageCount k).slot start D
    (Fintype.card packetMenu.index) (PacketWidths.ofMenu packetMenu).maximum mem)


local notation "I" => StripInput.of_payload hk M hM eps he tree ht minimum board prior start mem size

omit [Nonempty (Fin k)] in
theorem payload_funding_placement
    (original : ∀ j,j∈liveRows (I).ballot mem (sourceP).market.rows → j.val<2^z) : (I).Placed := by
  let R := ↥(liveRows (I).ballot mem (sourceP).market.rows)
  let r : R ↪ Fin (2^z) := ⟨fun j => ⟨j.val.val, original j.val j.property⟩,by
    intro a b eq
    exact Subtype.ext (Fin.ext (congrArg (fun i : Fin (2^z) => i.val) eq))⟩
  have width : PurchaseInventory.footprint z stages k ≤ 2^w :=
    (Nat.le_add_left _ _).trans (Nat.le_of_lt (I).bankFit)
  exact payload_slot_embedding (N:=stages) (k:=k) r mem width

end payload
section purchased
open ProbeStage StripDirectory PurchaseFrozen
local notation "stages" => (permutationFabric z d).shapes.length
variable (depth keyBase : ℕ) [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (sh : Shelf) (sampler : PurchaseSampler) (hk : 0<k) (M : ℝ) (hM : 0≤M)
  (eps : ℝ) (he : 0<eps) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ)
  (board : StripDirectory.Boards z d k q (Fintype.card (ChainStrip.Axes depth k)) (Fintype.card (PurchasedRole depth k)))
  (prior start : ℕ) (mem : Shelf.Mem z d)
local instance : Nonempty (PurchasedRole depth k) := ⟨.catalyst (ChainStrip.inlet depth 0) (Classical.choice inferInstance)⟩
local notation "sourceB" => board.build (purchasedFormat F z d k q depth keyBase sh sampler hk M hM eps he tree ht minimum) prior

local notation "W" => Native.wordBits z d Native.copies
variable (actualSize :
  let packetMenu := purchasedMenu F depth k hk M hM eps he tree ht minimum
  let rawBoard := board.build (purchasedFormat F z d k q depth keyBase sh sampler hk M hM eps he tree ht minimum) prior
  let channels := purchasedChannels (z:=z) (d:=d) (k:=k) sh sampler depth keyBase
  StripSizes rawBoard channels.slot start D (Fintype.card packetMenu.index) (PacketWidths.ofMenu packetMenu).maximum mem)
local notation "I" => StripInput.of_purchased depth keyBase sh sampler hk M hM eps he tree ht minimum
  board prior start mem actualSize

omit [Nonempty (Fin k)] in
theorem purchased_funding_placement (π : Equiv.Perm (Fin (2^z)))
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Shelf.Mem z d)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L sampler depth key).source
      (Shelf.pathRows sampler π depth key) mem)
    (flags : StoredFlags sh sampler π depth phase T kind frozen mem k)
    (headers : (stratumHeader z d k sampler.degree depth keyBase).Loaded mem)
    (keys : count z d k ≤ 2^W) (room : (depth+1)*paths z sampler.degree depth ≤ 2^W)
    (whole : count z d k*paths z sampler.degree depth ≤ 2^W) (wide : 0<W)
    (active : ∀ j,j∈liveRows (I).ballot mem (sourceB).market.rows →
      j.val<(stratumHeader z d k sampler.degree depth keyBase).count ∧
        (flagBank sh sampler z d k depth).read mem (j.val:Word W) ≠ 0) : (I).Placed := by
  let h := stratumHeader z d k sampler.degree depth keyBase
  let R := ↥(liveRows (I).ballot mem (sourceB).market.rows)
  let Active := {j : Fin h.count // (flagBank sh sampler z d k depth).read mem (j.val:Word W) ≠ 0}
  let row : R ↪ Active := ⟨fun j =>
    ⟨⟨j.val.val,(active j.val j.property).1⟩,(active j.val j.property).2⟩,by
    intro a b same
    exact Subtype.ext (Fin.ext (congrArg (fun j : Active => j.val.val) same))⟩
  have width : PurchaseInventory.footprint z stages k ≤ 2^W :=
    (Nat.le_add_left _ _).trans (Nat.le_of_lt (I).bankFit)
  obtain ⟨slots,read⟩ := purchased_slot_embedding sh sampler π depth keyBase hk phase T kind frozen mem
    tiles flags headers keys room whole wide width
  exact ⟨restrictPorts row slots,fun j a => read (row j) a⟩

end purchased
end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
