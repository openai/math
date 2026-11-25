import OAI.Hierarchy.DiscrepancyPaddedCap
import OAI.Hierarchy.ProbeFixedBroadcastCap
import OAI.Hierarchy.ProbeFixedRowPages

namespace OAI
/-! # Bounding every word of the initialized selector-price banks, including padding -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory DiscrepancyROM ThreeFlat.RAM
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing


namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "H" => v.publicHeader P z width
local notation "fee" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local instance broadcastPagesPayloadRoleNonempty : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
local instance broadcastPagesPurchasedRoleNonempty : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩

theorem broadcast_charge_words :
    (∀ u key, (fee).payload.word u key ≤ v.maxBits) ∧
    (∀ u key, (fee).purchase.word u key ≤ v.maxBits) := by
  constructor
  · intro u key
    let menu := payloadMenu F N k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt
      v.geometry.cutoff.1 v.cost.payload v.cost.payload_nonneg 0
    change MenuROM.chargeWord menu (key 0).val≤v.maxBits
    apply MenuROM.chargeWord_le
    intro i
    exact (Finset.le_sup (f:=fun j : menu.index => (menu.packet j).selectorBits) (Finset.mem_univ i)).trans
      (v.payload_selector_bits N (fixed_stage_count z v.W))
  · intro u key
    change MenuROM.chargeWord v.boughtPackets (key 0).val≤v.maxBits
    apply MenuROM.chargeWord_le
    intro i
    exact (Finset.le_sup (f:=fun j : v.boughtPackets.index => (v.boughtPackets.packet j).selectorBits)
      (Finset.mem_univ i)).trans v.purchased_selector_bits

/-- Both page ranges have their physical public price bound in the actual prefix image. -/
theorem broadcast_charge_image {w : ℕ} (raw : Memory w) :
    (∀x,(fee).payload.base≤x → x<(fee).payload.stop → (((fee).words raw) x).val≤v.maxBits) ∧
    (∀x,(fee).purchase.base≤x → x<(fee).purchase.stop → (((fee).words raw) x).val≤v.maxBits) := by
  obtain ⟨left,right⟩:=v.broadcast_charge_words P z width
  constructor
  · intro x lo hi
    change (((fee).purchase.words ((fee).payload.words raw)) x).val≤_
    rw [Table.outside _ _ (Or.inl (show x<(fee).purchase.base from hi))]
    exact Table.capped_words _ raw left x lo hi
  · exact Table.capped_words _ ((fee).payload.words raw) right
end FixedProtocolFormat

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
