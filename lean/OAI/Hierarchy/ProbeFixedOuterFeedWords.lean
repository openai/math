import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProtocolRAMCalendarFeedStock

namespace OAI
/-! # Physical retained and spilled stock at every fixed outer feed -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockBound
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners

private theorem outer_request (active : Commodity (Fin (2^z)) N k → ℕ) (u : ℕ)
    (cap : ∀i,active i ≤ v.keepLimit*width) (i : Commodity (Fin (2^z)) N k) :
    active i+(if u < v.mesh.inject then slice v.mesh.inject width u * payloadUnit i else 0) ≤ (v.keepLimit+1)*width := by
  rw [Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add (cap i)
  by_cases live : u < v.mesh.inject
  · rw [ite_eq_left live]
    have cut:=FeedLayout.slice_le_total width live
    cases i <;> simp [payloadUnit,cut]
  · simp [live]

/-- On the actual event tape, the feed reads the last active account of the
phase. It publishes a retained word for the next phase and the exact excess in
the immutable spill column, including when the clock has entered cooling. -/
theorem outer_feed_words (mem : Memory W) (stock : Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width))
    (initialRoom : P.joint.initial+PurchaseInventory.footprint z N k+
      (sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (G).first)
    (addressRoom : (G).endAddress v.mesh < 2^W) (headroom : (v.keepLimit+1)*width < 2^W)
    (u : ℕ) (hu : u < v.mesh.inject+v.mesh.cool) (i : Commodity (Fin (2^z)) N k) :
    let L:=FeedLayout.atEvent («N»:=N) v.mesh G f P.joint.initial width v.keepLimit (.outer u)
    let bits:=(A).bank.requests width v.mesh.inject u ((A).trial C mem u v.mesh.outerFuel)
    ((A).trial C mem (u+1) 0).bits i=min (bits i) (v.keepLimit*width) ∧
      (phaseState C mem (u+1) (L.overflow+PurchaseInventory.slot i)).val=spillBits v.keepLimit width bits i := by
  intro L bits
  let entry:=trialState C mem u v.mesh.outerFuel
  have active (g : Commodity (Fin (2^z)) N k) : (A).stockAt (.outer u v.mesh.outerFuel) g=L.active+PurchaseInventory.slot g :=
    stockAt_outer_end v.mesh G f P.joint.initial width v.keepLimit u g
  have next : (A).stockAt (.outer (u+1) 0) i=L.kept+PurchaseInventory.slot i :=
    stockAt_outer_next v.mesh G f P.joint.initial width v.keepLimit u i hu
  obtain ⟨_,atFeed⟩:=outer_feed_slot C mem u hu stock.mounted_all
  have request:=v.outer_request z width (PurchaseInventory.stock L.active entry) u (stock.slot atFeed).1 i
  have source : bits i=PurchaseInventory.stock L.active entry i +
      if u < v.mesh.inject then slice v.mesh.inject width u*payloadUnit i else 0 := by
    change (entry ((A).stockAt (.outer u v.mesh.outerFuel) i)).val+_= _
    rw [active];rfl
  have checked:=v.stock_feed P z width r banks src tab dst owners (.outer u) (outerFeed_occurs v.mesh hu) initialRoom addressRoom
  have maxWord : v.keepLimit*width < 2^W := by rw [Nat.add_mul,Nat.one_mul] at headroom;omega
  have rows : 2^z ≤ 2^W := Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega)
  apply L.stored A C u mem rfl checked.1 checked.2 maxWord rows i rfl rfl (active i) next
  change bits i < 2^W
  exact source.le.trans_lt (request.trans_lt headroom)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
