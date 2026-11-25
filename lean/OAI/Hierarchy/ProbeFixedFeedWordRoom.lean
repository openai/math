import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProbeStageAddress

namespace OAI
/-! # Native word bounds and the reserve table address for physical feed cells -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit PurchaseStage
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "G" => v.privateArena P z width
local notation "stride" => v.keepLimit*width+1
local notation "table" => sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps stride

/-- The single extra injection slice is word-safe uniformly for every allowed
payload width at sufficiently large input dimension. -/
theorem feed_headroom (payload : width ≤ 2^z) (dimension : v.keepLimit+2 ≤ 2^z) :
    (v.keepLimit+1)*width < 2^W := by
  have bound:=append_room (h:=z) (d:=2^v.W) (copies:=copies) (K:=v.keepLimit+1) dimension
  exact (Nat.mul_le_mul_left _ payload).trans_lt ((Nat.le_add_left ..).trans_lt bound)

/-- The scalar word index never wraps when the initial dimension pays for twice
the whole capped stock, even on the last live reserve slice. -/
theorem replay_headroom (payload : width≤2^z) (dimension : 2*v.keepLimit+1≤2^z) :
    2*(v.keepLimit*width)<2^W := by
  have bound:=append_room (h:=z) (d:=2^v.W) (copies:=copies) (K:=2*v.keepLimit) dimension
  rw [←Nat.mul_assoc]
  exact (Nat.mul_le_mul_left _ payload).trans_lt ((Nat.le_add_left ..).trans_lt bound)

theorem replay_slice_room (steps : P.joint.steps=v.mesh.reserveSteps)
    (digits : P.joint.cap*P.joint.width=v.keepLimit*width) : (table).base+(table).size≤(G).first := by
  have before := (Nat.le_add_right (JointHeader.half P.joint z N k).base _).trans (v.stock_half_low P z width)
  simpa only [JointHeader.half,FeedROM.halfBank,FeedROM.sliceBank,GlobalTests.rows,steps,digits] using before

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
