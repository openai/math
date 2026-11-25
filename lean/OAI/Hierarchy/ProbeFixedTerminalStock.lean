import OAI.Hierarchy.ProbeFixedAttemptStates

namespace OAI
/-! # The retained stock bank at the last feed of the fixed calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open scoped Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "N" => Stages z (2^v.W)
local notation "goods" => PurchaseInventory.footprint z N k
local notation "total" => (v.mesh.inject + v.mesh.cool)
local notation "finish" => Attempt.outer total 0

/-- The original fixed-width word column received by the terminal reporter. -/
def fixedTerminalStock : Bank :=
  ⟨previousStock v.mesh P.joint.initial (publishedStock v.mesh G f) (.attempt finish),
    ProtocolRAMPurchaseSampler.bits goods⟩

/-- The predecessor of the virtual terminal attempt is the last scheduled outer feed. -/
theorem fixedTerminalStock_base : (v.fixedTerminalStock P z width).base =
    (G).base v.mesh (.feed (.outer (total-1))) := by
  let p := total-1
  have first := v.clock.inject_pos
  have inside : p < total := by dsimp [p]; omega
  have next : p+1 = total := by dsimp [p]; omega
  change previousStock v.mesh P.joint.initial (publishedStock v.mesh G f) (.attempt finish) =
    publishedStock v.mesh G f (.feed (.outer p))
  apply previous_succ v.mesh P.joint.initial (publishedStock v.mesh G f) (outerFeed_occurs v.mesh inside)
  rw [← next]
  simp [position,trialBase,phaseSize,Nat.add_mul,Nat.add_assoc]

/-- The twice-rounded sampler allocation is fully covered by the last event stride. -/
theorem fixedTerminalStock_end : (v.fixedTerminalStock P z width).base +
    (v.fixedTerminalStock P z width).size ≤ (G).endAddress v.mesh := by
  have first := v.clock.inject_pos
  have inside := outerFeed_occurs v.mesh (by omega : total-1 < total)
  have pad := ProtocolRAMPurchaseSampler.span_le goods
  have bound : (v.fixedTerminalStock P z width).size ≤ (G).stride := by
    change ProtocolRAMPurchaseSampler.span goods ≤ _ + 8*goods+4
    omega
  rw [v.fixedTerminalStock_base P z width]
  exact (Nat.add_le_add_left bound _).trans ((G).within v.mesh _ inside)

theorem fixedTerminalStock_word {W : ℕ} (bills : Event → WordRows) (mem : Memory W)
    (i : Commodity (Fin (2^z)) N k) (fit : PurchaseInventory.slot i < 2^W) :
    (v.fixedTerminalStock P z width).read mem (PurchaseInventory.slot i : Word W) =
      mem ((v.nativeAccount P z width bills).stockAt finish i) := by
  have slot : PurchaseInventory.slot i < (v.fixedTerminalStock P z width).size :=
    (PurchaseInventory.slot_lt i).trans (ProtocolRAMPurchaseSampler.lt_span goods)
  simp only [Bank.read,Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt slot]; rfl

/-- In particular this reads the retained bits in the final executed memory,
with the exact native commodity key of the signed inventory. -/
theorem fixedTerminalStock_read {W : ℕ} (bills : Event → WordRows) (mem : Memory W)
    (i : Commodity (Fin (2^z)) N k) (fit : PurchaseInventory.slot i < 2^W) :
    ((v.fixedTerminalStock P z width).read mem (PurchaseInventory.slot i : Word W)).val =
      ((v.nativeAccount P z width bills).read finish mem).bits i :=
  congrArg Fin.val (v.fixedTerminalStock_word P z width bills mem i fit)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
