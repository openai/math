import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProbeFixedTerminalStock
import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # Stock and dated price words survive the terminal write to the verdict cell -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open scoped Classical Fin.CommRing BigOperators
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "hist" => postedRows v.mesh (v.issued P z width r banks src tab dst owners)
local notation "finish" => Attempt.outer (v.mesh.inject+v.mesh.cool) 0

theorem archive_charge_room (a : Attempt) (i : Fin ((A).charges a)) :
    ((A).row a i).width<(G).endAddress v.mesh ∧ ((A).row a i).key<(G).endAddress v.mesh := by
  change ((hist).word (cursor v.mesh a) i).width<_ ∧ ((hist).word (cursor v.mesh a) i).key<_
  obtain ⟨j,_,u,histRow⟩:=(hist).source (cursor v.mesh a) i
  rw [histRow]
  by_cases inside : j<(events v.mesh).length
  · have bounds:=postedRows_below v.mesh (v.issued P z width r banks src tab dst owners) G
      (fun e _=>v.issued_room P z width r banks src tab dst owners e) j (r:=u)
    have lim : (G).first+(j+1)*(G).stride≤(G).endAddress v.mesh :=
      Nat.add_le_add_left (Nat.mul_le_mul_right (G).stride inside) _
    exact ⟨bounds.1.trans_le lim,bounds.2.trans_le lim⟩
  · have empty : (hist).count j=0 := by simp [postedRows,scheduleRows,inside]
    exact Fin.elim0 (Fin.cast empty u)

private theorem inventory_equal {I : Type*} {x y : Inventory I} (bits : x.bits=y.bits) (paid : x.paid=y.paid) :
    x=y := by
  rcases x with ⟨leftBits,leftCash⟩
  rcases y with ⟨rightBits,rightCash⟩
  change leftBits=rightBits at bits
  change leftCash=rightCash at paid
  cases bits
  cases paid
  rfl

/-- This equality holds for either verdict, even without any selection
assumption. Each summand of the signed cash ledger reads its own historical
width and price words below the single terminal destination. -/
theorem terminal_check_state (m : Memory W) :
    (A).read finish (checkedOut C ((G).endAddress v.mesh) m)=(A).read finish (run C (events (C).mesh) m) := by
  have frame (x : ℕ) (low : x<(G).endAddress v.mesh) :
      checkedOut C ((G).endAddress v.mesh) m x=run C (events (C).mesh) m x :=
    ProtocolRAMGeneratedWrite.frame_image _ 1 _ _ _ (.inl low)
  apply inventory_equal
  · funext i
    have below : (A).stockAt finish i<(G).endAddress v.mesh := by
      change (v.fixedTerminalStock P z width).base+PurchaseInventory.slot i<_
      apply lt_of_lt_of_le _ (v.fixedTerminalStock_end P z width)
      exact Nat.add_lt_add_left ((PurchaseInventory.slot_lt i).trans
        (ProtocolRAMPurchaseSampler.lt_span (PurchaseInventory.footprint z N k))) _
    exact congrArg Fin.val (frame _ below)
  · simp only [AccountColumns.cash_words]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    obtain ⟨small,priced⟩:=v.archive_charge_room P z width r banks src tab dst owners finish i
    simp only [ChargeWord.value,frame _ small,frame _ priced]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
