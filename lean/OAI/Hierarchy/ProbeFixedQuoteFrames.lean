import OAI.Hierarchy.ProbeFixedScalarQuoteCells
import OAI.Hierarchy.ProbeFixedRowPages
import OAI.Hierarchy.ProbeFixedFailureWords

namespace OAI
/-! # Immutable price, tile and stock reads at the native ballot and before the signed commit -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit PurchaseStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "Goods" => Commodity (Fin (2^z)) N k
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "fs" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners
variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))
local notation "B" => repair C a
local notation "before" => (guard C a).apply entry
local notation "checked" => postSnapshot ((C).layout a) B (prepared C a entry)
local notation "cutoff" => (v.privateArena P z width).base v.mesh (.attempt a)

theorem row_buffer_frame (run : ready C (.attempt a) entry) (x : ℕ) (low : x<cutoff) :
    before x=entry x ∧ checked x=entry x ∧ input a entry x=entry x := by
  have safe:=(v.event_prefix P z width r banks src tab dst owners (.attempt a) x low).1
  obtain ⟨guardRoom,_,excess,payload,disc,mask,_,verdict,_⟩:=safe
  have prior:=(v.event_prefix P z width r banks src tab dst owners (.attempt a) x low).1
  refine ⟨?_,?_,?_⟩
  · exact ProtocolRAMGeneratedWrite.frame_image ((C).stopAt a) 1 (stop (C).mesh (C).modeAt a)
      entry x (.inl guardRoom)
  · change image (B).repairBits.base _ _ ((B).tests.after (prepared C a entry)) x=entry x
    simp only [image,fillSegment,not_le.mpr mask,false_and,ite_false,AttemptGate.TestBoard.after]
    rw [(B).tests.discrepancy.frame _ x disc,(B).tests.payload.frame _ x payload,(B).tests.excess.frame _ x excess]
    exact prepared_prior C a entry x run prior
  · change stageInput (fs a).pricedArea (fs a).stockSource (g a)
      (postOutput ((C).layout a) B (prepared C a entry)) x=entry x
    rw [stage_frame _ _ _ _ _ (verdict.trans (Nat.lt_succ_self _)) (Nat.le_add_right ..)]
    exact postOutput_prior C a entry x run prior

theorem row_buffer_stock (run : ready C (.attempt a) entry) (bills : Event→WordRows) (i : Goods) :
    let x:=(fs a).stockSource.old.base+PurchaseInventory.slot i
    let out:=entry ((v.nativeAccount P z width bills).stockAt a i)
    before x=out ∧ checked x=out ∧ input a entry x=out := by
  intro x out
  have padded:=v.stock_padded_old P z width a
  have span:=ProtocolRAMPurchaseSampler.lt_span (PurchaseInventory.footprint z N k)
  have small:=PurchaseInventory.slot_lt i
  have early : x<cutoff := by
    change (fs a).market.shelf.stockBase+PurchaseInventory.slot i<cutoff
    exact (Nat.add_lt_add_left (small.trans span) _).trans_le padded
  have account : entry x = out := congrArg entry (v.stock_pointer P z width bills a i).symm
  obtain ⟨atGuard,atCheck,atInput⟩ :=
    v.row_buffer_frame P z width r banks src tab dst owners a entry run x early
  exact ⟨atGuard.trans account, atCheck.trans account, atInput.trans account⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
