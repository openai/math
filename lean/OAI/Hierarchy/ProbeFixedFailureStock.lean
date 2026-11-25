import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProtocolRAMCommittedPortLayout

namespace OAI
/-! # Input and output ledger indices of the native paid repair -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit
open PurchaseStage RepairHistogram
open scoped BigOperators Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners

/-- The earlier stock pointer in the model is the actual source captured by
the guard, and the next public pointer is the newly published commodity bank. -/
theorem repair_stock (a : Attempt) (entry : Memory W) (scheduled : Event.attempt a∈events v.mesh)
    (run : ready C (.attempt a) entry)
    (layout : StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a))) :
    let states:=Succession v.mesh (.attempt a)
    let e:=v.nativeSlots P z width a
    let B:=(A).bank.coordinates e
    (∀i : Fin (st a).goods,B.stock ((A).read states.1 entry) i=((input a entry) ((st a).plan.bank.base+i.val)).val) ∧
    ∀i : Fin (st a).goods,B.stock ((A).read states.2 (after C (.attempt a) entry)) i=
      (((st a).native W (f a).market.rows (b a)).after (input a entry) ((st a).plan.activeOut+i.val)).val := by
  intro states e B
  let old:=v.issued P z width r banks src tab dst owners
  let arena:=v.privateArena P z width
  have srcEq : states.1=a := by cases a <;> rfl
  have sec : position v.mesh (.attempt states.2)=position v.mesh (.attempt a)+1 := by
    have next:=Succession.next v.mesh (.attempt a)
    change cursor v.mesh states.2=cursor v.mesh states.1+1 at next
    rwa [srcEq] at next
  have widthFit : (f a).pricedArea.goods≤2^W := by
    have room:=layout.window.room
    unfold Area.stop at room
    omega
  constructor
  · rw [srcEq]
    apply v.read_input P z width old a _ _ _ _ C entry run _ widthFit layout.window.capacity.1 layout.window.old
    intro i
    apply (v.event_prefix P z width r banks src tab dst owners (.attempt a) _ _).1
    change (v.nativeAccount P z width old).stockAt a i<arena.base v.mesh (.attempt a)
    rw [v.stock_pointer P z width old a i,←v.slot_index P z width a i]
    exact (Nat.add_lt_add_left (e i).isLt (f a).stockSource.old.base).trans_le layout.oldLow
  · intro i
    let named:=e.symm i
    have ix : PurchaseInventory.slot named=i.val := by
      rw [←v.slot_index P z width a named]
      exact congrArg Fin.val (e.apply_symm_apply i)
    have addr : (A).stockAt states.2 named=(f a).pricedArea.output+i.val := by
      change previousStock v.mesh P.joint.initial (publishedStock v.mesh arena f) (.attempt states.2)+
        PurchaseInventory.slot named=_
      rw [previous_succ v.mesh P.joint.initial (publishedStock v.mesh arena f) scheduled sec,ix]
      rfl
    change ((after C (.attempt a) entry) ((A).stockAt states.2 named)).val=_
    rw [addr]
    rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
