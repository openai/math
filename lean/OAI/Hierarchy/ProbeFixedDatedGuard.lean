import OAI.Hierarchy.ProtocolRAMCalendarGuardFits
import OAI.Hierarchy.ProbeFixedPostWindows
import OAI.Hierarchy.ProbeFixedStockPrefixFits

namespace OAI
/-! # The real scheduled guard and post-event archive lifetimes -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StripChart PurchaseStage StockCommit
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tbl dst owners
local notation "f" => v.nativeFormats P z width
local notation "A" => v.privateArena P z width
local notation "W" => wordBits z (2^v.W) copies

theorem dated_guard (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (room : (A).endAddress v.mesh<2^W) : (guard C a).Fits W := by
  let low:=(A).base v.mesh (.attempt a)
  have prior (b : Attempt) (hb : position v.mesh (.attempt b)<position v.mesh (.attempt a)) :
      (C).modeAt b<low := by
    have inside:=v.stock_mode_room P z width b
    exact inside.trans ((A).apart v.mesh hb)
  have input:=stop_before v.mesh (C).modeAt a low prior
  have tests : low≤(C).stopAt a := (v.stock_order P z width a).2.2
  have border : (C).stopAt a+1≤(f a).maskStart := by
    change (f a).testsStart+1≤PostLayout.afterTests _ (f a).testsStart
    unfold PostLayout.afterTests
    omega
  have mask : (f a).maskStart≤(f a).board.keys:=Nat.le_add_right ..
  have limit := (border.trans mask).trans_lt (v.post_window P z width a scheduled room).1
  have outputRoom : (C).stopAt a<2^W := (Nat.lt_succ_self _).trans limit
  exact ⟨Expr.fits_of_inputEnd _ (input.trans tests) outputRoom,limit⟩

theorem dated_keeps (a : Attempt) (b : Board ((C).layout a) (repair C a) W) :
    ((C).commit a).keeps (repair C a).verdict ∧
    ∀p∈writes ((C).layout a) (repair C a),∀i : Fin p.rows,((C).commit a).keeps (p.out+i.val) := by
  let ff:=f a
  let g:=v.stamp P z width r banks src tbl dst owners a
  let B:=repair C a
  let L:=(C).layout a
  have before : g.out+ff.pricedArea.occurrences≤ff.pricedArea.start:=le_rfl
  have keep (x : ℕ) (hx : x<g.out) : ((C).commit a).keeps x :=
    priced_keeps ff.pricedArea ff.stockSource g (enabledBatch L B) x before (.inl hx)
  have head : B.verdict<g.out:=Nat.lt_succ_self _
  refine ⟨keep _ head,?_⟩
  intro pass listed i
  exact keep _ ((Nat.add_lt_add_left i.isLt pass.out).trans_le (b.flagAfter pass listed) |>.trans head)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
