import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProtocolRAMCalendarStockActual

namespace OAI
/-! # A physical nonrepair attempt writes a zero to every spill cell -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open StripChart StockBound StockCommit PurchaseStage RepairHistogram
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "G" => v.privateArena P z width
local notation "st" => v.taskCommit P z width
local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "input" => v.stage P z width r banks src tab dst owners

theorem nonrepair_spill (a : Attempt) (entry : Memory W) (run : ready C (.attempt a) entry)
    (layout : TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((G).base v.mesh (.attempt a)))
    (off : AttemptGate.actual (repair C a).policy
      (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))≠2)
    (i : Fin (f a).pricedArea.goods) :
    let ar:=(f a).pricedArea
    after C (.attempt a) entry (ar.output+ar.goods+ar.goods+i.val)=0 := by
  intro ar
  let B:=repair C a
  let L:=(C).layout a
  let s:=(f a).stockSource
  let u:=prepared C a entry
  let snap:=postSnapshot L B u
  let post:=postOutput L B u
  let j : Fin L.candidates:=⟨0,layout.positive⟩
  let mode : Pass:=⟨B.modeOut,L.candidates,AttemptGate.mode B.policy⟩
  have check : AuditReady (audits L B) snap:=run.2.2.2.2.2.2.1
  have printed:=post_read L B u check layout.board mode
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) j
  have marked : post ((C).modeAt a)=(AttemptGate.actual B.policy snap:Word W):=
    printed.trans (AttemptGate.mode_eval ..)
  have signal : (s.mode.eval (pricedTransfer ar s (g a) (b a) post) (i.val:Word W)).val≠2 := by
    rw [layout.window.mode,word_eval,pricedTransfer_prior ar s (g a) (b a) post layout.window.room
      layout.window.label _ layout.window.modeBefore,marked,
      Fin.val_cast_of_lt ((AttemptGate.actual_lt ..).trans_le layout.window.wide)]
    exact off
  have entered:=v.entered P z width r banks src tab dst owners a entry run
  let cells:=(st a).beforeApply (b a) (f a).market.rows (input a entry)
  have read:=(commit_mode (st a).columns (st a).plan cells entered.2.1 i layout.window.wide).2.2
  change after C (.attempt a) entry (ar.output+ar.goods+ar.goods+i.val)=
    (if (s.mode.eval (pricedTransfer ar s (g a) (b a) post) (i.val:Word W)).val=2 then _ else 0) at read
  exact read.trans (ite_eq_right signal)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
