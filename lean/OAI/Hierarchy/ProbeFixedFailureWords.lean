import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCalendarFailedWords
import OAI.Hierarchy.ProtocolRAMCommittedTape
import OAI.Hierarchy.ProtocolRAMCalendarStockActual

namespace OAI
/-! # Literal event operands for an actual paid failure in the fixed chart -/
noncomputable section
open scoped Fin.CommRing
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

def stamp (a : Attempt) :=
  (f a).labelSource (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (StripChart.header F (v.nativeBoards P z width) a).fieldTerm (StripChart.id F (v.nativeBoards P z width) P.catalogue a)

local notation "g" => v.stamp P z width r banks src tab dst owners

def ballot (a : Attempt) := enabledBatch ((C).layout a) (repair C a)
def stage (a : Attempt) (entry : Memory W) :=
  stageInput (f a).pricedArea (f a).stockSource (g a) (postOutput ((C).layout a) (repair C a) (prepared C a entry))
def taskCommit (a : Attempt) := fresh (f a).pricedArea (f a).stockSource
def cashKeys (a : Attempt) :=
  reportedKeys (f a).pricedArea (g a) (repair C a) (fun _=>0)

local notation "b" => v.ballot P z width r banks src tab dst owners
local notation "st" => v.taskCommit P z width
local notation "input" => v.stage P z width r banks src tab dst owners
local notation "keys" => v.cashKeys P z width r banks src tab dst owners

theorem entered (a : Attempt) (entry : Memory W) (live : ready C (.attempt a) entry) :
    ((st a).native W (f a).market.rows (b a)).ready (input a entry) := by
  have installed : ((C).commit a).ready (postOutput ((C).layout a) (repair C a) (prepared C a entry)) :=
    live.2.2.2.2.2.2.2.2.2.2.1
  exact installed.2.2

theorem native_end (a : Attempt) (entry : Memory W) :
    ((st a).native W (f a).market.rows (b a)).after (input a entry)=after C (.attempt a) entry := rfl

/-- The signed sum passed to the native FailedRows constructor is exactly the
increment of the account, with both entries read on the one chronological run. -/
theorem posting (a : Attempt) (entry : Memory W) (scheduled : Event.attempt a∈events v.mesh)
    (live : ready C (.attempt a) entry) :
    let idx:=Succession v.mesh (.attempt a)
    let m':=((st a).native W (f a).market.rows (b a)).after (input a entry)
    ((A).read idx.2 m').paid=((A).read idx.1 entry).paid+∑e,
      ((st a).eventWords (repair C a).purchaseOut width (b a).copies (keys a)
        (v.printedCharge P z width a) (fun _ _=>v.cost.atAttempt a) (v.coreCharge P z width a)
        (fun _=>v.openingCharge) e).value width m' := by
  intro idx m'
  have sale:=v.append_paid P z width r banks src tab dst owners (.attempt a) entry scheduled live
  exact sale.trans (congrArg (((A).read idx.1 entry).paid+·) (WordRows.bill_ports _ width m'))

/-- No new strip fee occurs on a native selected failure. Every stock cell
reads mode two during its final commit on that same attempt. -/
theorem repair_words (a : Attempt) (entry : Memory W) (run : ready C (.attempt a) entry)
    (board : Board ((C).layout a) (repair C a) W) (positive : 0<((C).layout a).candidates)
    (window : StockWindow (f a).pricedArea (f a).stockSource (g a) ((C).modeAt a) (v.keepLimit*width) W)
    (failed : AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))=2) :
    (∀i : Fin (st a).goods,((st a).plan.mode.eval (beforeTransfer (st a).columns (st a).plan
      (st a).occurrences (st a).goods ((st a).beforeApply (b a) (f a).market.rows (input a entry)))
        (i.val:Word W)).val=2) ∧
    (∀j : Fin (f a).market.rows, ((st a).native W (f a).market.rows (b a)).after (input a entry)
      ((repair C a).purchaseOut+j.val)=0) := by
  exact ⟨fun i=>failure_mode C a entry (f a).pricedArea (f a).stockSource (g a) _ run board positive window failed i,
    fun j=>failure_flags C a entry run board window.wide failed j⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
