import OAI.Hierarchy.ProbeFixedFailureStock

namespace OAI
/-! # A native failure receipt on the fixed shape, in the original commodity coordinates -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native StripChart
open StockCommit PurchaseStage RepairHistogram
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
local notation "keys" => v.cashKeys P z width r banks src tab dst owners
variable (a : Attempt) (entry : Memory (wordBits z (2^v.W) copies))
  (layout : StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) a
    (v.nativeFormats P z width a).pricedArea (v.nativeFormats P z width a).stockSource
    (v.stamp P z width r banks src tab dst owners a) v.keepLimit width
    ((v.privateArena P z width).base v.mesh (.attempt a)))
  (run : Calendar.ready (v.nativeChart P z width r banks src tab dst owners) (.attempt a) entry)
  (π : PortPlan (v.taskCommit P z width a) (v.ballot P z width r banks src tab dst owners a)
    (v.stage P z width r banks src tab dst owners a entry) (v.nativeFormats P z width a).market.rows)

def selectedTape :=
  (st a).tape (b a) (input a entry) π (v.entered P z width r banks src tab dst owners a entry run)
    (fresh_broadcastRoom (f a).pricedArea (f a).stockSource (b a) layout.inputs layout.window.room) (keys a)
    (v.printedCharge P z width a) (fun _ _=>v.cost.atAttempt a)

local notation "T" => v.selectedTape P z width r banks src tab dst owners a entry layout run π
local notation "indices" => Succession v.mesh (.attempt a)
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width a)

/-- All financial, stock, and temporal identities are internal. The remaining
inputs concern the particular elected physical histogram, its prices, and its size. -/
def failed_packets (time : ℝ) (nominal : Fin (f a).market.rows→ℕ) (positive : 0<width)
    (scheduled : Event.attempt a∈events v.mesh)
    (failed : AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))=2)
    (funded : ∀i : Fin (st a).goods,resourceBits (T).kind (T).take i≤((input a entry) ((st a).plan.bank.base+i.val)).val)
    (fits : ∀i : Fin (st a).goods,((input a entry) ((st a).plan.bank.base+i.val)).val+resourceBits (T).kind (T).put i<2^W)
    (many : v.loss*(2^z:ℕ)≤(T).selected.card)
    (sizes : ∀j∈(T).selected,0<nominal j ∧ 2*(v.actualK*nominal j)≤width)
    (quotes : let price:=activePrice (T).kind (T).weight (maximizer (B).a (B).M time (B).coefficient (B).box
        ((B).units width ((A).read (indices).1 entry)))
      ∀j∈(T).selected,(∑e,((T).put (π.enum ⟨j,e⟩):ℝ)*price (π.enum ⟨j,e⟩))+(T).broadcast j+
        (copied v.actualK (nominal j) width:ℝ)*(nominal j*v.menu.margin/2) ≤
        ∑e,((T).take (π.enum ⟨j,e⟩):ℝ)*price (π.enum ⟨j,e⟩))
    (curve : (∑i,(stockChange (T).kind (netUnits width (T).put (T).take) i)^2/(4*time*(B).a))≤
      (2^z:ℕ)*v.loss*v.menu.margin/(8*v.actualK)) :
    (A).bank.FailedRows (2^z) width v.actualK v.keepLimit v.loss v.menu.margin time
      ((A).read (indices).1 entry) ((A).read (indices).2 (after C (.attempt a) entry)) := by
  have stock:=v.repair_stock P z width r banks src tab dst owners a entry scheduled run layout
  have reads:=v.repair_words P z width r banks src tab dst owners a entry run layout.board layout.positive layout.window failed
  apply FailedRows.ofCoordinates (v.nativeSlots P z width a)
  exact (st a).failedRows (b a) (input a entry) π (v.entered P z width r banks src tab dst owners a entry run)
    (fresh_broadcastRoom _ _ _ layout.inputs layout.window.room) (eventBoard _ _ _ layout.inputs layout.window.room)
    (keys a) (v.printedCharge P z width a) (fun _ _=>v.cost.atAttempt a) (v.coreCharge P z width a)
    (fun _=>v.openingCharge) (repair C a).purchaseOut (2^z) width v.actualK v.keepLimit v.loss v.menu.margin time
    B _ _ nominal positive (fresh_stockRoom _ _ _ layout.inputs width v.keepLimit layout.window.wide
      layout.window.room layout.window.budget (layout.window.budget.le.trans_lt layout.window.wordRoom)) stock.1 stock.2 funded fits reads.1
    (v.posting P z width r banks src tab dst owners a entry scheduled run)
    (fun i=>(v.route_price P z width a i _ r banks src tab dst owners).le) reads.2 many
    (fun j hj=>(sizes j hj).1) (fun j hj=>(sizes j hj).2) quotes curve

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
