import OAI.Hierarchy.ProbeFixedAttemptStates
import OAI.Hierarchy.ProtocolRAMCalendarReportedPriceRows
import OAI.Hierarchy.ProtocolRAMCalendarPhysicalCharges

namespace OAI
/-! # Actual signed charge records for the fixed chronological procedure -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "stages" => Stages z (2^v.W)

def paidSupply : Attempt→ℕ→Bool
  | .outer _ _, i=>if hi : i<Fintype.card (PayloadRole stages k) then
      decide (catalystBit ((Fintype.equivFin (PayloadRole stages k)).symm ⟨i,hi⟩)=1) else false
  | .inner _ _ _ _, i=>if hi : i<Fintype.card (PurchasedRole v.depth k) then
      decide (catalystBit ((Fintype.equivFin (PurchasedRole v.depth k)).symm ⟨i,hi⟩)=1) else false

theorem occurrence_count (a : Attempt) :
    (v.nativeFormats P z width a).pricedArea.occurrences=(StripChart.header F (v.nativeBoards P z width) a).count := by
  cases a <;> rfl

def occurrencePort (a : Attempt) (i : Fin (v.nativeFormats P z width a).pricedArea.occurrences) :=
  let H:=StripChart.header F (v.nativeBoards P z width) a
  (H.enum.symm (finCongr (v.occurrence_count P z width a) i)).2

def printedCharge (a : Attempt) (i : Fin (v.nativeFormats P z width a).pricedArea.occurrences) : ℕ→ℝ :=
  externalPrice (v.paidSupply z a (v.occurrencePort P z width a i).val) v.radius 1

def coreCharge (a : Attempt) (i : Fin (v.nativeFormats P z width a).pricedArea.goods) : ℕ→ℝ :=
  fun _=>routeCap stages v.radius (PurchaseInventory.lane ((v.nativeSlots P z width a).symm i))

def openingCharge := boughtPrice Λ p q Q (dyadicScale v.W) 1

/-- Constant geometric prices (stock spill and strip broadcast) do not depend
on the printed field word. Each direct edge and each newly bought edge uses
its live 7-field report's own length code. -/
def issued (r : ℕ) (banks : RouteSettlement.Banks) (source table dest : ℕ) (owners : Bank) : Event→WordRows
  | .attempt a=>
    let f:=v.nativeFormats P z width a
    let s:=v.nativeBoards P z width
    let sink:=P.catalogue.sink r banks source table dest owners
    let L:=f.labelSource sink P.catalogue.idBase (StripChart.header F s a).fieldTerm (StripChart.id F s P.catalogue a)
    let C:=v.nativeChart P z width r banks source table dest owners
    reportedRows f.pricedArea f.stockSource L (repair C a) (fun _=>0) width f.board.batch.copies
      (v.printedCharge P z width a) (fun _ _=>v.cost.atAttempt a) (v.coreCharge P z width a) (fun _=>v.openingCharge)
  | .feed b=>
    let f:=FeedLayout.atEvent (N:=stages) v.mesh (v.privateArena P z width) (v.nativeFormats P z width)
      P.joint.initial width v.keepLimit b
    spillRows f (fun _=>0) (fun i _=>routeCap stages v.radius (PurchaseInventory.lane i))

def billedAccount (r : ℕ) (banks : RouteSettlement.Banks) (source table dest : ℕ) (owners : Bank) :=
  v.nativeAccount P z width (v.issued P z width r banks source table dest owners)

theorem supply_price (a : Attempt) (i : Fin (v.nativeFormats P z width a).pricedArea.occurrences) (code : ℕ)
    (cat : v.paidSupply z a (v.occurrencePort P z width a i).val=true) :
    v.printedCharge P z width a i code=2*(v.radius:ℝ) := by simp [printedCharge,externalPrice,cat]

theorem nonsupply_price (a : Attempt) (i : Fin (v.nativeFormats P z width a).pricedArea.occurrences) (code : ℕ)
    (ordinary : v.paidSupply z a (v.occurrencePort P z width a i).val=false) :
    v.printedCharge P z width a i code=(code:ℝ) := by simp [printedCharge,externalPrice,lengthPrice,ordinary]

theorem bought_fee : v.openingCharge 1=Λ*(dyadicScale v.W)^p := by
  apply boughtPrice_unit
  · simp [lengthPrice]
  · unfold dyadicScale;positivity

theorem route_price (a : Attempt) (i : Fin (v.nativeFormats P z width a).pricedArea.goods) (code : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank) :
    v.coreCharge P z width a i code=((v.billedAccount P z width r banks src tab dest owners).bank.coordinates
      (v.nativeSlots P z width a)).box i := rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
