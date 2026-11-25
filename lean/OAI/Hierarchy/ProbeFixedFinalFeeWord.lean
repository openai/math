import OAI.Hierarchy.ProbeFixedBirthFees
import OAI.Hierarchy.ProbeFixedPrintedRole
import OAI.Hierarchy.ProbeFixedOriginalPrice
import OAI.Hierarchy.ProtocolRAMBoughtPaidSupport

namespace OAI
/-! # Re-evaluating the actual paid edge price from the terminal history -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open StripChart StockCommit PurchaseStage CoreBoard CatalogueRows ReportSockets
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "fs" => v.nativeFormats P z width
local notation "bs" => v.nativeBoards P z width
local notation "sink" => P.catalogue.sink r banks src tab dest owners

def directLabel (a : Attempt) := (fs a).labelSource sink P.catalogue.idBase
  (StripChart.header F bs a).fieldTerm (StripChart.id F bs P.catalogue a)

local notation "L" => v.directLabel P z width r banks src tab dest owners

/-- The published key-price pair and the re-evaluated direct traversal refer
to the same actual geometry at all dates. The genuine conditional price pass
itself proves that every operand was below its fresh output boundary. -/
theorem recomputed_label (a : Attempt) (m entry : Memory W) (pre post : List Event)
    (cut : Slot C m (.attempt a) pre post entry) (i : Fin (fs a).pricedArea.occurrences) :
    let out:=run C (events v.mesh) m
    out ((L a).out+i.val)=(P.catalogue.geometry 5).eval out ((L a).edge.eval out (i.val:Word W)) := by
  intro out
  let pf:=fs a
  let g:=L a
  let live:=postOutput ((C).layout a) (repair C a) (prepared C a entry)
  let batch:=enabledBatch ((C).layout a) ((C).raw a)
  let seg:=pricedSegment pf.pricedArea pf.stockSource g W batch
  have ready : seg.ready live:=cut.currentReady.2.2.2.2.2.2.2.2.2.2.1
  have span:g.out+pf.pricedArea.occurrences≤pf.pricedArea.stop:=pf.chargeColumns.1
  have earlier:g.out+pf.pricedArea.occurrences≤pf.pricedArea.start:=le_rfl
  have low (x : ℕ) (hx : x<g.out) : out x=live x := by
    have below : x < pf.pricedArea.stop :=
      hx.trans_le ((Nat.le_add_right g.out pf.pricedArea.occurrences).trans span)
    have eq:=v.attempt_word P z width r banks src tab dest owners m entry a pre post cut x below
    exact eq.trans (seg.frame live x ready (priced_keeps pf.pricedArea pf.stockSource g batch x earlier (Or.inl hx)))
  have comparison:=eval_below ((g.geometry 5).atRow g.edge) (i.val:Word W) live out ready.1.1 low
  rw [eval_atRow,eval_atRow] at comparison
  have index:g.out+i.val<pf.pricedArea.stop:=(Nat.add_lt_add_left i.isLt _).trans_le span
  exact (v.attempt_word P z width r banks src tab dest owners m entry a pre post cut _ index).trans
    ((price_label pf.pricedArea pf.stockSource g batch live i ready earlier).trans comparison.symm)

/-- Every ordinary positive direct hit has exactly the tariff carried by the
stored paid-rate word. No geometric validity is needed of inactive/padded words. -/
theorem direct_paid_rate (a : Attempt) (m entry : Memory W) (pre post : List Event)
    (cut : Slot C m (.attempt a) pre post entry) (i : Fin (fs a).pricedArea.occurrences) (edge : Fin P.catalogue.rows)
    (room : P.catalogue.rows≤2^W) (ordinary : v.paidSupply z a (v.occurrencePort P z width a i).val=false)
    (price : Fin P.catalogue.rows→ℝ) :
    let out:=run C (events v.mesh) m
    ((L a).edge.eval out (i.val:Word W)).val=edge.val →
    price edge=(((P.catalogue.geometry 5).eval out (edge.val:Word W)).val:ℝ) →
    price edge=v.paidRate P z width r banks src tab dest owners out a i := by
  intro out hit word
  have selected : (L a).edge.eval out (i.val:Word W)=(edge.val:Word W):=
    Fin.ext (hit.trans (Fin.val_cast_of_lt (edge.isLt.trans_le room)).symm)
  have stored:=v.recomputed_label P z width r banks src tab dest owners a m entry pre post cut i
  change out ((L a).out+i.val)=_ at stored
  rw [selected] at stored
  change price edge=v.printedCharge P z width a i (out ((L a).out+i.val)).val
  rw [v.nonsupply_price P z width a i _ ordinary,stored]
  exact word

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
