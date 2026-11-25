import OAI.Hierarchy.ProbeFixedEventCosts
import OAI.Hierarchy.ProbeFixedFinalFeeWord
import OAI.Hierarchy.ProbePaidAddress

namespace OAI
/-! # The measured direct and mate tolls on the actual original dated bill -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PurchaseStage StockCommit
open ThreeFlat.RAM
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dest owners
local notation "fmt" => v.nativeFormats P z width
local notation "label" => v.directLabel P z width r banks src tab dest owners
local notation "rate" => v.paidRate P z width r banks src tab dest owners
local notation "bs" => v.nativeBoards P z width
local notation "sink" => P.catalogue.sink r banks src tab dest owners
local notation "rec" => v.receipts P z width r banks src tab dest owners

set_option maxHeartbeats 2000000 in
theorem direct_invoice (a : Attempt) (m entry : Memory W) (pre post : List Event)
    (cut : Slot C m (.attempt a) pre post entry) (len : Fin P.catalogue.rows→ℝ)
    (mask mate : Expr) (room : P.catalogue.rows≤2^W) :
    let out:=run C (events (C).mesh) m
    let f:=fmt a
    let flagged:=fun i=>v.paidSupply z a (v.occurrencePort P z width a i).val
    let direct:=fun i : Fin f.occurrences=>(label a).edge.eval out (i.val:Word W)
    let positive:=fun i : Fin f.occurrences=>(out (f.pricedArea.direct+i.val)).val≠0
    (∀i,flagged i=false→mask.eval out (i.val:Word W)=0) →
    (∀i,positive i→flagged i=false→∀e : Fin P.catalogue.rows,(direct i).val=e.val →
      len e=(((P.catalogue.geometry 5).eval out (e.val:Word W)).val:ℝ)) →
    (∀i,positive i→flagged i=true→∃e g : Fin P.catalogue.rows,(direct i).val=e.val ∧
      (mate.eval out (i.val:Word W)).val=g.val ∧ mask.eval out (i.val:Word W)≠0 ∧ len e+len g=2*(v.radius:ℝ)) →
    ∀i,positive i→addressPrice len (direct i).val+
      (if mask.eval out (i.val:Word W)=0 then 0 else addressPrice len (mate.eval out (i.val:Word W)).val)≤rate out a i := by
  intro out f flagged direct positive off ordinary catalyst i on
  cases type : flagged i with
  | false =>
    have code:=v.nonsupply_price P z width a i (out ((label a).out+i.val)).val type
    change rate out a i=_ at code
    simp only [off i type,ite_true,add_zero]
    by_cases hi : (direct i).val<P.catalogue.rows
    · let e : Fin P.catalogue.rows:=⟨_,hi⟩
      have price:=v.direct_paid_rate P z width r banks src tab dest owners a m entry pre post cut i e room type
        len rfl (ordinary i on type e rfl)
      have sameOut : run C (events v.mesh) m = out := by
        change run C (events v.mesh) m = run C (events (C).mesh) m
        exact congrArg (fun mesh => run C (events mesh) m)
          (v.common_clock P z width r banks src tab dest owners).symm
      have paid : len e = rate out a i :=
        price.trans (congrArg (fun mem => rate mem a i) sameOut)
      have scalar : addressPrice len (direct i).val = rate out a i :=
        (addressPrice_fin len e).trans paid
      rw [scalar]
    · simp only [addressPrice,dite_eq_right hi,code]
      positivity
  | true =>
    obtain ⟨e,g,one,two,live,total⟩:=catalyst i on type
    simp only [one,two,addressPrice_fin,ite_eq_right live,total]
    change 2*(v.radius:ℝ)≤v.printedCharge P z width a i _
    exact (v.supply_price P z width a i _ type).symm.le

theorem attempt_invoice (a : Attempt) (m : Memory W) (len : Fin P.catalogue.rows→ℝ)
    (routes : Traversals) (bound : ℕ) (mask second : Expr)
    (tree : Fin (fmt a).pricedArea.rows→List (Fin P.catalogue.rows))
    (core : Fin (fmt a).pricedArea.goods→List (Fin P.catalogue.rows)) :
    let f:=fmt a
    let forest:=v.nativeTrees P z width a
    let role:=(StripChart.header F bs a).fieldTerm
    let ids:=StripChart.id F bs P.catalogue a
    let cost:=fun i : Fin f.occurrences=>addressPrice len ((label a).edge.eval m (i.val:Word W)).val
    let twin:=fun i : Fin f.occurrences=>if mask.eval m (i.val:Word W)=0 then 0 else addressPrice len (second.eval m (i.val:Word W)).val
    f.occurrences≤2^W →forest.catalystMate=some (mask,second) →
    forest.Reads m tree → routes.Reads m core → bound<2^W → f.board.batch.copies<2^W →
    (∀i : Fin f.pricedArea.rows,(m (f.pricedArea.broadcast+i.val)).val≤bound) →
    (∀i : Fin f.pricedArea.rows,f.board.batch.copies*(m (f.pricedArea.broadcast+i.val)).val<2^W) →
    (∀i,(m (f.pricedArea.direct+i.val)).val≠0→cost i+twin i≤rate m a i) →
    (∀i : Fin f.pricedArea.rows,(m (f.pricedArea.broadcast+i.val)).val≠0 →((tree i).map len).sum≤v.cost.atAttempt a) →
    (∀i : Fin f.pricedArea.goods,(m (f.pricedArea.output+f.pricedArea.goods+f.pricedArea.goods+i.val)).val≠0 →
      ((core i).map len).sum≤v.coreCharge P z width a i 0) →
    ((f.paidSlices sink P.catalogue.idBase role ids forest routes bound).map (fun t=>t.toll m len width)).sum≤
      (rec m (.attempt a)).install := by
  intro f forest role ids cost twin fit mate locations paths word copies bits full price treeCost routeCost
  let B:=repair C a
  let cols:=(fresh f.pricedArea f.stockSource).eventColumns B.purchaseOut
  have exactCost:=f.installed_charge_of_direct sink P.catalogue.idBase role ids forest routes bound width m len cost twin tree core
    B.purchaseOut f.pricedArea.rows (fun _=>0)
    (f.address_direct sink P.catalogue.idBase role ids m len width fit) (f.address_mate forest mask second m len width fit mate)
    locations paths word copies bits full
  have comp:=charges_install_mono cols m width f.board.batch.copies (fun i=>cost i+twin i) (rate m a)
    (fun i=>((tree i).map len).sum) (fun _=>(v.cost.atAttempt a:ℝ))
    (fun i=>((core i).map len).sum) (fun i=>v.coreCharge P z width a i 0)
    (fun _ : Fin f.pricedArea.rows=>0)
    (fun j : Fin f.pricedArea.rows=>v.openingCharge (m (B.boughtFields 5+j.val)).val)
    price treeCost routeCost
  cases a <;> exact exactCost.le.trans comp

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
