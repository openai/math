import OAI.Hierarchy.TaggedWireMeasuredPaid
import OAI.Hierarchy.TaggedWireInstallShape
import OAI.Hierarchy.TaggedWireElectedTender

namespace OAI
/-! # Mixed output shape at a genuine row election and its archived physical writes -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.CalendarTape.HistogramFormat
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open ProtocolRAM Calendar StockCommit PurchaseStage ChosenPackets Probe AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing

variable {F X : Type} [Field F] {S W q d paid ng : ℕ} {C : Chart W q d}
    (D : HistogramFormat C X) (ev : Attempt) (x : X) (start : Memory W)
    (a : Area) (s : Sources) (stamp : LabelSource) (mask mate : Expr) (post archive : Memory W)
    (G : PortGraph (Fin S) (Fin ng)) (P : PortGraph (Fin S) (Fin paid)) (pad : Chord S)
local notation "raw" => enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)
local notation "snap" => HistogramShelf.snapshot C ev start
local notation "I" => Fin (C.layout ev).candidates
local notation "picked" => fun i:I => (raw).selected snap (i.val:Word W)
local notation "phys" => unionRows G P pad

variable (view : D.observed ev x start)
    (menu : ∀i : Fin (C.layout ev).candidates,
      (enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)).selected
        (HistogramShelf.snapshot C ev start) (i.val : Word W) → Placed F S)
    (arity : ∀i hi, (menu i hi).data.terms =
      ((enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)).termCount.read
        (HistogramShelf.snapshot C ev start)
        ((enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)).packet.eval
          (HistogramShelf.snapshot C ev start) (i.val : Word W))).val)
    (route : ∀i hi,RowRouting (Row.packet (menu i hi)
      (enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)).copies) (unionRows G P pad))
    (choice : BallChoices (D.letters ev x) (D.copies ev x))
local notation "routeAt" => D.electedTender ev x start phys view menu arity route
local notation "chosen" => fun (i:I) (on:picked i) => cast
  (congrArg₂ (fun letters mass=>Histogram (Fin letters) mass)
    ((view.1 i).trans (arity i on).symm) ((view.2 i).trans (ite_eq_left on))) (choice i)

variable (L : PortPlan (fresh a s) (enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev))
    post (C.layout ev).candidates)
local notation "tag" => RepairHistogram.kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post
local notation "credit" => RepairHistogram.installedBits (n:=a.occurrences) (fresh a s).columns post
local notation "fir" => PaidWidths.paidDirect a s stamp
local notation "sec" => PaidWidths.paidMate a s mask mate

/-- Exact physical target before cap redistribution. Only elected routes need
a row readback. The native commit clears both archives on every other ballot.
A purchased catalyst's second radius and the independent tree array are summed
on their original paid-edge ordinals. -/
theorem measured_target (key : Fin ng≃Fin a.goods) (tree : PaidWidths.Slice) (treeAt : I→Fin paid→ℕ)
    (wide : a.occurrences≤2^W)
    (saved : ∀ i : Fin a.occurrences,(archive (a.direct+i.val)).val=
      if (tag) i=none then (credit) i else 0)
    (quiet : ∀j:I, ¬picked j → j∉liveRows raw post (C.layout ev).candidates)
    (quietTree : ∀j:I, ¬picked j → ∀ e, treeAt j e=0)
    (stock : ∀(j:I) (on:picked j) (i:Fin ng), (route j on).install.load
      ((route j on).bits ((chosen) j on)) (stockRow (p:=paid) i) =
        L.rowCredit j (fun o=>(tag) o=some (key i)))
    (billed : ∀(j:I) (on:picked j) (e:Fin paid), (route j on).install.load
      ((route j on).bits ((chosen) j on)) (paidRow (g:=ng) e) =
        L.rowCredit j (primaryHit a s stamp post archive e)+
        L.rowCredit j (secondaryHit a s mask mate post archive e)+treeAt j e)
    (trees : ∀e, tree.load archive e=∑j:I,treeAt j e)
    (stockDistinct : ∀i,G.tail i≠G.head i)
    (loopFree : ∀(j:I) (on:picked j) (e:Fin paid),P.tail e=P.head e →
      (route j on).install.load ((route j on).bits ((chosen) j on)) (paidRow (g:=ng) e)=0) :
    (∑j:I,(routeAt j).post (choice j)) =
      G.chordWidths (fun i=>OuterBank.resourceBits (tag) (credit) (key i))+
        P.chordWidths (fun e=>(fir).load archive e+(sec).load archive e+tree.load archive e) := by
  let width := fun (j:I) => (routeAt j).install.load ((routeAt j).bits (choice j))
  have held (i : Fin ng) : (∑j:I,width j (stockRow (p:=paid) i))=OuterBank.resourceBits (tag) (credit) (key i) := by
    refine Eq.trans ?_ (L.stock_rowCredit (key i))
    apply Finset.sum_congr rfl
    intro j _
    change (routeAt j).install.load ((routeAt j).bits (choice j)) _ = _
    rw [D.elected_load]
    by_cases on : picked j
    · rw [dite_eq_left on]
      exact stock j on i
    · rw [dite_eq_right on]
      exact (L.rowCredit_off j (quiet j on) (fun o => (tag) o = some (key i))).symm
  have printed (e : Fin paid) : (∑j:I,width j (paidRow (g:=ng) e))=
      (fir).load archive e+(sec).load archive e+tree.load archive e := by
    rw [primary_load a s stamp post archive e L wide saved,
      secondary_load a s mask mate post archive e L wide saved,trees,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change (routeAt j).install.load ((routeAt j).bits (choice j)) _ = _
    rw [D.elected_load]
    by_cases on : picked j
    · rw [dite_eq_left on]
      exact billed j on e
    · rw [dite_eq_right on]
      have first := L.rowCredit_off j (quiet j on) (primaryHit a s stamp post archive e)
      have second := L.rowCredit_off j (quiet j on) (secondaryHit a s mask mate post archive e)
      exact (congrArg₂ Nat.add (congrArg₂ Nat.add first second) (quietTree j on e)).symm
  apply sum_widths G P pad width _ _ held printed (fun i eq=>(stockDistinct i eq).elim)
  intro e equal
  rw [←printed e]
  apply Finset.sum_eq_zero
  intro j _
  change (routeAt j).install.load ((routeAt j).bits (choice j)) _=0
  rw [D.elected_load]
  by_cases on : picked j
  · rw [dite_eq_left on]
    exact loopFree j on e equal
  · simp only [dite_eq_right on]

end Hierarchy.WireTelescope.CalendarTape.HistogramFormat
end

end OAI
