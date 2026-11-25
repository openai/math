import OAI.Hierarchy.ProtocolRAMCalendarStripHeader
import OAI.Hierarchy.ProtocolRAMPortPadding
import OAI.Hierarchy.ProbeStripPortDestination
import OAI.Hierarchy.ProtocolRAMNativeOccurrenceFormat

namespace OAI
/-! # Compiling payload and purchased strips on the same physical occurrence board -/

namespace Hierarchy.ProtocolRAM.PortPadding
open Computability.VPVNP.BurstRAM PrivateRAM
open PurchaseStage Calendar
open scoped Classical Fin.CommRing
noncomputable section
variable {w z d k q n p r D : ℕ}

/-- Port-indexed fields of the native postprocessing procedure are expanded.
The chronological placer assigns the new stock, reserve and verdict addresses
using the expanded board's actual number of columns. -/
def repair (D : ℕ) (b : Repair q n) : Repair q D where
  batch := batch D b.batch
  decisionBits := b.decisionBits
  tests := b.tests
  modeOut := b.modeOut
  failedMIS := b.failedMIS
  repairBits := b.repairBits
  purchaseOut := b.purchaseOut
  boughtFields := b.boughtFields
  purchaseLink := b.purchaseLink
  purchaseMenu := b.purchaseMenu
  halfTable := b.halfTable
  reserveOut := extend b.reserveOut 0
  feedOnAdvance := b.feedOnAdvance
  keys := b.keys
  tally := b.tally
  verdict := b.verdict
  quoteOut := b.quoteOut
  priceOut := b.priceOut
  link := b.link
  reportWidth := b.reportWidth
  reportOut := b.reportOut
  feedTable := b.feedTable
  feedStride := b.feedStride
  mesh := b.mesh
  reserve := extend b.reserve (.lit 0)
  wire := extend b.wire (fun _ => .lit 0)
  cap := extend b.cap 0
  stockOut := extend b.stockOut 0

/-- Rebuild the flattened (ball,role) directory for the common native stride.
Real destinations use their original typed address expression; padding writes
zero to the private cash sentinel. The active mask and every destination pass
are constructed for the final placed board. -/
def format (D start : ℕ) (slot : Fin n → Option Expr) (s : Format z d k q n) : Format z d k q D :=
  let h : StockCommit.PortHeader := ⟨start,s.market.rows,D⟩
  let src := {s.sources with slot := StripDirectory.destination h s.coordinates (extend slot none)}
  let padded : Format z d k q D :=
    ⟨s.market,repair D s.batch,s.histMass,s.indexBits,src,h.count,s.coordinates,s.limit⟩
  padded.withOccurrenceHeader start

theorem real_slot (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr)
    (bound : n ≤ D) (m : Memory w) (row : Word w) (i : Fin n) (fit : D ≤ 2^w) :
    let h : StockCommit.PortHeader := ⟨start,s.market.rows,D⟩
    (h.fieldTerm.eval m row).val=i.val →
      ((format D start slot s).sources.slot.eval m row)=(slot i |>.getD (.lit s.coordinates)).eval m
        (h.ballTerm.eval m row) := by
  intro h hit
  change (StripDirectory.destination h s.coordinates (extend slot none)).eval m row = _
  simpa only [extend_real] using
    StripDirectory.destination_read h s.coordinates (extend slot none) m row (inject bound i) fit hit

theorem tail_slot (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr)
    (m : Memory w) (row : Word w) (i : Fin D) (hi : n ≤ i.val) (fit : D ≤ 2^w) :
    let h : StockCommit.PortHeader := ⟨start,s.market.rows,D⟩
    (h.fieldTerm.eval m row).val=i.val →
      ((format D start slot s).sources.slot.eval m row)=(s.coordinates : Word w) := by
  intro h hit
  change (StripDirectory.destination h s.coordinates (extend slot none)).eval m row = _
  simpa only [extend_tail _ _ _ hi,Option.getD_none,Expr.eval] using
    StripDirectory.destination_read h s.coordinates (extend slot none) m row i fit hit

/-- The checked, physically placed policy reads the identical failed-root word
on the two local boards. Padding introduces no additional selector words. -/
theorem enabled (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr) :
    enabledBatch s.market.layout (format D start slot s).board =
      batch D (enabledBatch s.market.layout s.board) := rfl

theorem placed_wire (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr) :
    (format D start slot s).board.wire = extend s.board.wire (fun _ => .lit 0) := rfl

theorem admitted (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr)
    (bound : n ≤ D) (m : Memory w) (row : Word w) (fits : s.batch.batch.maxWidth<2^w) :
    (enabledBatch s.market.layout (format D start slot s).board).valid m row ↔
      (enabledBatch s.market.layout s.board).valid m row := by
  rw [enabled]
  exact valid _ m row bound fits

theorem placed_debit (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr)
    (bound : n ≤ D) (m : Memory w) (row : Word w) (fits : s.batch.batch.maxWidth<2^w)
    (qFit : q≤2^w) (copyFit : s.histMass<2^w) (sumFit : q*s.histMass<2^w) (i : Fin D) :
    (RepairHistogram.debit (enabledBatch s.market.layout (format D start slot s).board) i).eval m row =
      extend (fun j => (RepairHistogram.debit (enabledBatch s.market.layout s.board) j).eval m row) 0 i := by
  rw [enabled]
  exact debit (enabledBatch s.market.layout s.board) m row bound fits qFit copyFit sumFit i

theorem placed_credit (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr)
    (bound : n ≤ D) (m : Memory w) (row : Word w) (fits : s.batch.batch.maxWidth<2^w)
    (qFit : q≤2^w) (copyFit : s.histMass<2^w) (sumFit : q*s.histMass<2^w) (i : Fin D) :
    ((enabledBatch s.market.layout (format D start slot s).board).wire ((format D start slot s).board.wire i)).eval m row =
      extend (fun j => ((enabledBatch s.market.layout s.board).wire (s.board.wire j)).eval m row) 0 i := by
  rw [enabled,placed_wire]
  exact wire (enabledBatch s.market.layout s.board) m row bound fits qFit copyFit sumFit s.board.wire i

/-- Each signed scatter record of the recompiled board reads the ballot and role
from the mounted rectangular directory, including records past the last true role. -/
def occurrencePlan (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr)
    (m : Memory w) (loaded : (⟨start,s.market.rows,D⟩ : StockCommit.PortHeader).Loaded m)
    (fit : D≤2^w) (qFit : q≤2^w) (copyFit : s.histMass<2^w) (sumFit : q*s.histMass<2^w) :
    let f := format D start slot s
    StockCommit.PortPlan (StockCommit.fresh f.pricedArea f.stockSource)
      (enabledBatch s.market.layout f.board) m s.market.rows :=
  (format D start slot s).occurrencePlan start m rfl loaded fit qFit copyFit sumFit

/-- Both branches share the same executable job type, including its complete
physical pass list. Each branch carries its own genuine incidence expressions. -/
inductive Geometry (z d k q p r : ℕ) where
  | payload (build : ℕ → Format z d k q p) (slot : Fin p → Option Expr)
  | purchased (build : ℕ → Format z d k q r) (slot : Fin r → Option Expr)

def Geometry.build (start active : ℕ) : Geometry z d k q p r → Format z d k q (max p r)
  | .payload source slot => format (max p r) start slot (source active)
  | .purchased source slot => format (max p r) start slot (source active)

theorem occurrence_count (s : Format z d k q n) (start : ℕ) (slot : Fin n → Option Expr) :
    (format D start slot s).occurrences=s.market.rows*D := rfl

end
end Hierarchy.ProtocolRAM.PortPadding

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen PurchaseStage
open scoped Classical

variable {z d k q : ℕ}

def Boards.build {digits ports : ℕ} (B : Boards z d k q digits ports)
    (make : Calendar.Market z d k→Repair q ports→StripTest digits→ Calendar.GlobalTests.Layout→ℝ→
      Bank→Bank→Bank→Bank→Bank→Bank→Bank→Bank→Bank→Expr→Expr→(ℕ→ℕ)→
      ℕ→ℕ→ℕ→ℕ→ℕ→ Calendar.Format z d k q ports) (active : ℕ) :=
  make {B.market with shelf:={B.market.shelf with stockBase:=active}}
    B.repair B.test B.globalTests B.baseline B.price B.terms B.menu B.enabled B.selectors
    B.old B.reserve B.half B.cash .row B.report B.priceOut B.copies B.maxWidth B.start B.indexBits B.limit

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
