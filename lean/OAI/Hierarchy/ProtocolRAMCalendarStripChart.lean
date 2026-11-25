import OAI.Hierarchy.ProtocolRAMNativeStripFormats
import OAI.Hierarchy.ProtocolRAMCalendarStripBuild
import OAI.Hierarchy.ProtocolRAMCalendarPortFormat
import OAI.Hierarchy.ProtocolRAMCalendarStripHeader
import OAI.Hierarchy.ProbeStripPortGeometry
import OAI.Hierarchy.ProtocolRAMCatalogueRows
import OAI.Hierarchy.ProtocolRAMCatalogueEdgeID

namespace OAI
/-! # The paid calendar instantiated with the two rooted strip programs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open PurchaseStage StripDirectory PortPadding
open scoped Classical Fin.CommRing
variable {z d k q depth r edges w : ℕ}

local notation "stripStages" => List.length (Fabric.shapes (permutationFabric z d))
local notation "P" => Fintype.card (PayloadRole stripStages k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R

variable (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

set_option maxHeartbeats 2000000 in
theorem capacity (s : Boards z d k q depth) (a : Attempt) (i j : ℕ) :
    (build F s a i).pricedArea=(build F s a j).pricedArea := by
  let base := build F s a j
  let layout (digits : ℕ) : StockCommit.Area :=
    let verdict := PostLayout.column base.maskStart base.indexBits base.market.rows (17+3*D+digits)
    {base.pricedArea with start:=verdict+1+base.occurrences}
  have placed (addr : ℕ) :
      (build F s a addr).pricedArea = layout (build F s a addr).batch.batch.quotes.length := by
    cases a <;> rfl
  rw [placed i,placed j]
  apply congrArg layout
  cases a with
  | outer p t =>
    change (List.ofFn (n:=Fintype.card (PayloadStrip.Quotes stripStages k)) _).length =
      (List.ofFn (n:=Fintype.card (PayloadStrip.Quotes stripStages k)) _).length
    simp only [List.length_ofFn]
  | inner p t l u =>
    change (List.ofFn (n:=Fintype.card (ChainStrip.Axes depth k)) _).length =
      (List.ofFn (n:=Fintype.card (ChainStrip.Axes depth k)) _).length
    simp only [List.length_ofFn]

theorem source (s : Boards z d k q depth) (a : Attempt) (i : ℕ) :
    (build F s a i).market.shelf.stockBase=i := by cases a <;> rfl

theorem live (c : Mesh) (arena : Arena) (initial : ℕ) (s : Boards z d k q depth)
    (a : Attempt) (i : Commodity (Fin (2^z)) stripStages k) :
    stockAt c arena (formats F c arena initial s) initial a i=
      ((formats F c arena initial s) a).market.shelf.stockBase+PurchaseInventory.slot i :=
  live_stock c arena initial (build F s) (fun a i => capacity F s a i initial) (source F s) a i

theorem candidate_count (c : Mesh) (arena : Arena) (initial : ℕ) (s : Boards z d k q depth) (a : Attempt) :
    ((formats F c arena initial s) a).market.rows=count z d k*paths z s.sampler.degree depth := by
  cases a <;> rfl

/-- The ballot's failed-word check reads its own row in the current physical
failed mask. It cannot borrow a positive failure word from another ballot. -/
theorem ballot_owner (c : Mesh) (arena : Arena) (initial : ℕ) (s : Boards z d k q depth) (a : Attempt) :
    ((formats F c arena initial s) a).board.batch.owner=.row := by cases a <;> rfl

theorem ballot_mask (c : Mesh) (arena : Arena) (initial : ℕ) (s : Boards z d k q depth) (a : Attempt) :
    let f := (formats F c arena initial s) a
    f.board.failedMIS=f.market.failures.bank := rfl

/-- The one-past-end ordinal is the native scatter's private disposable cell.
Inactive slots never address a physical edge. -/
def rawEdge (s : Boards z d k q depth) (edgeCount : ℕ) : Attempt → Fin D → Expr
  | .outer p a => extend (s.payloadEdge p a) (.lit edgeCount)
  | .inner p a j t => extend (s.purchaseEdge p a j t) (.lit edgeCount)

/-- The native occurrence header has exactly the rows in the format built for
this attempt, including its actual sampler degree and path depth. -/
theorem header_build (s : Boards z d k q depth) (a : Attempt) :
    header F s a = ⟨start s a,(build F s a 0).market.rows,D⟩ := by
  cases a <;> rfl

def edge (s : Boards z d k q depth) (edgeCount : ℕ) (a : Attempt) (i : Fin D) : Expr :=
  (rawEdge s edgeCount a i).atRow (header F s a).ballTerm

/-- A repair may use only its own parent trial's acquisition. Read the
actual mode-gated packed flag recorded by that true earlier event. A
payload trial has no purchased strip. -/
def retainedAt (s : Boards z d k q depth) : Attempt→Expr
  | .outer .. => .lit 0
  | .inner p a j t =>
    let origin:=build F s (.outer p a) 0
    let bank:Bank:=⟨origin.board.purchaseOut,ProtocolRAMPurchaseSampler.bits origin.market.rows⟩
    .lookup bank (header F s (.inner p a j t)).ballTerm

/-- Check the public raw ordinal against the immediately relevant purchase
receipt, without reading any later, still private event. -/
def physicalEdge (b : CatalogueRows.Board) (keep raw : Expr) : Expr :=
  .branch .lt raw (.lit b.coreRows) raw <|
    .branch .lt raw (.lit b.rows) (.branch .eq keep (.lit 0) (.lit b.rows) raw) (.lit b.rows)

def id (s : Boards z d k q depth) (catalogue : CatalogueRows.Board) (a : Attempt) (i : Fin D) : Expr :=
  .op .add (.lit catalogue.idBase)
    (physicalEdge catalogue (retainedAt F s a) (edge F s catalogue.rows a i))

/-- Once the actual parent receipt and the final bought-catalogue cell are
agreed at a live noncore candidate, the chronological and final physical
edge IDs coincide. Core and sentinel values require no retained flag. -/
theorem physicalEdge_agrees (b : CatalogueRows.Board) (keep raw : Expr) (m out : Memory w) (r r' : Word w)
    (same : raw.eval m r=raw.eval out r')
    (hit : (keep.eval m r=0) ↔
      ((b.bought.flag.atRow (.op .sub raw (.lit b.coreRows))).eval out r'=0)) :
    (physicalEdge b keep raw).eval m r=(b.checkedEdge raw).eval out r' := by
  simp only [physicalEdge,CatalogueRows.Board.checkedEdge,Expr.eval,same,
    ThreeFlat.RAM.DescriptorExpr.Comparison.test,
    decide_eq_true_eq,beq_iff_eq,Nat.cast_zero,hit]
  by_cases core : raw.eval out r' < (b.coreRows : Word w) <;>
    by_cases live : raw.eval out r' < (b.rows : Word w) <;> simp [core,live]


theorem payload_edge (s : Boards z d k q depth) (count : ℕ) (p a : ℕ) (i : Fin P) (m : Memory w) (u : Word w) :
    (edge F s count (.outer p a) (inject (Nat.le_max_left P R) i)).eval m u =
      (s.payloadEdge p a i).eval m ((header F s (.outer p a)).ballTerm.eval m u) := by
  simp [edge,rawEdge,eval_atRow]

theorem purchased_edge (s : Boards z d k q depth) (count : ℕ) (p a j t : ℕ) (i : Fin R) (m : Memory w) (u : Word w) :
    (edge F s count (.inner p a j t) (inject (Nat.le_max_right P R) i)).eval m u =
      (s.purchaseEdge p a j t i).eval m ((header F s (.inner p a j t)).ballTerm.eval m u) := by
  simp [edge,rawEdge,eval_atRow]

theorem actual_id (s : Boards z d k q depth) (catalogue : CatalogueRows.Board) (a : Attempt)
    (i : Fin D) (mem : Memory w) (row : Word w) :
    (id F s catalogue a i).eval mem row-(catalogue.idBase:Word w) =
      (physicalEdge catalogue (retainedAt F s a) (edge F s catalogue.rows a i)).eval mem row := by
  change (catalogue.idBase:Word w)+(physicalEdge catalogue (retainedAt F s a) (edge F s catalogue.rows a i)).eval mem row-(catalogue.idBase:Word w)=_
  abel


def chart (c : Mesh) (arena : Arena) (initial width cap : ℕ) (s : Boards z d k q depth)
    (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board) (r : ℕ)
    (banks : RouteSettlement.Banks) (source table destination : ℕ) (owners : Bank) :
    Chart (wordBits z d copies) q D :=
  let profiles := formats F c arena initial s
  pricedInstalled c finish prices profiles (feedColumns (N:=stripStages) c arena profiles initial width cap)
    (catalogue.sink r banks source table destination owners) catalogue.idBase
    (fun a => (header F s a).fieldTerm) (id F s catalogue)

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
