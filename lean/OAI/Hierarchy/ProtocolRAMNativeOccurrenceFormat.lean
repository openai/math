import OAI.Hierarchy.ProtocolRAMNativeFormat
import OAI.Hierarchy.ProtocolRAMStockCommitPortSources
import OAI.Hierarchy.ProtocolRAMStockPortPlan

namespace OAI
/-! # Binding a physical padded occurrence to the actual native commit plan -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {w q d : ℕ}

/-- The selected-port indexing of the economic ledger is the actual RAM decoding
of an occurrence ordinal, for every stored histogram and every selector value. -/
def PortHeader.plan (h : PortHeader) (m : Memory w) (start goods limit : ℕ)
    (old reserve half price : Bank) (mode slot : Expr) (b : Batch q h.ports) (tabs : Fin h.ports → Fin q → Expr)
    (loaded : h.Loaded m) (dFit : h.ports≤2^w) (qFit : q≤2^w) (copyFit : b.copies<2^w) (sumFit : q*b.copies<2^w) :
    PortPlan (fresh (h.area start goods limit) (h.sources old reserve half price mode slot b tabs)) b m h.rows where
  enum := h.enum
  owner := h.owner
  data := h.parity
  dest := RepairHistogram.destination start goods slot
  ball := h.ballTerm
  field := h.fieldTerm
  tabs := tabs
  columns := rfl
  site := fun e => loaded.first e
  localIndex := fun e => by
    rw [show h.fieldTerm.eval m (e.val:Word w)=((e.val%h.ports:ℕ):Word w) from loaded.second e]
    exact Fin.val_cast_of_lt ((h.enum.symm e).2.isLt.trans_le dFit)
  portRoom := dFit
  termRoom := qFit
  copyRoom := copyFit
  sumRoom := sumFit

/-- The fresh seed copy preserves every word of the four upstream public input
columns. The same plan therefore applies to the true source of the charged commit. -/
theorem PortHeader.seed_loaded (h : PortHeader) (a : Area) (s : Sources) (m : Memory w) (old : h.Loaded m)
    (prior : h.stop≤a.start) : h.Loaded ((a.seed s).apply m) :=
  old.frame (fun x _ hx => a.seed_frame s m x (.inl (hx.trans_le prior)))

theorem PortHeader.directory (h : PortHeader) (m : Memory w) (start goods limit : ℕ)
    (old reserve half price : Bank) (mode slot : Expr) (b : Batch q h.ports) (tabs : Fin h.ports → Fin q → Expr)
    (loaded : h.Loaded m) :
    PairDirectory ((fresh (h.area start goods limit) (h.sources old reserve half price mode slot b tabs)).columns) m h.count :=
  ⟨loaded.pair.first,loaded.pair.second,loaded.pair.firstRow,loaded.pair.secondRow⟩

end Hierarchy.ProtocolRAM.Calendar.StockCommit

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage ProbeStage.Native PurchaseStage RepairHistogram StockCommit
open scoped Classical Fin.CommRing
variable {z d k q goods w : ℕ}

/-- Public enumeration installed by the strip layout: each ballot has one entry
for every local port. -/
def Format.occurrenceHeader (p : Format z d k q goods) (start : ℕ) : PortHeader :=
  ⟨start,p.market.rows,goods⟩

/-- Recompile the two histogram expressions from the finalized selector-mask
bank and row owner. The existing global-slot expression and wire tables retain
the physical local role and menu indexing. -/
def Format.withOccurrenceHeader (p : Format z d k q goods) (start : ℕ) : Format z d k q goods :=
  let h := p.occurrenceHeader start
  let s := p.sources
  { p with
    sources := h.sources s.old s.reserve s.half s.price s.mode s.slot
      (enabledBatch p.market.layout p.board) p.board.wire }

@[simp] theorem Format.withOccurrenceHeader_area (p : Format z d k q goods) (start : ℕ) :
    (p.withOccurrenceHeader start).pricedArea=p.pricedArea := rfl

@[simp] theorem Format.withOccurrenceHeader_market (p : Format z d k q goods) (start : ℕ) :
    (p.withOccurrenceHeader start).market=p.market := rfl

/-- A loaded physical header decodes the port and row of every occurrence in the
actual generated compact transfer. -/
def Format.occurrencePlan (p : Format z d k q goods) (start : ℕ) (m : Memory w)
    (occ : p.occurrences=(p.occurrenceHeader start).count)
    (loaded : (p.occurrenceHeader start).Loaded m) (dFit : goods≤2^w) (qFit : q≤2^w)
    (copyFit : p.histMass<2^w) (sumFit : q*p.histMass<2^w) :
    PortPlan (fresh p.pricedArea (p.withOccurrenceHeader start).stockSource)
      (enabledBatch p.market.layout p.board) m p.market.rows := by
  let h := p.occurrenceHeader start
  have area : p.pricedArea=h.area p.pricedArea.start p.pricedArea.goods p.pricedArea.limit :=
    congrArg (fun count : ℕ=>(⟨p.pricedArea.start,p.market.rows,count,p.pricedArea.goods,p.pricedArea.limit⟩ : Area)) occ
  rw [area]
  exact h.plan m p.pricedArea.start p.pricedArea.goods p.pricedArea.limit (p.withOccurrenceHeader start).stockSource.old p.sources.reserve p.sources.half
    p.sources.price (word p.board.modeOut) p.sources.slot (enabledBatch p.market.layout p.board) p.board.wire
    loaded dFit qFit copyFit sumFit

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
