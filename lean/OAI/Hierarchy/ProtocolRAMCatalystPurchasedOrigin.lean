import OAI.Hierarchy.ProtocolRAMCatalystPurchasedBirth
import OAI.Hierarchy.ProtocolRAMCatalystBirthArchive
import OAI.Hierarchy.ProtocolRAMNativeStripFormats
import OAI.Hierarchy.ProtocolRAMCalendarStripPortBanks
import OAI.Hierarchy.ProbePurchaseArchiveOrigin
import OAI.Hierarchy.ProtocolRAMCoreCatalogueOperands
import OAI.Hierarchy.ProtocolRAMPurchaseCalendarROM

namespace OAI
/-! # The original frozen shelf at the actual entry of a purchased date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen StripDirectory CatalystArchive
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z d k q goods w r edges : ℕ}

/-- Run the actual outer sampler at its frozen price. Its tile and flag
words become the birth shelf in the subsequent dated signed-cash receipt. -/
theorem priced_purchase_entry (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (F : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (initial : Shelf.Mem z d)
    (p a j t start : ℕ) (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z d) (arena : Arena) :
    let C := pricedInstalled c finish prices F feeds sink idBase role ids
    let event := Attempt.outer p a
    let v := (F event).atTime c finish prices event
    let frozen := v.failures.pass.apply ((guard C event).apply (trialState C initial p a))
    let keys := stratumHeader z d k v.sampler.degree v.depth start
    mounted C (events c) initial → p<c.inject+c.cool → a<c.outerFuel → j<c.reserveSteps → t<c.innerFuel →
    v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
    (∀i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
    keys.stop≤v.shelf.firstBase → keys.Loaded frozen →
    v.shelf.flagsBase v.sampler z d k v.depth+v.rows ≤ arena.base c (.attempt event)+arena.stride →
    (∀e x,x<arena.base c e→protected C x e) →
    ArchiveReads v.shelf v.sampler π v.depth start v.phase v.temperature v.kind frozen
      (entryMemory C initial (.inner p a j t)) k := by
  intro C event v frozen keys whole hp ha hj ht inc prep head loaded alloc floor
  have ready := outer_head_ready whole hp ha
  have market : v.ready ((guard C event).apply (trialState C initial p a)) := ready.2.1
  have saved := priced_purchase_archive c finish prices F feeds sink idBase role ids initial p a start π fixture
    ready inc prep head loaded
  exact purchased_entry_archive C initial arena p a j t saved whole hp ha hj ht market.2.2.1 head alloc floor


namespace StripChart

section Birth
open CatalogueRows CoreBoard
variable {W depth : ℕ}
local notation "N" => Stages z (2^W)
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))

/-- Select the original market's actual incoming stock and closed deadline
from the static calendar before running its sampler. -/
def pricedBirth (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : StripChart.Boards z (2^W) k q depth)
    (c : Mesh) (b : CatalogueRows.Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
    (arena : Arena) (initialStock : ℕ) (finish : ℝ) (fees : PhasePrice)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin D→Expr) (initial : Shelf.Mem z (2^W))
    (p a j t : ℕ) (π : Equiv.Perm (Fin (2^z))) (fixture : Shelf.Mem z (2^W)) :
    let forms := formats F c arena initialStock (withPorts s c b G)
    let C := pricedInstalled c finish fees forms feeds sink idBase role ids
    let ev := Attempt.outer p a
    let v := (forms ev).atTime c finish fees ev
    let frozen := v.failures.pass.apply ((guard C ev).apply (trialState C initial p a))
    let h := stratumHeader z (2^W) k s.sampler.degree depth (s.stratumHeader p a)
    mounted C (events c) initial → p<c.inject+c.cool → a<c.outerFuel → j<c.reserveSteps → t<c.innerFuel →
    v.shelf.Incoming (k:=k) s.sampler π depth v.phase v.temperature v.kind frozen →
    (∀i : Key z (2^W) k,v.shelf.Prepared s.sampler depth fixture i frozen) →
    h.stop≤v.shelf.firstBase → h.Loaded frozen →
    v.shelf.flagsBase s.sampler z (2^W) k depth+v.rows≤arena.base c (.attempt ev)+arena.stride →
    (∀e y,y<arena.base c e→protected C y e) →
    PurchasedBirth (s.outer p a).market.shelf s.sampler π depth (s.stratumHeader p a)
      (entryMemory C initial (.inner p a j t)) k := by
  intro forms C ev v frozen h whole hp ha hj ht incoming prepared keys loaded allocated floor
  let stock := resolvedStock c arena initialStock (build F (withPorts s c b G)) ev
  exact ⟨stock,v.phase,v.temperature,v.kind,frozen,
    priced_purchase_entry c finish fees forms feeds sink idBase role ids initial p a j t (s.stratumHeader p a)
      π fixture arena whole hp ha hj ht incoming prepared keys loaded allocated floor⟩


/-- The installed prefix already supplies the sampler fixture and table.
The public permutation geometry identifies its original CT rows, without
selecting a permutation or sampler witness as input to the date. -/
def pricedBirthFromBoard (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : StripChart.Boards z (2^W) k q depth)
    (c : Mesh) (b : CatalogueRows.Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
    (arena : Arena) (initialStock : ℕ) (finish : ℝ) (fees : PhasePrice)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin D→Expr) (initial : Shelf.Mem z (2^W))
    (p a j t : ℕ) (π : Equiv.Perm (Fin (2^z))) :
    let forms := formats F c arena initialStock (withPorts s c b G)
    let C := pricedInstalled c finish fees forms feeds sink idBase role ids
    let ev := Attempt.outer p a
    let v := (forms ev).atTime c finish fees ev
    let h := stratumHeader z (2^W) k s.sampler.degree depth (s.stratumHeader p a)
    let origin := entryMemory C initial ev
    mounted C (events c) initial → p<c.inject+c.cool → a<c.outerFuel → j<c.reserveSteps → t<c.innerFuel →
    CoreCatalogue.Geometry π origin (2^W) → h.Loaded origin →
    max (heapEnd z (2^W) copies) h.stop ≤ min (C.stopAt ev) v.failures.base →
    h.stop≤v.shelf.firstBase →
    v.shelf.flagsBase s.sampler z (2^W) k depth+v.rows≤arena.base c (.attempt ev)+arena.stride →
    (∀e y,y<arena.base c e→protected C y e) →
    PurchasedBirth (s.outer p a).market.shelf s.sampler π depth (s.stratumHeader p a)
      (entryMemory C initial (.inner p a j t)) k := by
  intro forms C ev v h origin whole hp ha hj ht measured header low keys allocated floor
  let state := trialState C initial p a
  let input := (guard C ev).apply state
  let frozen := v.failures.pass.apply input
  have slot := (outer_slot C initial p a hp ha whole).choose_spec
  have time : origin=state := slot.entryMemory
  have keep (x : ℕ) (lt : x< max (heapEnd z (2^W) copies) h.stop) : frozen x=origin x := by
    have early := lt.trans_le low
    have guardLow := early.trans_le (min_le_left _ _)
    have failureLow := early.trans_le (min_le_right _ _)
    change image v.failures.base v.failures.rows _ input x=origin x
    rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl failureLow),time]
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl guardLow)
  have original : Shelf.Geometry π origin :=
    fun site => ⟨(PurchaseCT.groupNumber site).toEmbedding,measured site⟩
  have geom := Shelf.geometry_of_frame π origin frozen original (fun x hx=>keep x (hx.trans_le (le_max_left _ _)))
  have loaded : h.Loaded frozen := header.frame (fun x _ hi=>keep x (hi.trans_le (le_max_right _ _)))
  have ready : v.ready input := slot.currentReady.2.1
  let fixture := Classical.choose (Classical.choose_spec ready.2.2.2.2)
  have sample := Classical.choose_spec (Classical.choose_spec ready.2.2.2.2)
  have incoming : v.shelf.Incoming (k:=k) s.sampler π depth v.phase v.temperature v.kind frozen :=
    ⟨sample.1.dimensions,(fun i => by
      obtain ⟨enc, measuredRows⟩ := geom (stage i)
      exact ⟨enc, ⟨measuredRows.group, measuredRows.input, measuredRows.output⟩⟩),sample.1.table,sample.1.bankEnd,sample.1.stockEnd,sample.1.afterCT⟩
  exact pricedBirth F s c b G arena initialStock finish fees feeds sink idBase role ids initial p a j t π fixture
    whole hp ha hj ht incoming sample.2 keys loaded allocated floor

end Birth
end StripChart
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
