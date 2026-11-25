import OAI.Hierarchy.ProtocolRAMCalendarStripPublicROM
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceHistory

namespace OAI
/-! # The padded paid strip calendar makes no histogram updates at an actual purchase -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage
open ThreeFlat.RAM
open StripDirectory PortPadding StockCommit RepairHistogram
open scoped Fin.CommRing
variable {z d k q depth : ℕ}
local notation "stripStages" => List.length (Fabric.shapes (permutationFabric z d))
local notation "D" => max (Fintype.card (PayloadRole stripStages k)) (Fintype.card (PurchasedRole depth k))
local notation "W" => wordBits z d copies
variable (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

omit [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)] in
private theorem sealed_header {ports : ℕ} (profile : Format z d k q ports) (start : ℕ) :
    (profile.withOccurrenceHeader start).withOccurrenceHeader start=profile.withOccurrenceHeader start := rfl

omit [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)] in
private theorem sealed_geometry {p t : ℕ} (g : PortPadding.Geometry z d k q p t) (start active : ℕ) :
    (g.build start active).withOccurrenceHeader start=g.build start active := by
  cases g <;> exact sealed_header _ _

theorem occurrence_sealed (s : Boards z d k q depth) (c : Mesh) (arena : Arena) (initial : ℕ) (x : Attempt) :
    let f := formats F c arena initial s x
    f.withOccurrenceHeader (start s x)=f :=
  sealed_geometry (shape F s x) (start s x) (resolvedStock c arena initial (build F s) x)

omit [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)] in
private theorem sealed_buy_idle {goods simEdges totalEdges : ℕ} (c : Mesh) (finish : ℝ) (price : PhasePrice)
    (profiles : Attempt → Format z d k q goods) (headerStart : Attempt → ℕ)
    (fixedHeader : ∀ y,(profiles y).withOccurrenceHeader (headerStart y)=profiles y)
    (feeds : Boundary → List CommodityColumn) (sink : Sink simEdges totalEdges)
    (idBase : ℕ) (role : Attempt → Expr) (ids : Attempt → Fin goods → Expr)
    (m : Memory W) (p a : ℕ) :
    let x := Attempt.outer p a
    let f := profiles x
    let C := pricedInstalled c finish price profiles feeds sink idBase role ids
    let out := postOutput (C.layout x) (repair C x) (prepared C x (trialState C m p a))
    let g := f.labelSource sink idBase (role x) (ids x)
    ready C (.attempt x) (trialState C m p a) → observedMode C m p a=3 →
    4≤2^W → f.market.rows≤2^f.indexBits → f.occurrences=(f.occurrenceHeader (headerStart x)).count →
    (f.occurrenceHeader (headerStart x)).Loaded out → (f.occurrenceHeader (headerStart x)).stop≤g.out →
    goods≤2^W → q≤2^W → f.histMass<2^W → q*f.histMass<2^W →
    ∀ e : Fin f.occurrences,delta (f.pricedArea.columns f.stockSource)
      ((f.pricedArea.seed f.stockSource).apply ((g.pass f.occurrences).apply out)) e=0 := by
  have active := occurrence_buy_idle c finish price profiles headerStart feeds sink idBase role ids m p a
  have fixed : (fun y=>(profiles y).withOccurrenceHeader (headerStart y))=profiles := funext fixedHeader
  dsimp only [] at active
  rw [fixed,fixedHeader (.outer p a)] at active
  exact active

set_option maxHeartbeats 1600000 in
theorem buy_idle (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh) (arena : Arena)
    (finish : ℝ) (price : PhasePrice) (catalogue : CatalogueRows.Board) (r : ℕ)
    (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank) (p a : ℕ) (m : Memory W) :
    let cfg := withPublicROM s b c finish price
    let ps := portTable s (JointHeader.stop b z stripStages k (DeadlineROM.count c))
    let x := Attempt.outer p a
    let C := chart F c arena b.initial b.width b.cap cfg finish price catalogue r banks src tbl dst owners
    let f := formats F c arena b.initial cfg x
    let B := repair C x
    let out := postOutput (C.layout x) B (prepared C x (trialState C m p a))
    let g := f.labelSource (catalogue.sink r banks src tbl dst owners) catalogue.idBase
      (header F cfg x).fieldTerm (id F cfg catalogue x)
    mounted C (events c) m → p<c.inject+c.cool → a<c.outerFuel → observedMode C m p a=3 →
    (ps.header 0).Loaded m → ps.stop≤arena.first →
    (∀ e u,u<arena.base c e→protected C u e) →
    ps.stop≤g.out → f.market.rows≤2^f.indexBits →
    D≤2^W → q≤2^W → f.histMass<2^W → q*f.histMass<2^W →
    ∀ e : Fin f.occurrences,delta (f.pricedArea.columns f.stockSource)
      ((f.pricedArea.seed f.stockSource).apply ((g.pass f.occurrences).apply out)) e=0 := by
  intro cfg ps x C f B out g whole hp ha buy loaded fits floor head padded dFit qFit copyFit sumFit
  have h := shared_header F s b c finish price x
  have same := (shape_header F cfg c arena b.initial x).1.trans h
  have occ := (shape_header F cfg c arena b.initial x).2.trans (congrArg PortHeader.count h)
  have raw := Boot.ports_before_purchase C arena m (ps.header 0) p a whole hp ha
    ((ps.end_le 0).trans fits) floor loaded
  have live : (f.occurrenceHeader (start cfg x)).Loaded out := by
    rw [same]
    exact raw
  have late : (f.occurrenceHeader (start cfg x)).stop≤g.out := by
    rw [same]
    exact (ps.end_le 0).trans head
  have sites : f.occurrences=(f.occurrenceHeader (start cfg x)).count := occ.trans (congrArg PortHeader.count same).symm
  have wide : 4≤2^W := calc
    4 = 2^2 := by decide
    _ ≤ 2^W := Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega)
  have run := outer_head_ready (C:=C) (mem:=m) (p:=p) (h:=a) whole hp ha
  exact sealed_buy_idle c finish price (formats F c arena b.initial cfg) (start cfg)
    (occurrence_sealed F cfg c arena b.initial)
    (feedColumns (N:=stripStages) c arena (formats F c arena b.initial cfg) b.initial b.width b.cap)
    (catalogue.sink r banks src tbl dst owners) catalogue.idBase
    (fun y=>(header F cfg y).fieldTerm) (id F cfg catalogue) m p a
    run buy wide padded sites live late dFit qFit copyFit sumFit

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
