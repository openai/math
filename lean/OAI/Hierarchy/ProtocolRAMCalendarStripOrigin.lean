import OAI.Hierarchy.ProbeFixedPhase
import OAI.Hierarchy.ProtocolRAMCalendarStripPorts
import OAI.Hierarchy.ProtocolRAMCalendarChargePages

namespace OAI
/-! # Native register and bank origins for the fixed, gated strip calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen
open StripDirectory CatalogueRows
open scoped Fin.CommRing Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}

private def blank : Bank := ⟨0,0⟩
private def zeroExpr : Expr := .lit 0
private def emptyBatch (letters ports : ℕ) : Batch letters ports :=
  ⟨0,1,0,[],blank,blank,blank,.row,fun _=>zeroExpr,fun _=>zeroExpr,fun _=>zeroExpr⟩

private def baseRepair (q n : ℕ) (bits limit : ℕ) (link : Link) (menu : Expr) : Repair q n where
  batch:=emptyBatch q n
  decisionBits:=bits
  tests:=⟨blank,⟨0,0,0,zeroExpr⟩,⟨0,0,0,zeroExpr⟩,⟨0,0,0,zeroExpr⟩,false,false⟩
  modeOut:=0
  failedMIS:=blank
  repairBits:=blank
  purchaseOut:=0
  boughtFields:=fun _=>0
  purchaseLink:=link
  purchaseMenu:=menu
  halfTable:=blank
  reserveOut:=fun _=>0
  feedOnAdvance:=false
  keys:=0
  tally:=0
  verdict:=0
  quoteOut:=0
  priceOut:=fun i=>i.val
  link:=link
  reportWidth:=fun _=>zeroExpr
  reportOut:=fun _=>0
  feedTable:=blank
  feedStride:=1
  mesh:=1
  reserve:=fun _=>zeroExpr
  wire:=fun _ _=>zeroExpr
  cap:=fun _=>limit
  stockOut:=fun _=>0

variable (v : FixedProtocolFormat F k p q Q σ Λ)

/-- Before the original physical writes, both branches already have their
actual market temperature, native threshold kind, stock cap, and scheduled
global cooling threshold. Address fields overwritten by the named layout
passes have a common initial zero value. -/
private def localOrigin (z letters digits ports width keyBase : ℕ) (a : Attempt) :
    StripDirectory.Boards z (2^v.W) k letters digits ports :=
  let phase:=v.basePhase width
  let deadline:=Calendar.deadline v.mesh v.finish phase a
  let n:=count z (2^v.W) k*paths z v.sampler.degree v.depth
  let stockBits:=ProtocolRAMPurchaseSampler.bits (PurchaseInventory.footprint z (publicStages v.W) k)
  let market : Market z (2^v.W) k :=
    ⟨v.sampler,v.depth,phase,probeHeat v.W,1,⟨0,0,0,0⟩,⟨0,0,n,zeroExpr,zeroExpr,0,0⟩⟩
  let t : StripTest digits:=⟨blank,1,fun _=>zeroExpr,zeroExpr,n,2^z,0,0,v.precision,v.toleranceAt⟩
  let ptr:=stratumHeader z (2^v.W) k v.sampler.degree v.depth keyBase
  let packet:=Expr.op .add (.lit 1) ptr.ballTerm
  let link : Link:=⟨zeroExpr,zeroExpr,zeroExpr,0,.lit 1⟩
  let baseline:=(v.W:ℝ)⁻¹^2*min (1/deadline.time) (1/(dyadicScale v.W)^8)
  let cap:=v.keepLimit*width
  ⟨market,baseRepair letters ports (ProtocolRAMPurchaseSampler.bits n) cap link packet,t,
    ⟨0,0,0,v.precision⟩,baseline,blank,blank,blank,blank,blank,⟨0,stockBits⟩,⟨0,stockBits⟩,blank,
    blank,.lit 0,(fun i=>i),0,0,0,0,cap⟩

/-- A concrete initial board, before finite public packet and port ROM
installation, for the actual cofinal scale. The only placement input is
the original public signed-stratum header base. -/
def originBoards (z width keyBase : ℕ) : Boards z (2^v.W) k 0 v.depth where
  sampler:=v.sampler
  positive:=v.positive
  radius:=v.radius
  radius_nonneg:=Nat.cast_nonneg _
  tolerance:=v.toleranceAt
  tolerance_pos:=v.geometry.cutoff.1
  tree:=fun a=>match a with | .outer ..=>v.cost.payload | .inner ..=>v.cost.purchase
  tree_nonneg:=fun a=>by cases a <;> first | exact v.cost.payload_nonneg | exact v.cost.purchase_nonneg
  minimum:=0
  outer:=fun p a=>localOrigin v z 0 _ _ width keyBase (.outer p a)
  inner:=fun p a j b=>localOrigin v z 0 _ _ width keyBase (.inner p a j b)
  stratumHeader:=fun _ _=>keyBase
  payloadEdge:=fun _ _ _=>zeroExpr
  purchaseEdge:=fun _ _ _ _ _=>zeroExpr

variable {z d letters depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

def reservedRole (b : Bank) : Option Expr→Expr
  | none=>.lit 0
  | some i=>.lookup b i

/-- The outer raw board uses the installed public zeros. A reserve trial
always observes the original outer purchase's saved half at the genuine
price-segment address. Every local role uses its actual geometric stock
coordinate; globally priced roles have no local reserve. -/
def withReserveSource (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z d k letters depth) (c : Mesh)
    (A : Arena) (initial : ℕ) (empty : Bank) : Boards z d k letters depth :=
  {s with
    outer:=fun p a=>
      let b:=s.outer p a
      {b with reserve:=empty,repair:={b.repair with
        reserve:=fun i=>reservedRole empty ((payloadChannels z N k).slot i)}}
    inner:=fun p a j t=>
      let b:=s.inner p a j t
      let parent:=formats F c A initial s (.outer p a)
      let held : Bank:=⟨parent.pricedArea.output+parent.pricedArea.goods,
        ProtocolRAMPurchaseSampler.bits (PurchaseInventory.footprint z N k)⟩
      let ports:=purchasedChannels (z:=z) (d:=d) (k:=k) (s.outer p a).market.shelf s.sampler depth (s.stratumHeader p a)
      {b with reserve:=held,repair:={b.repair with reserve:=fun i=>reservedRole held (ports.slot i)}}}

private theorem priced_reserve_congr {letters ports : ℕ} (b a : Format z d k letters ports)
    (mask : b.maskStart = a.maskStart) (bits : b.indexBits = a.indexBits)
    (rows : b.market.rows = a.market.rows) (occ : b.occurrences = a.occurrences)
    (goods : b.coordinates = a.coordinates) (quotes : b.batch.batch.quotes.length = a.batch.batch.quotes.length) :
    b.pricedArea.output + b.pricedArea.goods = a.pricedArea.output + a.pricedArea.goods := by
  let address (m i r o g n : ℕ) :=
    let area : StockCommit.Area := ⟨PostLayout.column m i r (17+3*ports+n)+1+o,r,o,g,0⟩
    area.output + area.goods
  change address b.maskStart b.indexBits b.market.rows b.occurrences b.coordinates b.batch.batch.quotes.length =
    address a.maskStart a.indexBits a.market.rows a.occurrences a.coordinates a.batch.batch.quotes.length
  rw [mask,bits,rows,occ,goods,quotes]

private theorem reserve_mask_congr {letters ports : ℕ} (b a : Format z d k letters ports)
    (flags : b.market.flags = a.market.flags) (rows : b.market.rows = a.market.rows)
    (excess : b.batch.tests.excess.rows = a.batch.tests.excess.rows)
    (payload : b.batch.tests.payload.rows = a.batch.tests.payload.rows)
    (failure : b.market.failures.rows = a.market.failures.rows) : b.maskStart = a.maskStart := by
  change b.market.flags+b.market.rows+1+(b.batch.tests.excess.rows+1)+(b.batch.tests.payload.rows+1)+
      (b.market.failures.rows+1) = a.market.flags+a.market.rows+1+(a.batch.tests.excess.rows+1)+
      (a.batch.tests.payload.rows+1)+(a.market.failures.rows+1)
  rw [flags,rows,excess,payload,failure]

set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
theorem reserve_parent (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z d k letters depth) (c : Mesh)
    (A : Arena) (initial : ℕ) (empty : Bank) (p a j t : ℕ) :
    let parent:=formats F c A initial (withReserveSource F s c A initial empty) (.outer p a)
    ((withReserveSource F s c A initial empty).inner p a j t).reserve.base =
      parent.pricedArea.output+parent.pricedArea.goods := by
  let v := withReserveSource F s c A initial empty
  let atOutput (area : StockCommit.Area) := area.output + area.goods
  change atOutput (liveFormats c A initial (build F s) (.outer p a)).pricedArea =
    atOutput (liveFormats c A initial (build F v) (.outer p a)).pricedArea
  have fixed (board : Boards z d k letters depth) :=
    live_area c A initial (build F board) (fun event addr => capacity F board event addr initial) (.outer p a)
  refine (congrArg atOutput (fixed s)).trans (Eq.trans ?_ (congrArg atOutput (fixed v)).symm)
  let before := build F s (.outer p a) initial
  let after := build F v (.outer p a) initial
  change atOutput before.pricedArea = atOutput after.pricedArea
  apply priced_reserve_congr before after
  · exact reserve_mask_congr before after rfl rfl rfl rfl rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change (List.ofFn (n:=Fintype.card (PayloadStrip.Quotes N k)) _).length =
      (List.ofFn (n:=Fintype.card (PayloadStrip.Quotes N k)) _).length
    simp only [List.length_ofFn]

/-- Both authoritative stock operands in the installed sparse ledger refer
to their chronological producer, even after post-layout selector rebinding. -/
theorem source_banks (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z d k letters depth) (c : Mesh)
    (A : Arena) (initial : ℕ) (empty : Bank) (a : Attempt) :
    let v:=withReserveSource F s c A initial empty
    let f:=formats F c A initial v
    (f a).stockSource.old.base=previousStock c initial (publishedStock c A f) (.attempt a) ∧
    (f a).stockSource.reserve.base=(match a with
      | .outer .. => empty.base
      | .inner p h _ _ => (f (.outer p h)).pricedArea.output+(f (.outer p h)).pricedArea.goods) := by
  dsimp only
  let v:=withReserveSource F s c A initial empty
  constructor
  · change (liveFormats c A initial (build F v) a).market.shelf.stockBase =
      previousStock c initial (publishedStock c A (liveFormats c A initial (build F v))) (.attempt a)
    rw [live_published c A initial (build F v) (fun a addr=>capacity F v a addr initial)]
    exact source F v a _
  · cases a with
    | outer p h => rfl
    | inner p h j t => exact reserve_parent F s c A initial empty p h j t

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
