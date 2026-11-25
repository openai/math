import OAI.Hierarchy.ProbeFixedWirePaidChronology
import OAI.Hierarchy.ProtocolRAMDateSpillBilled
import OAI.Hierarchy.TaggedWireWideGoodsChange

namespace OAI
/-! # Original paid edges of one native attempt -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "order" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit

local notation "ownerBank" => sinkBank start cnt r (P).catalogue.rows
local notation "paidO" => v.catalystPairOwners P h width
local notation "paidP" => v.catalystPairParity P h width
local notation "floor" => (A).endAddress v.mesh
local notation "who" => v.nativeBoards P h width
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (P).catalogue.sink r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) ownerBank

local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride

local notation "rows" => (P).catalogue.rows
local notation "chk" => fun m=> checkedOut C floor m
local notation "memAt" => fun m j=> StockBound.state C m j
local notation "stamp" => fun a=>(f a).labelSource sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
  (StripChart.id F who (P).catalogue a)
local notation "regular" => fun a=> PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (stamp a)
local notation "secondary" => fun a u v'=> PaidWidths.paidMate (f a).pricedArea (f a).stockSource u v'
local notation "broadcasting" => fun (bits : ℕ) a=> PaidWidths.paidBroadcast (f a).pricedArea
  (tree a).positions (tree a).owner (tree a).parity (tree a).edge (tree a).sourceRow (f a).board.batch.copies bits

def AttemptPaidView (bits : ℕ) (π : Equiv.Perm (Fin (2^h))) (initial : Memory w) (charges : ℕ→Memory w) : Prop :=
  ∀t : Fin (es).length,∀a : Attempt,(es).get t=.attempt a→∀mask mate,(tree a).catalystMate=some (mask,mate)→
    let prior:=StockBound.state C initial t.val
    let next:=StockBound.state C initial (t.val+1)
    let ar:=(f a).pricedArea
    let stockSpill:=fun i : Commodity (Fin (2^h)) N k=>(next (ar.output+ar.goods+ar.goods+PurchaseInventory.slot i)).val
    let geometry:=((P).catalogue).coreMount π (siteNumber h D k) (v.wideOrder h width) next
    ∀e : Fin (P).catalogue.rows,
    v.wirePaidAt h width bits (t.val+1) next e=v.wirePaidAt h width bits t.val prior e+
      (regular a).load (charges t.val) e+(secondary a mask mate).load (charges t.val) e+
      (broadcasting bits a).load (charges t.val) e+routeLoad geometry.ordinary stockSpill e

def AttemptPaidComponents (bits : ℕ) (π : Equiv.Perm (Fin (2^h))) (initial : Memory w) : Prop :=
  v.AttemptPaidView h width bits π initial (fun t=>StockBound.state C initial (t+1))

theorem attempt_spill_after (π : Equiv.Perm (Fin (2^h))) (initial : Memory w)
    (active : Calendar.mounted C es initial) (word : floor<2^w)
    (native : v.WideSpillSource h width π (checkedOut C floor initial))
    (menu : Fintype.card (Actions N k)≤2^w) (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (edges : (P).catalogue.rows≤2^w) (t : Fin (es).length) (a : Attempt) (date : (es).get t=.attempt a)
    (e : Fin (P).catalogue.rows) :
    let now:=StockBound.state C initial (t.val+1)
    let ar:=(f a).pricedArea
    let path:=v.paidSpillPath P h width recipe route order a
    let walk:=v.spillPath P h π (v.wideOrder h width)
    (PaidWidths.paidSpill ar path.positions path.owner path.parity path.edge path.sourceRow).load now e=
      routeLoad walk (fun i=>(now (ar.output+ar.goods+ar.goods+PurchaseInventory.slot i)).val) e := by
  intro now ar path walk
  let stop:=checkedOut C floor initial
  let index:=v.nativeSlots P h width a
  obtain ⟨enum,edgeAt,ownerAt⟩:=v.spill_read P h width π (v.wideOrder h width) stop route native.1 recipe
    (fun z : Columns h D×Fin k=>(pairKeys (Columns h D) k z).val) native.2 menu goods edges paidO paidP a
  have low:=v.prior_paid_low h width initial active t (t.val+1) (Nat.lt_succ_self _) t.isLt
  rw [date] at low
  have fits:=(v.prior_spill_operands h width (.attempt a) (date ▸ (es).get_mem t) word).1 a
  have read : path.Reads now (fun j=>walk (index.symm j)) := by
    refine ⟨enum,fun i=>?_,fun i=>?_⟩
    · exact (congrArg Fin.val (PrefixAgreement.expr path.edge stop now _ (PrefixAgreement.inputEnd_of_fits _ fits.1)
        low (i.val:Word w))).symm.trans (edgeAt i)
    · exact (congrArg Fin.val (PrefixAgreement.expr path.sourceRow stop now _ (PrefixAgreement.inputEnd_of_fits _ fits.2)
        low (i.val:Word w))).symm.trans (ownerAt i)
  rw [path.spill_load ar now e _ read]
  let recorded:=fun j : Fin ar.goods=>(now (ar.output+ar.goods+ar.goods+j.val)).val
  let cost:=fun j : Fin ar.goods=>(walk (index.symm j)).count e*recorded j
  have changed:=index.sum_comp cost
  simpa only [routeLoad,cost,recorded,Equiv.symm_apply_apply,index, v.slot_index] using changed.symm

private theorem attempt_slices_at (bits : ℕ) (a : Attempt) (mask mate : Expr)
    (same : (tree a).catalystMate=some (mask,mate)) :
    let path:=v.paidSpillPath P h width recipe route order a
    v.wideEventSlices h width bits (.attempt a) =
      [regular a,secondary a mask mate,broadcasting bits a,
        PaidWidths.paidSpill (f a).pricedArea path.positions path.owner path.parity path.edge path.sourceRow] := by
  intro path
  change (f a).paidSlices sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
    (StripChart.id F who (P).catalogue a) (tree a) path bits=_
  simp [Format.paidSlices,Format.mateSlices,same]

/-- Every original paid row decomposes into direct, mate, selector tree and
all repeated ordinary spill traversals of that date on the immediate successor. -/
theorem wire_attempt_paid_components :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      ∀size,(arena).endAddress v.mesh≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) bits,
        v.AttemptPaidComponents h width bits π
          (v.wideSignedMidAt h width size paidStock v.radius π (wideRouteOrder h (2^v.W) k) raw) := by
  let : Nonempty (Fin k) := ⟨⟨0, v.positive⟩⟩
  filter_upwards [v.wide_wire_paid,v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight]
    with h past words arity age
  intro width small budget placed arena paidStock size extent π raw bits
  let initial:=v.wideSignedMidAt h width size paidStock v.radius π (wideRouteOrder h (2^v.W) k) raw
  have word:=(v.wide_stock_sizes h width age budget small).words.addresses
  have mounted':=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  have native:=(v.wide_spill_source h width size extent π raw word mounted').2
  intro t a date mask mate same prior next ar stockSpill geometry e
  have advance:=(past width small budget size extent π raw bits).2 t e
  rw [date] at advance
  have flow:=v.attempt_spill_after h width π initial mounted' word native words.1 words.2.1 (arity width).1.le t a date e
  rw [attempt_slices_at v h width bits a mask mate same] at advance
  calc
    _ = _ := advance
    _ = _ := by
      simp only [PaidWidths.total,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      change _=_+routeLoad (v.spillPath placed h π (v.wideOrder h width)) stockSpill e
      rw [flow]
      exact (show ∀a b c d e : ℕ, a+(b+(c+(d+e)))=a+b+c+d+e from
        fun a b c d e => by omega) _ _ _ _ _

/-- The three charged contributions are read from the reporting checkout.
The changing commodity and its excess still come from this attempt's
immediate chronological successor. -/
theorem wire_attempt_paid_checkout :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      ∀size,(arena).endAddress v.mesh≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) bits,
        let o:=wideRouteOrder h (2^v.W) k
        let mid:=v.wideSignedMidAt h width size paidStock v.radius π o raw
        let finalMem:=v.wideSignedCheckoutAt h width size paidStock v.radius π o raw
        v.AttemptPaidView h width bits π mid (fun _=>finalMem) := by
  filter_upwards [v.wire_attempt_paid_components,v.wide_elapsed_paid] with h components elapsed
  intro width small budget placed arena paidStock size extent π raw bits o mid finalMem t a date mask mate same
    prior next ar stockSpill geometry e
  have step:=components width small budget size extent π raw bits t a date mask mate same e
  have stable:=elapsed width small budget size extent π raw bits (t.val+1) t.isLt t (Nat.lt_succ_self _)
  rw [date] at stable
  rw [attempt_slices_at v h width bits a mask mate same] at stable
  have primary:=stable _ (List.mem_cons_self ..) e
  have paired:=stable _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) e
  have forest:=stable _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) e
  dsimp only at step
  rw [←primary,←paired,←forest]
  exact step

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
