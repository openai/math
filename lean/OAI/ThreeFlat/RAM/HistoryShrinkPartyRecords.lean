import OAI.ThreeFlat.RAM.HistoryShrinkBatchRecords

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression Diagonal Diagonal.PhysicalStage
open Diagonal.CompressorPacking Diagonal.CompressorPacking.PhysicalShrink
open Diagonal.CompressorPacking.Native Diagonal.CompressorPacking.Native.ShrinkStage
open Diagonal.NavigationDirectory Diagonal.NavigationPass Diagonal.ShrinkStageNav
open HistoryStageBody.Physical HistoryGatherBody

open scoped Fin.NatCast in
private abbrev gatherIncidentWord (w n : ℕ) : Word w := (n : Word w)

open scoped Classical BigOperators Fin.CommRing

private theorem recordedGatherKey {w : ℕ} (n : ℕ) {value : Word w}
    (h : value = (n : Word w)) : value = gatherIncidentWord w n :=
  h.trans (by rfl)

noncomputable section


open Diagonal.CompressorPacking.Native.ShrinkStage.Resident HistoryMotifJoin

section PublishedParty
open private colors_le from OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
variable {F : Type} [Field F] [Fintype F] (B : Block F) (s D rem : ℕ) (hD : 0<D)
  (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "T₀" => B.shrink
local notation "M₀" => shrinkBinary T₀ s D rem hD small A
local notation "B₀" => shrinkRecordState s rem A
local notation "N₀" => Fintype.card (B₀).Base
local notation "P₀" => shrinkRecordPacking s rem A
local notation "d₀" => (2^s:ℕ)
local notation "hc₀" => colors_le s
local notation "S₀" => shrinkStage s D
local notation "t₀" => Diagonal.CompressorPacking.tagBits d₀
local notation "x₀" => dims S₀ N₀ t₀ rem
variable {W K : ℕ} (cur ctr : Word W) (before issued final post : Memory W) (c : Cursor) (branch : Fin (shrinkBinary B.shrink s D rem hD small A).rules.count)
local notation "issuedWords" => shrinkIssuedWords T₀ s D rem hD small A branch
local notation "lay₀" => ShrinkMotif.chooseWidths issuedWords
local notation "en₀" => allocate K c (.shrink x₀)
local notation "f₀" => DescriptorSpan.fields K c x₀ lay₀
variable (hdr : ℕ) (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved : let x := Resident.dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base)
                         (Diagonal.CompressorPacking.tagBits (2^s)) rem
             let next := (allocate K c (.shrink x)).next
             SavedFrame cur ctr hdr next.header next.heap issued final)
    (site : Computability.VPVNP.Compression.Site (shrinkRecordState s rem A).Base
      (BitWord (Diagonal.CompressorPacking.tagBits (2^s))) (BitWord rem))
    (O : Incidents.SiteOrder (S:=shrinkStage s D) (shrinkRecordPacking s rem A)
      (shrinkRecordState s rem A).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) site W)
    (slot : Fin (Incidents.siteKeys (S:=shrinkStage s D) (w:=W) (shrinkRecordPacking s rem A) (shrinkRecordState s rem A).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) site).length)
local notation "m₀" => (O.equiv slot).val
local notation "prior" => shrinkRecordWidth s rem A
local notation "du" => PhysicalShrink.b P₀ prior (shrinkRecordCode s rem A) hc₀
local notation "bestIndex" => RefreshDemandRows.tileNumber (du m₀) ((T₀).base ∘ (T₀).row)
local notation "ordinal" => (shrinkRecordOrder s rem A m₀).val
local notation "baseRow" => f₀ 36+6*(Incidents.capacity S₀*Incidents.siteNumber (B₀).order site+slot.val)

open private publishedIncidentRow from OAI.ThreeFlat.RAM.HistoryShrinkIncidentRecords

variable (J : HistoryGatherBody.Layout)
    (oldCaps : ShrinkOldCaps s rem W) (baseFit : Fintype.card (shrinkRecordState s rem A).Base≤2^W) (wide : 8≤W)
    (capFits : Incidents.capacity (shrinkStage s D)<2^W) (offset : 0<c.width)
    (rowPtr : let widths := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
              (selected J post).incident=(publishedIncidentRow K c s D rem A widths site slot.val : Word W))
    (apart : let widths := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
             let row := publishedIncidentRow K c s D rem A widths site slot.val
             ∀j:Fin 6,row+j.val≠cur.val ∧ row+j.val≠ctr.val ∧ hdr≤row+j.val)
    (preserved : let widths := ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)
                 let row := publishedIncidentRow K c s D rem A widths site slot.val
                 ∀j:Fin 6,post (row+j.val)=final (row+j.val))

local notation "siteNo" => Incidents.siteNumber (B₀).order site
local notation "kernelBase" => f₀ 34+5*siteNo

local notation "G₀" => shrinkGrid B
variable {height start : ℕ} {pre tail : List (Grid F)} (level : Fin B.levels)
    (mounted : Mounted B height W start post) (stage : grids B=pre++shrinkGrid B level::tail)
local notation "g₀" => (shrinkGrid B level).family (Mounted.base B height start pre)

local notation "tileAt" => shrinkRecordTile T₀ s rem A m₀
local notation "baseAt" => PhysicalShrink.widths T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀
local notation "dp" j => (Fintype.equivFin (demandGraph.Port j)).symm
local notation "sp" j => (Fintype.equivFin (supplyGraph.Port j)).symm

open HistoryPartyBatchExec HistoryPartySpecialization
open Resident

open Diagonal.MotifOuterTerms Diagonal.HistogramTileNetwork Diagonal.MotifKernel
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryRefreshEmitter LinearAlgebra.SpectralBooks
open private selected_bundle_positive from OAI.ThreeFlat.Diagonal.ShrinkSelectedGeometry
open private copiesPositive selectedSiteDecidableEq from OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply
attribute [local instance 2000] selectedSiteDecidableEq
local instance (priority := 2000) recordedBaseDecidableEq :
    DecidableEq (shrinkRecordState s rem A).Base := Classical.decEq _
local notation "rawCode" => Demand.key P₀ (baseNat (B₀).order)
local notation "numbers" => motifNumbers P₀ rawCode hc₀
local notation "chosen" => PhysicalShrink.widths T₀ P₀ prior (shrinkRecordCode s rem A) hc₀
local notation "many" => shrinkRecordCopies T₀ s rem A
local notation "tiles" => shrinkRecordTile T₀ s rem A
local notation "hist" => shrinkIssuedBranch T₀ s D rem hD small A branch
local notation "good" => Ordered.binaryPacking_conditions (B₀).order.symm (B₀).graph
local notation "paddingN" => PhysicalShrink.padding (2*d₀+1) d₀ D
local notation "edgeOrd" => edgeOrder P₀ (baseNat (B₀).order) (tagOrdinal t₀).toEmbedding (S₀).pieces (S₀).pieceRadix (shrinkPieceBound s D)
local notation "padding" => tagPadding (V:=(B₀).Base) (L:=BitWord rem) (tagOne H.tagPos) (tagOne_ne H.tagPos) paddingN
private abbrev recordedOutgoingGraph (layout : Bool) (tagPositive : 0 < Diagonal.CompressorPacking.tagBits (2^s)) :=
  outGraph P₀ binary_neg good layout (shrinkStage s D).pieces edgeOrd hc₀ paddingN
    (tagPadding (V:=(shrinkRecordState s rem A).Base) (L:=BitWord rem)
      (tagOne tagPositive) (tagOne_ne tagPositive) paddingN)

private abbrev recordedOutgoingWidth :=
  outputWidth (shrinkRecordPacking s rem A) chosen many tiles
    (shrinkIssuedBranch B.shrink s D rem hD small A branch) binary_neg good
    (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch))
    (shrinkStage s D).pieces edgeOrd hc₀ paddingN

local notation "Gnew" => recordedOutgoingGraph s D rem A lay₀ H.tagPos
local notation "wnew" => recordedOutgoingWidth B s D rem hD small A branch
variable {Pins : Type}
variable (previous : WordLayout (oldGraph (shrinkRecordPacking s rem A)) (shrinkRecordWidth s rem A) Pins)
variable (successor : WordLayout
    (recordedOutgoingGraph s D rem A
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) H.tagPos)
    (recordedOutgoingWidth B s D rem hD small A branch) Pins)
variable (part : {j : Fin 6 //
  partySite (shrinkRecordPacking s rem A) (ShrinkMotif.chooseWidths
    (shrinkIssuedWords B.shrink s D rem hD small A branch)) (O.equiv slot).val j = site})
local notation "arm" => ({J with party:={J.party with motif:=slot.val,party:=part.val.val}} : HistoryGatherBody.Layout)
local notation "pageIndex" => (g₀).ports+(G₀ level).stride*((bestIndex).val*6+part.val.val)


local notation "ownerCount" => fun _ : Computability.VPVNP.Compression.Site (B₀).Base (BitWord t₀) (BitWord rem) => d₀*2^(2*d₀+1)
local notation "ownerOrd" => Owner.childOrder P₀ lay₀
local notation "oldPins" => WordLayout.oldPin previous successor ((P₀).placement lay₀) ownerCount ownerOrd site
local notation "newPins" => WordLayout.newPin previous successor ((P₀).placement lay₀) ownerCount ownerOrd site

local notation "iso₀" => StageAddress.shrinkInputIso (B₀).graph (B₀).chart (shrinkRecordLane s rem) P₀ rfl (B₀).width

private def recordedChildPrefix {V E U : Type} [Fintype V] [Fintype E]
    {G : PortGraph V E} {w : E → ℕ} (L : WordLayout G w Pins)
    (own : V → U) (count : U → ℕ) (ord : ∀ u, Fin (count u) ≃ {v // own v = u})
    (u : U) (k : Fin (count u)) : ℕ :=
  ∑ b : Fin k.val, L.ports.halfBits (ord u (b.castLE k.isLt.le)).val

private theorem recordedDemandRead {bits : ℕ} (mem : ℕ → ℕ)
    {ids nodes starts count k h oldID head childStart portStart : ℕ}
    (within : k < count) (room : ids + count ≤ 2^bits)
    (nodeRoom : nodes + (8*oldID+6) < 2^bits)
    (nodesFit : nodes < 2^bits) (startsRoom : starts + count < 2^bits)
    (idWord : mem (ids + k) = oldID) (nodeWord : mem (nodes + (8*oldID+6)) = head)
    (headerFit : head + 1 < 2^bits) (portFit : mem (head+1) + (4*h+3) < 2^bits)
    (startWord : mem (starts + k) = childStart)
    (portWord : mem (mem (head+1) + (4*h+3)) = portStart) :
    let child := mem (ids + k)
    let header := mem ((nodes : Word bits).val + (8*child+6))
    let table := mem (header + 1)
    (ids + k < 2^bits ∧ (nodes : Word bits).val + (8*child+6) < 2^bits ∧
     header+1 < 2^bits ∧ table+(4*h+3) < 2^bits ∧ (starts : Word bits).val+k < 2^bits) ∧
      mem ((starts : Word bits).val+k) = childStart ∧ mem (table+(4*h+3)) = portStart := by
  dsimp only
  rw [Fin.val_cast_of_lt nodesFit, Fin.val_cast_of_lt (show starts < 2^bits by omega),
    idWord, nodeWord]
  exact ⟨⟨by omega, nodeRoom, headerFit, portFit, by omega⟩, startWord, portWord⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
omit [Fintype F] in
private theorem recordedDemandCellsAt {E : Type} [Fintype E]
    {next : PortGraph (Computability.VPVNP.Compression.Site (B₀).Base (BitWord t₀) (BitWord rem)) E}
    {width : E → ℕ} (fresh : WordLayout next width Pins) (L : (B₀).Words Pins) (ordered : (B₀).OrderedHalves L)
    (oldSites : (B₀).ArchiveSites) (scratch : Memory W) (q : Fin (Fintype.card (demandGraph.Port part.val)))
    (bit : Fin (du m₀ ((dp part.val) q).val.1))
    (oldRows : State.HalfRows oldSites (fun a=>a<2^W) (fun a=>(scratch a).val))
    (childRoom : (HistoryGatherBody.selected arm scratch).childIDs.val+ownerCount site≤2^W)
    (nodeRoom : ∀ v,(arm).nodePorts.nodes+(8*oldSites.id v+6)<2^W)
    (nodesFit : (arm).nodePorts.nodes<2^W) (startsRoom : (arm).nodePorts.starts+ownerCount site<2^W)
    (childIds : ∀ k : Fin (ownerCount site),(scratch ((HistoryGatherBody.selected arm scratch).childIDs.val+k.val)).val=
      oldSites.id ((iso₀).site.symm ((ownerOrd site k).val)))
    (headers : ∀v,(scratch ((arm).nodePorts.nodes+(8*oldSites.id v+6))).val=
      oldSites.layer.incident+(oldSites.ord v).val*2)
    (oldPinsAt : ∀k : Fin (ownerCount site),(scratch ((arm).nodePorts.starts+k.val)).val=
      recordedChildPrefix (G:=oldGraph P₀) (w:=prior) ((iso₀).pushWord L)
        ((P₀).placement lay₀) ownerCount ownerOrd site k) :
    HistoryGatherExecution.DemandCells T₀ s D rem hD small A branch arm scratch m₀ part.val q.val
      ((iso₀).pushWord L) fresh site part.property ((dp part.val) q) bit := by
  let asked:=ChildSend.request P₀ rawCode prior (selected_bundle_positive s) numbers m₀
    ((dp part.val) q).val.2 ((dp part.val) q).val.1 bit
  have placed := ChildSend.at_party rawCode (selected_bundle_positive s) numbers
    (motifNumbers_bundle P₀ rawCode hc₀) lay₀ m₀ (v:=site) part.property ((dp part.val) q) bit
  let old:=ChildSend.ownedChild lay₀ site asked placed
  let half:=ChildSend.ownedPort lay₀ site asked placed
  let k:=((ownerOrd site).symm old)
  let h:=((ChildSend.portOrder P₀ old.val).symm half)
  let v:=(iso₀).site.symm old.val
  let head:=oldSites.layer.incident+(oldSites.ord v).val*2
  let table:=(scratch (head+1)).val
  have idCell : (scratch ((HistoryGatherBody.selected arm scratch).childIDs.val+k.val)).val=oldSites.id v := by
    simpa only [k,Equiv.apply_symm_apply,v] using childIds k
  have ind (k' : Fin (2*d₀)) : (scratch (table+(4*k'.val+3))).val=
      Halves.prefixValue (B₀).graph (B₀).width ((B₀).chart.symm v) k' := by
    simpa only [table,head,Nat.add_assoc] using oldRows.start v k'
  have tailFit : table+(4*h.val+3)<2^W := by
    simpa only [table,head,Nat.add_assoc,show (3 : Fin 4).val = 3 by decide] using
      oldRows.entriesSafe v h (3 : Fin 4)
  have halfStart := ChildSend.predecessor_half_row B₀ (shrinkRecordLane s rem) P₀ rfl L ordered old.val
    (fun a=>(scratch a).val) table ind half
  exact recordedDemandRead (bits:=W) (fun a => (scratch a).val) k.isLt childRoom (nodeRoom v)
    nodesFit startsRoom idCell (headers v) (oldRows.headerSafe v (1:Fin 2)) tailFit (oldPinsAt k) halfStart

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
omit [Fintype F] in
/-- Walk the actual child-ID and incident rows from the selected register file.
The requested old party may be on either end of any dense or sparse edge. -/
theorem recorded_demand_cells (L : (B₀).Words Pins) (ordered : (B₀).OrderedHalves L)
    (oldSites : (B₀).ArchiveSites) (scratch : Memory W) (q : Fin (Fintype.card (demandGraph.Port part.val)))
    (bit : Fin (du m₀ ((dp part.val) q).val.1))
    (oldRows : State.HalfRows oldSites (fun a=>a<2^W) (fun a=>(scratch a).val))
    (childRoom : (HistoryGatherBody.selected arm scratch).childIDs.val+ownerCount site≤2^W)
    (nodeRoom : ∀ v,(arm).nodePorts.nodes+(8*oldSites.id v+6)<2^W)
    (nodesFit : (arm).nodePorts.nodes<2^W) (startsRoom : (arm).nodePorts.starts+ownerCount site<2^W)
    (childIds : ∀ k : Fin (ownerCount site),(scratch ((HistoryGatherBody.selected arm scratch).childIDs.val+k.val)).val=
      oldSites.id ((iso₀).site.symm ((ownerOrd site k).val)))
    (headers : ∀v,(scratch ((arm).nodePorts.nodes+(8*oldSites.id v+6))).val=
      oldSites.layer.incident+(oldSites.ord v).val*2)
    (oldPinsAt : ∀k : Fin (ownerCount site),(scratch ((arm).nodePorts.starts+k.val)).val=
      recordedChildPrefix (G:=oldGraph P₀) (w:=prior) ((iso₀).pushWord L)
        ((P₀).placement lay₀) ownerCount ownerOrd site k) :
    HistoryGatherExecution.DemandCells T₀ s D rem hD small A branch arm scratch m₀ part.val q.val
      ((iso₀).pushWord L) successor site part.property ((dp part.val) q) bit :=
  recordedDemandCellsAt (B:=B) (s:=s) (D:=D) (rem:=rem) (hD:=hD) (small:=small) (A:=A)
    (branch:=branch) (site:=site) (O:=O) (slot:=slot) (J:=J) (part:=part)
    successor L ordered oldSites scratch q bit oldRows childRoom nodeRoom nodesFit startsRoom
    childIds headers oldPinsAt

local notation "success[" row "]" => Resident.successor («pad»:=paddingN) S₀ P₀ (B₀).order (shrinkPieceBound s D)
  lay₀ hc₀ good (row).tagPos
local notation "dnew" => Diagonal.CompressorPacking.Native.Graph.liveDegree S₀+paddingN

private theorem recordedSupplyHalfReads {V Tag Pin : Type} [Fintype V] [Fintype Tag]
    {degree lanes : ℕ} (graph : LiftedSlots (V × Tag) degree (BitWord lanes))
    (v : Computability.VPVNP.Compression.Site V Tag (BitWord lanes))
    {bits : Numbered V Tag (BitWord lanes) degree → ℕ}
    (words : WordLayout (slotPortGraph graph) bits Pin) (count : words.count v = 2*degree)
    (order : ∀ i, words.order v i = HalfOrder.order graph v (i.cast count))
    (mem : ℕ → ℕ) (limit : ℕ) {start table : ℕ} (pointer : start = table)
    (extent : table + 4*(2*degree) ≤ limit)
    (rows : ∀ i : Fin (2*degree), mem (table+4*i.val+3) =
      Halves.prefixValue graph bits ((v.1,v.2.1),v.2.2) i) :
    (∀ a : (slotPortGraph graph).Port v, start+(4*SupplySend.halfOrdinal graph a.val.1 a.val.2+3) < limit) ∧
    (∀ a : (slotPortGraph graph).Port v, mem (start+(4*SupplySend.halfOrdinal graph a.val.1 a.val.2+3)) =
      words.ports.start v a) := by
  subst start
  constructor
  · intro a
    rw [← SupplySend.successor_ordinal graph v a]
    have bound := ((HalfOrder.order graph v).symm a).isLt
    omega
  · exact SupplySend.successor_half_row graph v words count order mem table rows

/-- Count a word layout's incident bits directly in the order of its ports. -/
private def recordedSupplyPortBits {V E Pin : Type} {graph : LinearAlgebra.SpectralBooks.PortGraph V E}
    {bits : E → ℕ} (words : WordLayout graph bits Pin) (v : V) : ℕ :=
  ∑ i : Fin (words.count v), bits (words.order v i).val.1

private theorem recordedSupplyArgSize {V E U D Pin : Type}
    [Fintype V] [Fintype E] [Fintype U] [Fintype D] {g : LinearAlgebra.SpectralBooks.PortGraph V E}
    {h : LinearAlgebra.SpectralBooks.PortGraph U D} {b : E → ℕ} {c : D → ℕ}
    (old : WordLayout g b Pin) (fresh : WordLayout h c Pin) (own : V → U)
    (count : U → ℕ) (order : ∀ u, Fin (count u) ≃ {v // own v = u}) (u : U) :
    WordLayout.prior old own count order u + recordedSupplyPortBits fresh u =
      WordLayout.argSize old fresh own count order u := rfl

private theorem recordedSupplyPrivateRoom {w start : ℕ} (e : Fin 8) (fit : start+9 < 2^w) :
    (start : Word w).val+e.val < 2^w := by
  rw [Fin.val_cast_of_lt (show start < 2^w by omega)]
  have bound := e.isLt
  omega

open private incidentOwnerWith from OAI.ThreeFlat.RAM.HistoryShrinkIncidentRecords

private theorem recordedSupplyFilterEq {Party Site : Type} (src dst : Fin 8 → Party)
    (place : Party → Site) (site : Site) (e : Fin 8) (widths : Fin 8 → ℕ)
    (first second : DecidableEq Site)
    (p₁ : DecidablePred (fun b : Fin 8 => incidentOwnerWith first src dst place b = some site ∧ b < e))
    (p₂ : DecidablePred (fun b : Fin 8 => incidentOwnerWith second src dst place b = some site ∧ b < e)) :
    (∑ b ∈ @Finset.filter (Fin 8) (fun b => incidentOwnerWith first src dst place b = some site ∧ b < e)
      p₁ Finset.univ, widths b) =
    (∑ b ∈ @Finset.filter (Fin 8) (fun b => incidentOwnerWith second src dst place b = some site ∧ b < e)
      p₂ Finset.univ, widths b) := by
  cases Subsingleton.elim first second
  cases Subsingleton.elim p₁ p₂
  rfl

private theorem recorded_supply_prefix {w₁ : ℕ} {geo : Diagonal.CompressorPacking.Native.Graph.Stage}
    (layout : HistoryGatherBody.Layout) (initial scratch : Memory w₁) (owns : Fin 8 → Prop)
    (widths : Fin 8 → ℕ) (rows : PrivateSite (geo:=geo) layout initial owns widths)
    (room : layout.privateStarts+9 < 2^w₁)
    (saved : ∀ e : Fin 8, scratch (layout.privateStarts+e.val) =
      headerImage (privateHeader layout w₁) layout.privateStarts 9 initial (layout.privateStarts+e.val))
    (total : (∑ b, widths b) < 2^w₁) (e : Fin 8) :
    (scratch ((layout.privateStarts : Word w₁).val+e.val)).val =
      ∑ b ∈ Finset.univ.filter (fun b : Fin 8 => owns b ∧ b < e), widths b := by
  let prefixSize := ∑ b ∈ Finset.univ.filter (fun b : Fin 8 => owns b ∧ b < e), widths b
  have fits : prefixSize < 2^w₁ := lt_of_le_of_lt
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => Nat.zero_le (widths b))) total
  have readWord : scratch (layout.privateStarts+e.val) = (prefixSize : Word w₁) :=
    (saved e).trans (HistoryMotifJoin.PrivateSite.prefix layout rows (e.castLE (by decide)) room)
  rw [Fin.val_cast_of_lt (show layout.privateStarts < 2^w₁ by omega)]
  exact (congrArg Fin.val readWord).trans (Fin.val_cast_of_lt fits)

private def supplyReadAt {w : ℕ} {Port : Type} (mem : Memory w) (registers : HistoryScopeAddress.Layout)
    (publicWidth oldWidth : ℕ) (edge : Fin 8) (portOrdinal portStart : Port → ℕ)
    (owns : Fin 8 → Prop) (widths : Fin 8 → ℕ)
    (choice : DecidablePred (fun b : Fin 8 => owns b ∧ b < edge)) : Prop :=
  let table := (mem (registers.newHalves+1)).val
  registers.publicPins = publicWidth ∧ registers.oldBits = oldWidth ∧ registers.newHalves+1 < 2^w ∧
    (∀ a, table+(4*portOrdinal a+3) < 2^w) ∧ registers.privateStarts+edge.val < 2^w ∧
    (∀ a, (mem (table+(4*portOrdinal a+3))).val = portStart a) ∧
    (mem (registers.privateStarts+edge.val)).val =
      ∑ b ∈ @Finset.filter (Fin 8) (fun b => owns b ∧ b < edge) choice Finset.univ, widths b

private theorem supplyReadAt_selected {w : ℕ} {Port : Type} (layout : HistoryGatherBody.Layout)
    (mem : Memory w) (job : ℕ) (digit : Word w) (publicWidth oldWidth : ℕ) (edge : Fin 8)
    (portOrdinal portStart : Port → ℕ) (owns : Fin 8 → Prop) (widths : Fin 8 → ℕ)
    (choice : DecidablePred (fun b : Fin 8 => owns b ∧ b < edge))
    (pub : ((HistoryGatherBody.selected layout mem).oldBits+(HistoryGatherBody.selected layout mem).newBits).val = publicWidth)
    (oldRead : (HistoryGatherBody.selected layout mem).oldBits.val = oldWidth)
    (header : (HistoryGatherBody.selected layout mem).newHalves.val+1 < 2^w)
    (fits : ∀ a, (mem ((HistoryGatherBody.selected layout mem).newHalves.val+1)).val+
        (4*portOrdinal a+3) < 2^w)
    (room : (layout.privateStarts : Word w).val+edge.val < 2^w)
    (portRead : ∀ a, (mem ((mem ((HistoryGatherBody.selected layout mem).newHalves.val+1)).val+
        (4*portOrdinal a+3))).val = portStart a)
    (privateRead : (mem ((layout.privateStarts : Word w).val+edge.val)).val =
        ∑ b ∈ @Finset.filter (Fin 8) (fun b => owns b ∧ b < edge) choice Finset.univ, widths b) :
    supplyReadAt mem (HistoryGeometryPointer.layoutOf (HistoryGatherBody.sourceRegisters layout mem true job digit))
      publicWidth oldWidth edge portOrdinal portStart owns widths choice :=
  ⟨pub,oldRead,header,fits,room,portRead,privateRead⟩

set_option maxHeartbeats 1200000 in
omit [Fintype F] in
/-- Read the genuine native half table for a crossing edge, or the genuine
saved nine-cell prefix for an absorbed edge, on the same selected component. -/
theorem recorded_supply_cells (scratch begin_ : Memory W) (q : Fin (Fintype.card (supplyGraph.Port part.val)))
    (bit : Fin (issuedWords m₀ ((sp part.val) q).val.1))
    (oldBits : ((HistoryGatherBody.selected arm scratch).oldBits).val=WordLayout.prior previous ((P₀).placement lay₀) ownerCount ownerOrd site)
    («public» : ((HistoryGatherBody.selected arm scratch).oldBits+(HistoryGatherBody.selected arm scratch).newBits).val=
      WordLayout.prior (G:=oldGraph P₀) (w:=prior) previous ((P₀).placement lay₀) ownerCount ownerOrd site +
        recordedSupplyPortBits successor site)
    (count : successor.count site=2*dnew)
    (order : ∀i,successor.order site i=HalfOrder.order success[H] site (i.cast count))
    (privateRows : PrivateSite (geo:=S₀) J begin_
      (fun e=>wireOwner supplyGraph.tail supplyGraph.head (partySite P₀ lay₀ m₀) e=some site) (issuedWords m₀))
    (room : J.privateStarts+9<2^W)
    (savedPrefix : ∀ e:Fin 8,scratch (J.privateStarts+e.val)=
      headerImage (privateHeader J W) J.privateStarts 9 begin_ (J.privateStarts+e.val))
    (width : (∑e:Fin 8,issuedWords m₀ e)<2^W)
    (header : (HistoryGatherBody.selected arm scratch).newHalves.val+1<2^W)
    (table : ℕ) (whereAt : (scratch ((HistoryGatherBody.selected arm scratch).newHalves.val+1)).val=table)
    (end_ : table+4*(2*dnew)≤2^W)
    (rowAt : ∀ i:Fin (2*dnew),(scratch (table+4*i.val+3)).val=
      Halves.prefixValue success[H] wnew ((site.1,site.2.1),site.2.2) i) :
    HistoryGatherExecution.SupplyCells T₀ s D rem hD small A branch H arm scratch m₀ part.val q.val
      previous successor site ((sp part.val) q) bit := by
  let e:=((sp part.val) q).val.1
  let owns:=fun e=>wireOwner supplyGraph.tail supplyGraph.head (partySite P₀ lay₀ m₀) e=some site
  have halves := recordedSupplyHalfReads success[H] site (bits:=wnew) successor count order
    (fun a => (scratch a).val) (2^W) whereAt end_ rowAt
  have publicSize := «public».trans
    (recordedSupplyArgSize previous successor ((P₀).placement lay₀) ownerCount ownerOrd site)
  have prefixRead := recorded_supply_prefix (geo:=S₀) J begin_ scratch owns (issuedWords m₀)
    privateRows room savedPrefix width e
  refine supplyReadAt_selected arm scratch q.val (bit.val : Word W)
    (WordLayout.argSize previous successor ((P₀).placement lay₀) ownerCount ownerOrd site)
    (WordLayout.prior previous ((P₀).placement lay₀) ownerCount ownerOrd site) e
    (fun a : (Gnew).Port site => SupplySend.halfOrdinal success[H] a.val.1 a.val.2)
    (fun a => successor.ports.start site a)
    (fun b => incidentOwnerWith _ supplyGraph.tail supplyGraph.head (partySite P₀ lay₀ m₀) b = some site)
    (issuedWords m₀) _ publicSize oldBits header halves.1 (recordedSupplyPrivateRoom e room) halves.2 ?_
  exact prefixRead.trans
    (recordedSupplyFilterEq supplyGraph.tail supplyGraph.head (partySite P₀ lay₀ m₀) site e (issuedWords m₀) _ _ _ _)

/-- Data read from the issued arm and the exact pair and gather instructions
at that arm. The dependent tile and page were fixed by the accepted row. -/
structure CapturedArm {K₀ : Type} [Field K₀] [Fintype K₀] {w n e a p h : ℕ}
    (role : Party K₀) (page ar r : ℕ) (live : Fin n→ℕ) (digits : Fin n→ℕ)
    (widths : Fin e→ℕ) (size : ℕ) (id : ((Fin 3→Bool)→K₀)→ℕ)
    (awin : HistoryGatherBody.Layout) (node : ℕ) (z : HistoryGatherExecution.Plan w)
    (first paired : Memory w) (ticks : ℕ) (net : BitNetwork K₀ a) (wire : Fin a→BitSource h p)
    (batchRoom : Prop) : Prop where
  room : batchRoom
  election : Elected node id awin z first paired ticks net wire
  pageRead : HistoryGatherExecution.ReadPage awin paired role ar page
  demands : n≤awin.demandCap
  supplies : e≤awin.supplyCap
  oldWords : ∀i:Fin n,(physicalWidth awin paired false i.val).val=live i
  freshWords : ∀i:Fin e,(physicalWidth awin paired true i.val).val=widths i
  repetitions : ∀i,live i≤digits i*r
  mapCount : (partyMapCount awin paired).val=size
  atNode : (HistoryNodePorts.id awin.nodePorts).value (fun _=>0) paired (fun _=>0)=(node:Word w)
  pairAddress : HistoryPartyPair.atPair awin.party node 2<2^w

private abbrev recordedTileHeader (catalog : ShrinkMotif.Table F) (row : catalog.Row) (j : Fin 6) :
    HistogramTileNetwork.Header (demandGraph.Port j) (catalog.block row).Alphabet
      (fun q => catalog.base row q.1.1) (catalog.block row).bits (Fintype.card (demandGraph.Port j)) :=
  ⟨(Fintype.equivFin (demandGraph.Port j)).symm, (catalog.block row).encode⟩

omit [Fintype F] in
private theorem recordedCatalogueBounds (archive : Block F) (levelAt : Fin archive.levels)
    (index : Fin (archive.shrink.more.length+1)) (row : archive.shrink.Row)
    (chosenRow : archive.shrink.row index = row) (j : Fin 6)
    (listed : shrinkGrid archive levelAt ∈ grids archive) :
    let entry := archive.shrink.block row
    let count := Fintype.card (supplyGraph.Port j)
    (recordedTileHeader archive.shrink row j).arity + (count*entry.bitCap + count*entry.bitCap) ≤ arity archive ∧
      count*entry.bits + Fintype.card entry.Alphabet ≤ arity archive := by
  subst row
  exact arity_fits archive listed (show shrinkParty archive.shrink index j ∈ (shrinkGrid archive levelAt).rows from
    grid_has (shrinkParty archive.shrink) index j)

private def recordedPageStart (archive : Block F) (levelAt : Fin archive.levels)
    (height base : ℕ) (earlier : List (Grid F)) (index j : ℕ) : ℕ :=
  let grid := shrinkGrid archive levelAt
  (grid.family (Mounted.base archive height base earlier)).ports + grid.stride*(index*6+j)

open private emitPartyAt from OAI.ThreeFlat.RAM.HistoryShrinkArms
open private sitePins from OAI.ThreeFlat.Diagonal.ShrinkSiteTree

private structure RecordedGather (wordBits parentSize : ℕ) where
  privateSize : ℕ
  inputSize : ℕ
  wire : Fin inputSize → BitSource privateSize parentSize
  source : Bool → ℕ → ℕ → Word wordBits

private noncomputable def RecordedGather.plan {wordBits parentSize : ℕ}
    (bank : HistoryGatherBody.Layout) (mem : Memory wordBits) (wiring : RecordedGather wordBits parentSize) :=
  let ptr := ((HistoryGatherBody.selected bank mem).privatePage 2).val
  let word := HistoryGatherExecution.gatheredWord (W:=wordBits) ptr (fun i => BitLayout.sourceAddress (wiring.wire i))
  HistoryGatherExecution.nativePlan bank mem wiring.source word

section Gather
open Diagonal.MotifBinaryPacking
attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph SlotRefinement.actualWidth allPieceSlots

private noncomputable def recordedGather
    {colors degree quota parentSize wordBits : ℕ} {V G Tag L : Type}
    [AddCommGroup G] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype G] [Fintype Tag] [Fintype L]
    (pack : PackingData V G Tag L degree colors) (width : Arc V G Tag L degree colors → ℕ)
    (code : Arc V G Tag L degree colors ↪ ℕ) (nonzero : 0 < quota)
    (number : pack.Motif ≃ (Site V Tag L × Fin degree) × Fin quota)
    (bases : pack.Motif → Fin 2 → ℕ) (copiesAt : pack.Motif → ℕ)
    (tables : ∀ m, FixedMotifTile demandGraph supplyGraph (bases m) F)
    (observations : Histories pack bases copiesAt tables) (neg : ∀ a : Tag, -a = a)
    (shape : TagConditions pack.slots (shift pack) pack.offset) (choice : Bool)
    (slots : Fin 4 → ℕ) (pos : ∀ i, 0 < slots i) (edge : ShrinkEdge pack slots ↪ ℕ)
    (two : 2 ≤ colors) (extraN : ℕ) (extraSlots : LiftedSlots (V × Tag) extraN L) (v : Site V Tag L)
    (old : (i : {i // pack.placement choice i = v}) → (q : (oldGraph pack).Port i.val) →
      Fin (width q.1.1) → Fin parentSize)
    (new : sitePins (outGraph pack neg shape choice slots edge two extraN extraSlots)
      (outputWidth pack bases copiesAt tables observations neg shape choice slots edge two extraN) v parentSize)
    (m : pack.Motif) (side : {j // partySite pack choice m j = v})
    (bank : HistoryGatherBody.Layout) : RecordedGather wordBits parentSize :=
  let selectedTile := tables m
  letI := selectedTile.hasLetter
  let demand := (Fintype.equivFin (demandGraph.Port side.val)).symm
  let supply := (Fintype.equivFin (supplyGraph.Port side.val)).symm
  let head : HistogramTileNetwork.Header (demandGraph.Port side.val) selectedTile.Alphabet
        (fun q => bases m q.1.1) selectedTile.bits (Fintype.card (demandGraph.Port side.val)) :=
    ⟨demand, selectedTile.encode⟩
  let sample : Histogram selectedTile.Alphabet (copiesAt m) := observations m
  let location := partySite pack choice m
  let owned := HistoryMaskOrder.order (fun e => wireOwner supplyGraph.tail supplyGraph.head location e = some v)
  let bits := HistogramTileNetwork.order (k:=selectedTile.bits) ShrinkMotif.supply location v selectedTile.output sample owned
  let crossed := crossingPin (p:=parentSize) pack bases copiesAt tables observations neg shape choice slots pos
    edge two extraN extraSlots v new m
  let oldSource := oldPinSource (p:=parentSize) (h:=bits.bits) pack width code nonzero number choice v old m side.val
  let freshSource := bits.partySource crossed side
  let source := HistoryGatherExecution.typedSources (W:=wordBits) (p:=parentSize) (h:=bits.bits) (r:=copiesAt m)
    bank demandGraph ShrinkMotif.supply side.val (bases m) (demandWidth pack width number m) head supply
    selectedTile.output sample oldSource freshSource
  let ports := Fintype.card (supplyGraph.Port side.val)
  let inputSize := copiesAt m * (ports * selectedTile.bits) +
    (copiesAt m * head.arity + ports * (copiesAt m * selectedTile.bitCap))
  let wire : Fin inputSize → BitSource bits.bits parentSize :=
    partyPointer (d:=selectedTile.bitCap) (p:=parentSize) (h:=bits.bits) (r:=copiesAt m)
      demandGraph ShrinkMotif.supply side.val (bases m) (demandWidth pack width number m) head supply
      selectedTile.output sample oldSource freshSource
  ⟨bits.bits, inputSize, wire, source⟩
end Gather


set_option maxRecDepth 16000 in
private theorem recordedPortProbe {w : ℕ} {layout : HistoryGatherBody.Layout}
    {input old scratch : Memory w} {x : Diagonal.CompressorPacking.Native.ShrinkStage.Dimensions}
    {p : Diagonal.CompressorPacking.Native.ShrinkStage.Pointers}
    (foot : PortFootprint layout input x p) (inheritedGeometry : Resident.GeometryFrame x p old input)
    (span : DescriptorScan.agreesOutside layout.temp (HistoryGatherExecution.portsEnd layout) scratch input)
    (side : Bool) (index : ℕ) (valid : index < HistoryGatherExecution.cap layout side)
    (header : ℕ) (keyWord : Word w) (port : ℕ)
    (kernel : (input (selected layout input).kernel.val).val = header)
    (key : input (selected layout input).incident.val = keyWord)
    (code : (portCode layout input side index).val = port) :
    Resident.GeometryFrame x p old scratch ∧
      (scratch (selected layout scratch).kernel.val).val = header ∧
      scratch (selected layout scratch).incident.val = keyWord ∧
      (portCode layout scratch side index).val = port := by
  obtain ⟨geometry,atKernel,atIncident,atPort⟩ := foot.after_port inheritedGeometry span side index valid
  exact ⟨geometry,(congrArg Fin.val atKernel).trans kernel,atIncident.trans key,
    (congrArg Fin.val atPort).trans code⟩

private noncomputable def recordedSupplyWidths (partyIndex : Fin 6) (widths : Fin 8 → ℕ)
    (i : Fin (Fintype.card (supplyGraph.Port partyIndex))) : ℕ :=
  widths (((Fintype.equivFin (supplyGraph.Port partyIndex)).symm i).val.1)

private theorem recordedScanFrame {w parentSize : ℕ} (bank : HistoryGatherBody.Layout)
    (input scratch : Memory w) (wiring : RecordedGather w parentSize)
    (side : Bool) (i size : ℕ) (valid : i < HistoryGatherExecution.cap bank side)
    (width : (physicalWidth bank input side i).val = size)
    (current : DescriptorScan.agreesOutside (srcBase bank side i) (srcBase bank side i + size)
      scratch (HistoryGatherExecution.beforePort bank (RecordedGather.plan bank input wiring) input side i))
    (headerSize : 3 + 5 * bank.demandCap + 4 * bank.supplyCap ≤ bank.party.V)
    (fits : ∀ side j, j < HistoryGatherExecution.cap bank side →
      (RecordedGather.plan bank input wiring).width side j ≤ bank.party.V) :
    DescriptorScan.agreesOutside bank.temp (HistoryGatherExecution.portsEnd bank) scratch input := by
  apply HistoryGatherExecution.beforePort_frame bank (RecordedGather.plan bank input wiring) input side i valid scratch _ headerSize fits
  change DescriptorScan.agreesOutside _ (_ + (physicalWidth bank input side i).val) _ _
  rw [width]
  exact current

set_option maxHeartbeats 2400000 in
/-- Elected physical shrink arm from actual journal incidence, mounted catalogue, selected
tile, and both issued-width scans. Remaining scan bounds and scope fields are local to the
indicated party. The result carries both executions, the actual factor rows and every wire. -/
abbrev emit_recorded_party := fun (input : Memory W) (node : ℕ)
    (heightFit : siteHeight (many m₀) (tileAt).bitCap≤height)
    (kindBase : (arm).party.kinds=(g₀).kinds) (portBase : (arm).catalogue=(g₀).ports)
    (dem : (arm).demandCap=(G₀ level).demand) (sup : (arm).supplyCap=(G₀ level).supply) (dig : (arm).digitCap=(G₀ level).digits)
    (ps : (arm).party.parties=6) (mode : (arm).mode=.shrink S₀)
    (stride : (arm).histogramStride=K) (positive : 0<K) (strideFit : K<2^W)
    (kindRoom : (g₀).kinds+7*((bestIndex).val*6+part.val.val)+7≤2^W)
    (portRoom : pageIndex+(G₀ level).stride≤2^W)
    (kindFit : ∀k:Fin 7,((shrinkParty T₀ bestIndex part.val).kind (arity B)).words k<2^W)
    (portFit : ∀k:Fin (G₀ level).stride,(shrinkParty T₀ bestIndex part.val).port.at (G₀ level).demand (G₀ level).supply k.val<2^W)
    (extra : ShrinkOutputCaps s D N₀ W) (top : ℕ) (issuedSize : ∀ a e,issuedWords a e≤top)
    (topWord : top<2^W) (oldWord : A.maxWidth<2^W) (thickWord : thickWidth P₀ prior ((P₀).bundle m₀)<2^W) =>
  letI := (tileAt).hasLetter
  let selectedDemand : Fin 2 → ℕ := du m₀
  let index : Fin ((T₀).more.length+1) := RefreshDemandRows.tileNumber selectedDemand ((T₀).base ∘ (T₀).row)
  let row : (T₀).Row := MotifIntegerChoice.best (MotifIntegerChoice.score selectedDemand (T₀).base) (T₀).first (T₀).more
  letI : Nonempty ((T₀).block row).Alphabet := ((T₀).block row).hasLetter
  let hd := recordedTileHeader T₀ row part.val
  let alpha:=Fintype.equivFin (tileAt).Alphabet
  let accepted:=headerGood ShrinkMotif.supply part.val (sp part.val) hd.code
  let letter:=headerLetter ShrinkMotif.supply part.val (sp part.val) alpha hd.code
  let observations : shrinkRecordHists T₀ s rem A := shrinkIssuedBranch T₀ s D rem hD small A branch
  let selectedHistogram : Histogram (tileAt).Alphabet (many m₀) := observations m₀
  let z := numberHistogram (H:=(tileAt).Alphabet) (r:=many m₀)
    (h:=Fintype.card (tileAt).Alphabet) alpha selectedHistogram
  let t:Fin (height+1):=⟨siteHeight (many m₀) (tileAt).bitCap,by omega⟩
  let tbl:=HistogramTileNetwork.tile demandGraph ShrinkMotif.supply part.val baseAt hd (sp part.val) (tileAt).output
    (fun a e=>(tileAt).output_le_cap a _) (tileAt).entry
  have gmem : G₀ level ∈ grids B := by rw [stage]; simp
  have bounds := recordedCatalogueBounds B level index row ((T₀).row_chosen selectedDemand) part.val gmem
  let pageStart := recordedPageStart B level height start pre index.val part.val.val
  fun readC readP eroom=>
  let postPair : Memory W := electedOutput tbl accepted letter bounds.1 bounds.2 (arm).party node input t z readC readP
  fun (library : Mounted B height W start postPair)
      (nodePtr : (selected arm postPair).kernel=(kernelBase:Word W))
      (kguard : ∀j:Fin 5,kernelBase+j.val≠cur.val ∧ kernelBase+j.val≠ctr.val ∧ hdr≤kernelBase+j.val)
      (kkeep : ∀j:Fin 5,postPair (kernelBase+j.val)=final (kernelBase+j.val))
      (keepRows : ∀j:Fin 6,postPair (baseRow+j.val)=final (baseRow+j.val))
      (geo : GeometryFrame x₀ (pointers K c x₀) issued postPair)
      (portWindow : (selected arm postPair).portPage=(pageStart:Word W)→PortFootprint arm postPair x₀ (pointers K c x₀))
      (dkeep : ∀e:Fin 2,postPair ((pointers K c x₀).demands+ordinal*2+e.val)=issued ((pointers K c x₀).demands+ordinal*2+e.val))=>
  have kernel:=recorded_kernel B s D rem hD small A cur ctr before issued final postPair c branch hdr H saved
    site slot arm oldCaps baseFit wide capFits offset nodePtr rfl kguard kkeep
  have mountedTile:=recorded_tile B s D rem hD small A cur ctr before issued final postPair c branch hdr H saved
    site O slot arm oldCaps baseFit wide capFits offset kernel.1 apart keepRows level library stage part
    kindBase portBase dem sup dig ps rfl rfl kernel.2.1 kindRoom portRoom kindFit portFit
  have outside:=portWindow mountedTile.1.base
  have physical:=recorded_widths B s D rem hD small A cur ctr before issued final postPair c branch hdr H saved
    site O slot arm oldCaps baseFit wide capFits offset kernel.1 apart keepRows level part.val pageStart (arity B) mountedTile.1
    mountedTile.2.1 dem sup dig mode stride positive strideFit geo kernel.2.2 dkeep (fun e=>(issuedSize _ e).trans_lt topWord)
  let parentPins := WordLayout.argSize previous successor ((P₀).placement lay₀) ownerCount ownerOrd site
  let wiring := recordedGather (F:=F) (parentSize:=parentPins) (wordBits:=W)
    P₀ prior rawCode (selected_bundle_positive s) numbers chosen many tiles observations binary_neg good lay₀
    (S₀).pieces (copiesPositive s D hD small) edgeOrd hc₀ paddingN padding site oldPins newPins m₀ part arm
  let plan := RecordedGather.plan arm postPair wiring
  have key : postPair (selected arm postPair).incident.val=(rawCode (m₀).val:Word W):=by
    have cell : wordAt postPair (selected arm postPair).incident 0 = (rawCode (m₀).val : Word W) :=
      recorded_word B s D rem hD small A cur ctr before issued final postPair c branch hdr H saved site O slot
        arm oldCaps baseFit wide capFits offset kernel.1 apart keepRows (0 : Fin 6)
    simpa only [wordAt,Nat.cast_zero,add_zero] using cell
  let freshWidth := recordedSupplyWidths part.val (issuedWords m₀)
  And.intro mountedTile.1 (And.intro mountedTile.2.1 (And.intro physical
    (And.intro kernel.2.2 (And.intro key (
  fun (drows : ∀(i:Fin (Fintype.card (demandGraph.Port part.val))) (bit:Fin (du m₀ ((dp part.val) i).val.1))
      (scratch:Memory W),DescriptorScan.agreesOutside (arm).temp (HistoryGatherExecution.portsEnd arm) scratch postPair →
        HistoryGatherExecution.DemandCells T₀ s D rem hD small A branch arm scratch m₀ part.val i.val
            previous successor site part.property ((dp part.val) i) bit)
      (srows : ∀(i:Fin (Fintype.card (supplyGraph.Port part.val))) (bit:Fin (freshWidth i))
      (scratch:Memory W),DescriptorScan.agreesOutside (arm).temp (HistoryGatherExecution.portsEnd arm) scratch postPair →
        HistoryGatherExecution.SupplyCells T₀ s D rem hD small A branch H arm scratch m₀ part.val i.val
            previous successor site ((sp part.val) i) bit)
      space resident hSize fits mapCount mapRoom range header keep clear headAt digit scalar oldRoom newRoom
      atNode fitsAddress clearPair=>
  have selectedParty : (arm).party.party = part.val.val := rfl
  let oldAt := fun (i : Fin (Fintype.card (demandGraph.Port part.val)))
      (bit : Fin (du m₀ ((dp part.val) i).val.1)) (scratch : Memory W)
      (frame : DescriptorScan.agreesOutside (HistoryGatherBody.srcBase arm false i.val)
        (HistoryGatherBody.srcBase arm false i.val + du m₀ ((dp part.val) i).val.1) scratch
        (HistoryGatherExecution.beforePort arm plan postPair false i.val)) =>
    have span := recordedScanFrame arm postPair scratch wiring false i.val _ (i.isLt.trans_le physical.1)
      (physical.2.2.2.1 i) frame hSize fits
    let pc:=mountedTile.1.demand physical.1 i mountedTile.2.1
    have probe := recordedPortProbe outside geo span false i.val (i.isLt.trans_le physical.1)
      (pointers K c x₀).ownHeader (rawCode (m₀).val : Word W) ((dp part.val) i).val.1.val
      kernel.2.2 key pc.2
    have rowRead : scratch (HistoryGatherBody.selected arm scratch).incident.val =
        gatherIncidentWord W (Demand.key (shrinkRecordPacking s rem A)
          (baseNat (shrinkRecordState s rem A).order) (O.equiv slot).val.val) :=
      recordedGatherKey (rawCode (m₀).val) probe.2.2.1
    let data:=drows i bit scratch span
    HistoryGatherExecution.demand_of_cells (W:=W) (K:=K) (cur:=cur) (c:=c)
      (boot:=before) (published:=issued) T₀ s D rem hD small A branch H oldCaps extra top issuedSize topWord
      arm mode scratch probe.1 probe.2.1 m₀ part.val rowRead selectedParty i.val previous successor
      site part.property wiring.privateSize ((dp part.val) i) bit probe.2.2.2 oldWord thickWord data
  let newAt := fun (i : Fin (Fintype.card (supplyGraph.Port part.val)))
      (bit : Fin (freshWidth i)) (scratch : Memory W)
      (frame : DescriptorScan.agreesOutside (HistoryGatherBody.srcBase arm true i.val)
        (HistoryGatherBody.srcBase arm true i.val + freshWidth i) scratch
        (HistoryGatherExecution.beforePort arm plan postPair true i.val)) =>
    have span := recordedScanFrame arm postPair scratch wiring true i.val _ (i.isLt.trans_le physical.2.1)
      (physical.2.2.2.2 i) frame hSize fits
    let pc:=mountedTile.1.supply physical.2.1 i mountedTile.2.1
    have probe := recordedPortProbe outside geo span true i.val (i.isLt.trans_le physical.2.1)
      (pointers K c x₀).ownHeader (rawCode (m₀).val : Word W) ((sp part.val) i).val.1.val
      kernel.2.2 key pc.2
    have rowRead : scratch (HistoryGatherBody.selected arm scratch).incident.val =
        gatherIncidentWord W (Demand.key (shrinkRecordPacking s rem A)
          (baseNat (shrinkRecordState s rem A).order) (O.equiv slot).val.val) :=
      recordedGatherKey (rawCode (m₀).val) probe.2.2.1
    let data:=srows i bit scratch span
    HistoryGatherExecution.supply_of_cells (W:=W) (K:=K) (cur:=cur) (c:=c)
      (boot:=before) (published:=issued) T₀ s D rem hD small A branch H oldCaps extra top issuedSize topWord
      arm mode scratch probe.1 probe.2.1 m₀ part.val rowRead selectedParty i.val previous successor
      site part.property ((sp part.val) i) bit probe.2.2.2 data
  let election := emitPartyAt (p:=parentPins) (W:=W) (Dmax:=height) P₀ prior rawCode (selected_bundle_positive s) numbers chosen many tiles hist binary_neg good
      (S₀).pieces (copiesPositive s D hD small) edgeOrd hc₀ paddingN padding site lay₀ oldPins newPins m₀ part J node slot.val (arity B)
      input heightFit bounds.1 bounds.2 readC readP eroom pageStart (arity B) mountedTile.1 mountedTile.2.1 mountedTile.2.2
      physical.1 physical.2.1 physical.2.2.1 space resident hSize fits mapCount mapRoom range header keep clear headAt digit scalar
      physical.2.2.2.2 physical.2.2.2.1 oldRoom newRoom oldAt newAt atNode fitsAddress clearPair
  let role:=Party.ofTile demandGraph ShrinkMotif.supply part.val baseAt tileAt
    (dp part.val) (sp part.val) (fun q=>((dp part.val) q).val.1.val) (fun q=>((sp part.val) q).val.1.val)
  have cover (i:Fin (Fintype.card (demandGraph.Port part.val))) :
      du m₀ ((dp part.val) i).val.1≤baseAt ((dp part.val) i).val.1*many m₀ :=
    PhysicalShrink.fits T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀ _
  show CapturedArm role pageStart (arity B) (many m₀)
    (fun i : Fin (Fintype.card (demandGraph.Port part.val))=>du m₀ ((dp part.val) i).val.1)
    (fun i=>baseAt ((dp part.val) i).val.1)
    (fun i : Fin (Fintype.card (supplyGraph.Port part.val))=>freshWidth i)
    _ tag arm node plan input postPair _ _ wiring.wire
    (ElectedRoom tbl accepted letter bounds.1 bounds.2 (arm).party node input t z readC readP) from
    ⟨eroom,election,mountedTile.1,physical.1,physical.2.1,physical.2.2.2.1,physical.2.2.2.2,
      cover,mapCount,atNode,fitsAddress⟩)))))


end PublishedParty
end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
