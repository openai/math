import OAI.ThreeFlat.RAM.HistoryShrinkIncidentRecords

namespace OAI
set_option quotPrecheck false
set_option maxErrors 600

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression Diagonal Diagonal.PhysicalStage
open Diagonal.CompressorPacking Diagonal.CompressorPacking.PhysicalShrink
open Diagonal.CompressorPacking.Native Diagonal.CompressorPacking.Native.ShrinkStage
open Diagonal.NavigationDirectory Diagonal.NavigationPass Diagonal.ShrinkStageNav
open HistoryStageBody.Physical HistoryGatherBody
open scoped Classical BigOperators Fin.CommRing
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

set_option maxHeartbeats 1400000 in
include H saved oldCaps baseFit wide capFits offset rowPtr apart preserved mounted stage in
/-- The two S38 tables at this physical incident: the catalogue is indexed by the selected
tile and raw party, and the tile equality uses the integer minimizer of the actual demand. -/
theorem recorded_page (party : Fin 6)
    (kindBase : J.party.kinds=(g₀).kinds) (portBase : J.catalogue=(g₀).ports)
    (dem : J.demandCap=(G₀ level).demand) (sup : J.supplyCap=(G₀ level).supply) (dig : J.digitCap=(G₀ level).digits)
    (ps : J.party.parties=6) (atP : J.party.party=party.val)
    (kindRoom : (g₀).kinds+7*((bestIndex).val*6+party.val)+7≤2^W)
    (portRoom : (g₀).ports+(G₀ level).stride*((bestIndex).val*6+party.val)+(G₀ level).stride≤2^W)
    (kindFit : ∀k:Fin 7,((shrinkParty T₀ bestIndex party).kind (arity B)).words k<2^W)
    (portFit : ∀k:Fin (G₀ level).stride,(shrinkParty T₀ bestIndex party).port.at (G₀ level).demand (G₀ level).supply k.val<2^W) :
    HistoryGatherExecution.ReadPage J post (shrinkParty T₀ bestIndex party) (arity B)
      ((g₀).ports+(G₀ level).stride*((bestIndex).val*6+party.val)) := by
  have chosen:=recorded_fields B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved party
  have tileWord : wordAt post (selected J post).incident 2 = ((bestIndex).val : Word W) := by
    simpa only [Fin.cast_val_eq_self] using congrArg (fun n : ℕ => (n : Word W)) chosen.2.1
  exact HistoryGatherExecution.read_mounted (G:=G₀ level) J post mounted stage (f:=shrinkParty T₀) rfl
    bestIndex party kindBase portBase dem sup dig ps atP tileWord kindRoom portRoom kindFit portFit

include H saved in
omit [Fintype F] in
/-- Each count surviving the chronological stage history belongs to this issued rewrite
branch and the actual alphabet of its selected tile. -/
theorem recorded_histogram (a : (P₀).Motif)
    (denseHold : ∀ (i : Fin (shrinkBinaryFamily T₀ s D rem hD small A).motifs)
      (v : (shrinkBinaryFamily T₀ s D rem hD small A).alphabet i),
      let addr:=c.dense+i.val*K+(Fintype.equivFin _ v).val
      addr≠c.header+27 ∧ addr≠cur.val ∧ addr≠ctr.val ∧ hdr≤addr ∧
      addr<(en₀).next.heap ∧ post addr=final addr)
    (b : Fin (Fintype.card (shrinkRecordTile T₀ s rem A a).Alphabet)) :
    (post (c.dense+(shrinkRecordOrder s rem A a).val*K+b.val)).val=
      ((shrinkIssuedBranch T₀ s D rem hD small A branch a).val ((Fintype.equivFin _).symm b)).val := by
  let ord:=shrinkRecordOrder s rem A
  obtain ⟨i,rfl⟩:=ord.symm.surjective a
  let v:=(Fintype.equivFin (shrinkRecordTile T₀ s rem A (ord.symm i)).Alphabet).symm b
  have hv : (Fintype.equivFin _ v).val=b.val:=congrArg Fin.val (Equiv.apply_symm_apply _ _)
  have room:=denseHold i v
  have word:=H.histogramWord i v room.1
  have through := saved _ room.2.1 room.2.2.1 (.inr room.2.2.2.1) room.2.2.2.2.1
  let addr:=c.dense+i.val*K+(Fintype.equivFin _ v).val
  have atAddr : c.dense+(ord (ord.symm i)).val*K+b.val = addr := by
    dsimp only [addr]
    rw [Equiv.apply_symm_apply,hv]
  calc
    _ = (post addr).val := congrArg (fun n => (post n).val) atAddr
    _ = (final addr).val := congrArg Fin.val room.2.2.2.2.2
    _ = (issued addr).val := congrArg Fin.val through
    _ = _ := word

local notation "tileAt" => shrinkRecordTile T₀ s rem A m₀
local notation "baseAt" => PhysicalShrink.widths T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀
local notation "dp" j => (Fintype.equivFin (demandGraph.Port j)).symm
local notation "sp" j => (Fintype.equivFin (supplyGraph.Port j)).symm

set_option maxHeartbeats 1400000 in
include H saved oldCaps baseFit wide capFits offset rowPtr apart preserved mounted stage in
/-- Actual image consumed by the elected gather, stated using the mathematical tile
appearing in the selected shrinkPiece, the two masks and the true copy count. -/
theorem recorded_tile (part : {j : Fin 6 // partySite P₀ lay₀ m₀ j=site})
    (kindBase : J.party.kinds=(g₀).kinds) (portBase : J.catalogue=(g₀).ports)
    (dem : J.demandCap=(G₀ level).demand) (sup : J.supplyCap=(G₀ level).supply) (dig : J.digitCap=(G₀ level).digits)
    (ps : J.party.parties=6) (atP : J.party.party=part.val.val) (atSlot : J.party.motif=slot.val)
    (kernelCount : (wordAt post (selected J post).kernel 3).val=
      (Incidents.siteKeys (S:=shrinkStage s D) (w:=W) P₀ (B₀).order lay₀ site).length)
    (kindRoom : (g₀).kinds+7*((bestIndex).val*6+part.val.val)+7≤2^W)
    (portRoom : (g₀).ports+(G₀ level).stride*((bestIndex).val*6+part.val.val)+(G₀ level).stride≤2^W)
    (kindFit : ∀k:Fin 7,((shrinkParty T₀ bestIndex part.val).kind (arity B)).words k<2^W)
    (portFit : ∀k:Fin (G₀ level).stride,(shrinkParty T₀ bestIndex part.val).port.at (G₀ level).demand (G₀ level).supply k.val<2^W) :
    let tileRecord:=Party.ofTile demandGraph ShrinkMotif.supply part.val baseAt tileAt
      (dp part.val) (sp part.val) (fun q=>((dp part.val) q).val.1.val) (fun q=>((sp part.val) q).val.1.val)
    HistoryGatherExecution.ReadPage J post tileRecord (arity B) ((g₀).ports+(G₀ level).stride*((bestIndex).val*6+part.val.val)) ∧
      partyActive J post ∧ (wordAt post (selected J post).incident 3).val=shrinkRecordCopies T₀ s rem A m₀ := by
  have fields:=recorded_fields B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved part.val
  have ready:=recorded_page B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved level mounted stage part.val
    kindBase portBase dem sup dig ps atP kindRoom portRoom kindFit portFit
  have selectedRow : (T₀).row bestIndex=PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀:=
    (T₀).row_chosen (du m₀)
  unfold shrinkParty at ready
  rw [selectedRow] at ready
  refine ⟨ready,?_,fields.2.2.1⟩
  have activeSlot : J.party.motif < (wordAt post (selected J post).kernel 3).val := by
    rw [atSlot,kernelCount]
    exact slot.isLt
  have maskWidth : J.party.party < W := by
    rw [atP]
    exact lt_of_lt_of_le part.val.isLt (le_trans (by decide : 6 ≤ 8) wide)
  apply (partyActive_iff J post (lt_trans activeSlot (wordAt post (selected J post).kernel 3).isLt)
    (Nat.pow_lt_pow_right (by decide) maskWidth)
    (lt_of_lt_of_le (by decide : 2<2^8) (Nat.pow_le_pow_right (by decide) wide))).2
  refine ⟨activeSlot,?_⟩
  rw [atP]
  exact fields.2.2.2.trans (@decide_eq_true _ (Classical.propDecidable _) part.property)


open HistoryPartyBatchExec HistoryPartySpecialization

/-- The selected row before and after one real batch boot. The literal kind,
quota and accounting addresses survive both the checks and the payload boot. -/
structure RecordedBoot {K₁ : Type} [Field K₁] [Fintype K₁] {w height₀ n ar letters : ℕ}
    (run : Build w) (lib : HistoryStaticArchive.Catalog K₁ n ar) (copies : ℕ) (t : Fin (height₀+1))
    (counts : Fin letters→ℕ) (inc row hist : ℕ) : Prop where
  read : HistoryPartySpecialization.Reads run.regs (numeric run.bootImage) lib copies t
  grid : ∀j:Fin 7,numeric run.bootImage (run.regs.grid+j.val)=run.kind.words j
  quota : ∀ j : Fin letters, numeric run.bootImage (numeric run.bootImage (run.regs.incident+1)+j.val)=counts j
  active : HistoryPartyBatch.occupied run.layout (numeric run.input)
  count : numeric run.input (HistoryPartyBatch.incident run.layout (numeric run.input)+3)=copies
  kindAt : ∀j:Fin 7,numeric run.input (HistoryPartyBatch.shape run.layout (numeric run.input)+j.val)=run.kind.words j
  record : HistoryPartyBatch.incident run.layout (numeric run.input)=inc
  table : HistoryPartyBatch.shape run.layout (numeric run.input)=row
  histogram : numeric run.input (HistoryPartyBatch.incident run.layout (numeric run.input)+1)=hist
  inputQuota : ∀ j : Fin letters, numeric run.input (hist+j.val)=counts j
  level : t.val=Diagonal.HistogramTileNetwork.siteHeight copies run.kind.digit

set_option maxHeartbeats 2400000 in
include H saved oldCaps baseFit wide capFits offset rowPtr apart preserved mounted stage in
/-- Read the selected checks/payload ROM header and the chosen histogram at batch boot.
Dyadic and archive room are numerical, and every table value comes from the issued rows. -/
theorem recorded_batch (part : {j : Fin 6 // partySite P₀ lay₀ m₀ j=site}) (side : Bool)
    (hp : Diagonal.HistogramTileNetwork.siteHeight (shrinkRecordCopies T₀ s rem A m₀) (tileAt).bitCap≤height)
    (kindAddr : J.party.kinds=(g₀).kinds)
    (ps : J.party.parties=6) (atP : J.party.party=part.val.val)
    (rawPtr : HistoryPartyBatch.incident J.party (numeric post)=baseRow)
    (live : J.party.motif<numeric post (HistoryPartyBatch.kernel J.party (numeric post)+3))
    (span : baseRow+6≤2^W)
    (kindFit : ∀k:Fin 7,((shrinkParty T₀ bestIndex part.val).kind (arity B)).words k<2^W)
    (seed : J.party.seed+37<2^W)
    (lut : J.party.lutBase=start+StableCompactROMNative.size height)
    (counter : J.party.countBase=start+StableCompactROMNative.size height+staticSize B)
    (step : J.party.lutStride=HistoryStaticArchive.stride (arity B))
    (len : HistoryStaticArchive.stride (arity B)≤2^W)
    (powRoom : 2^(Diagonal.HistogramTileNetwork.siteHeight (shrinkRecordCopies T₀ s rem A m₀) (tileAt).bitCap)<2^W)
    (shapeRoom : ∀j,HistoryCompactorCounts.words F
      (⟨Diagonal.HistogramTileNetwork.siteHeight (shrinkRecordCopies T₀ s rem A m₀) (tileAt).bitCap,
        Nat.lt_succ_of_le hp⟩ : Fin (height+1)) j<2^W)
    (incFree : baseRow+4≤J.party.seed ∨ J.party.seed+37≤baseRow)
    (kindFree : (g₀).kinds+7*((bestIndex).val*6+part.val.val)+7≤J.party.seed ∨ J.party.seed+37≤(g₀).kinds+7*((bestIndex).val*6+part.val.val))
    (libFree : J.party.lutBase+staticSize B≤J.party.seed ∨ J.party.seed+37≤J.party.lutBase)
    (countsFree : J.party.countBase+HistoryCompactorCounts.size height≤J.party.seed ∨ J.party.seed+37≤J.party.countBase)
    (histFree : c.dense+ordinal*K+Fintype.card (tileAt).Alphabet≤J.party.seed ∨ J.party.seed+37≤c.dense+ordinal*K)
    (denseHold : ∀ (i : Fin (shrinkBinaryFamily T₀ s D rem hD small A).motifs)
      (v : (shrinkBinaryFamily T₀ s D rem hD small A).alphabet i),
      let addr:=c.dense+i.val*K+(Fintype.equivFin _ v).val
      addr≠c.header+27 ∧ addr≠cur.val ∧ addr≠ctr.val ∧ hdr≤addr ∧ addr<(en₀).next.heap ∧ post addr=final addr) :
    let k:=(shrinkParty T₀ bestIndex part.val).kind (arity B)
    let run : Build W:=⟨J.party,side,k,post⟩
    let t : Fin (height+1) := ⟨Diagonal.HistogramTileNetwork.siteHeight
      (shrinkRecordCopies T₀ s rem A m₀) (tileAt).bitCap, Nat.lt_succ_of_le hp⟩
    RecordedBoot run (HistoryStaticArchive.all F (arity B)) (shrinkRecordCopies T₀ s rem A m₀) t
      (fun j:Fin (Fintype.card (tileAt).Alphabet)=>
        ((shrinkIssuedBranch T₀ s D rem hD small A branch m₀).val ((Fintype.equivFin _).symm j)).val)
      baseRow ((g₀).kinds+7*((bestIndex).val*6+part.val.val)) (c.dense+ordinal*K) := by
  let k:=(shrinkParty T₀ bestIndex part.val).kind (arity B)
  let t : Fin (height+1) := ⟨Diagonal.HistogramTileNetwork.siteHeight
    (shrinkRecordCopies T₀ s rem A m₀) (tileAt).bitCap, Nat.lt_succ_of_le hp⟩
  have info:=recorded_fields B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved part.val
  have read (j:Fin 6) : (wordAt post (selected J post).incident j.val).val=numeric post (HistoryPartyBatch.incident J.party (numeric post)+j.val) := by
    change (post (((selected J post).incident + (j.val : Word W)).val)).val =
      (post (HistoryPartyBatch.incident J.party (numeric post)+j.val)).val
    rw [rawPtr, rowPtr, ← Nat.cast_add, Fin.val_cast_of_lt (show baseRow+j.val < 2^W by
      have hj := j.isLt
      omega)]
  have tNo : numeric post (HistoryPartyBatch.incident J.party (numeric post)+2)=(bestIndex).val:=(read 2).symm.trans info.2.1
  have shape : HistoryPartyBatch.shape J.party (numeric post)=(g₀).kinds+7*((bestIndex).val*6+part.val.val):=by
    unfold HistoryPartyBatch.shape;rw [kindAddr,tNo,ps,atP]
  have mask : HistoryPartyBatch.occupied J.party (numeric post):=by
    refine ⟨live,?_⟩
    have bit := info.2.2.2.trans (@decide_eq_true _ (Classical.propDecidable _) part.property)
    rw [show (wordAt post (selected J post).incident 5).val=numeric post (HistoryPartyBatch.incident J.party (numeric post)+5) from read 5,
      Nat.testBit_eq_decide_div_mod_eq] at bit
    rw [atP];exact of_decide_eq_true bit
  have kinds (j:Fin 7):numeric post (HistoryPartyBatch.shape J.party (numeric post)+j.val)=k.words j:=by
    rw [shape,numeric,Mounted.kindAt mounted stage (f:=shrinkParty T₀) rfl bestIndex part.val j,Fin.val_cast_of_lt (kindFit j)]
  have row := (T₀).row_chosen (du m₀)
  have digits : k.words 4=(tileAt).bitCap:=by
    dsimp only [k,shrinkParty]
    rw [row]; rfl
  have counts := recorded_histogram B s D rem hD small A cur ctr before issued final post c branch
    hdr H saved m₀ denseHold
  have readHist:=HistoryRefreshEmitter.elected_histogram J.party k post side mask seed (c.dense+ordinal*K)
    (Fintype.card (tileAt).Alphabet) _ ((read 1).symm.trans info.1)
    counts (by rwa [rawPtr]) histFree
  have data:=HistoryRefreshEmitter.elected_reads J.party k post side (HistoryStaticArchive.all F (arity B))
    (shrinkRecordCopies T₀ s rem A m₀) (tileAt).bitCap t mask ((read 3).symm.trans info.2.2.1)
    ((kinds 4).trans digits) rfl powRoom seed step len kinds (lut.symm ▸ stored_scalar B mounted.words)
    (by rw [counter];exact stored_counts B mounted.words) shapeRoom (by rwa [rawPtr]) (by rwa [shape])
    libFree countsFree
  refine ⟨data.1,data.2,readHist,mask,(read 3).symm.trans info.2.2.1,kinds,rawPtr,shape,
    (read 1).symm.trans info.1,counts,?_⟩
  change Diagonal.HistogramTileNetwork.siteHeight _ (tileAt).bitCap =
    Diagonal.HistogramTileNetwork.siteHeight _ k.digit
  rw [show k.digit=(tileAt).bitCap from digits]

private abbrev recordedRoleAt (T : ShrinkMotif.Table F) (row : T.Row) (party : Fin 6) : Party F :=
  let demand := (Fintype.equivFin (demandGraph.Port party)).symm
  let supply := (Fintype.equivFin (supplyGraph.Port party)).symm
  Party.ofTile demandGraph ShrinkMotif.supply party (T.base row) (T.block row)
    demand supply (fun q => (demand q).1.1.val) (fun q => (supply q).1.1.val)

local notation "recOf" party:arg => recordedRoleAt T₀
  (PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀) party

open Resident
private theorem recorded_port_word {w n : ℕ} {x : Word w} (value : x.val = n) :
    x = (n : Word w) := by
  subst n
  exact (Fin.cast_val_eq_self x).symm

set_option maxHeartbeats 800000 in
include H saved oldCaps baseFit wide capFits offset rowPtr apart preserved in
/-- Both incoming demand and outgoing supply widths of each actual selected ROM port.
Padding and capacity use the entries of the grid that selected this tile. -/
theorem recorded_widths (party : Fin 6) (page ar : ℕ)
    (loaded : HistoryGatherExecution.ReadPage J post (recOf party) ar page)
    (active : partyActive J post)
    (dem : J.demandCap=(G₀ level).demand) (sup : J.supplyCap=(G₀ level).supply)
    (dig : J.digitCap=(G₀ level).digits)
    (mode : J.mode=.shrink S₀) (stride : J.histogramStride=K) (positive : 0<K) (strideFit : K<2^W)
    (geometry : GeometryFrame x₀ (pointers K c x₀) issued post)
    (kernel : (post (selected J post).kernel.val).val=(pointers K c x₀).ownHeader)
    (demands : ∀e:Fin 2,post ((pointers K c x₀).demands+ordinal*2+e.val)=
        issued ((pointers K c x₀).demands+ordinal*2+e.val))
    (cap : ∀e:Fin 8,issuedWords m₀ e<2^W) :
    Fintype.card (demandGraph.Port party)≤J.demandCap ∧
    Fintype.card (supplyGraph.Port party)≤J.supplyCap ∧
    (∑i,baseAt ((dp party) i).val.1)≤J.digitCap ∧
    (∀i : Fin (Fintype.card (demandGraph.Port party)),(physicalWidth J post false i.val).val=du m₀ ((dp party) i).val.1) ∧
    (∀i : Fin (Fintype.card (supplyGraph.Port party)),(physicalWidth J post true i.val).val=issuedWords m₀ ((sp party) i).val.1) := by
  have mem : shrinkParty T₀ bestIndex party ∈ (G₀ level).rows := grid_has (shrinkParty T₀) bestIndex party
  have bound:=(G₀ level).caps mem
  have selectedRow : (T₀).row bestIndex=PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀:=
    (T₀).row_chosen (du m₀)
  have selectedParty : shrinkParty T₀ bestIndex party = recOf party :=
    congrArg (fun row => recordedRoleAt T₀ row party) selectedRow
  rw [selectedParty] at bound
  have capD : (recOf party).demands≤J.demandCap:=dem.symm ▸ bound.1
  have capS : (recOf party).supplies≤J.supplyCap:=sup.symm ▸ bound.2.1
  have fields:=recorded_fields B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved party
  refine ⟨capD,capS,dig.symm ▸ bound.2.2,?_,?_⟩
  · intro q
    have here:=loaded.demand capD q active
    exact HistoryGatherExecution.shrink_demand_width_at T₀ s D rem hD small A branch H J mode post geometry kernel m₀ q.val
      ((dp party) q).val.1 here.1 stride positive strideFit fields.1 (recorded_port_word here.2) (demands _)
  · intro q
    have here:=loaded.supply capS q active
    exact HistoryGatherExecution.shrink_supply_width_at T₀ s D rem hD small A branch H J mode post geometry kernel m₀ q.val
      ((sp party) q).val.1 here.1 stride positive strideFit fields.1 (recorded_port_word here.2) (cap _)


set_option maxHeartbeats 800000 in
include H saved oldCaps baseFit wide capFits offset rowPtr apart preserved in
/-- Every live gather cell in a bounded port loop has its concrete scheduled width,
and its native address is in the admitted demand or issued-width table. -/
theorem recorded_port_limits (party : Fin 6) (page ar floor volume : ℕ)
    (loaded : HistoryGatherExecution.ReadPage J post (recOf party) ar page)
    (active : partyActive J post)
    (dem : J.demandCap=(G₀ level).demand) (sup : J.supplyCap=(G₀ level).supply)
    (dig : J.digitCap=(G₀ level).digits) (mode : J.mode=.shrink S₀)
    (stride : J.histogramStride=K) (positive : 0<K) (strideFit : K<2^W)
    (geometry : GeometryFrame x₀ (pointers K c x₀) issued post)
    (kernel : (post (selected J post).kernel.val).val=(pointers K c x₀).ownHeader)
    (demands : ∀e:Fin 2,post ((pointers K c x₀).demands+ordinal*2+e.val)=
        issued ((pointers K c x₀).demands+ordinal*2+e.val))
    (di : ∀e,du m₀ e≤volume) (si : ∀e,issuedWords m₀ e≤volume) (wordRoom : volume<2^W)
    (loD : floor≤(pointers K c x₀).demands) (loS : floor≤(pointers K c x₀).supply) :
    (∀ side i,i<HistoryGatherExecution.cap J side→(physicalWidth J post side i).val≤volume) ∧
    (∀ side i,i<HistoryGatherExecution.cap J side→portActive J post side i→
      floor≤ issuedCell J post side i) := by
  have live:=recorded_widths B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved level party page ar loaded active dem sup dig
    mode stride positive strideFit geometry kernel demands (fun e=>(si e).trans_lt wordRoom)
  have fields:=recorded_fields B s D rem hD small A cur ctr before issued final post c branch hdr H saved
    site O slot J oldCaps baseFit wide capFits offset rowPtr apart preserved party
  have actual (side : Bool) (i : ℕ) (hi : i<HistoryGatherExecution.cap J side)
      (on : portActive J post side i) :
      i<(if side then Fintype.card (supplyGraph.Port party) else Fintype.card (demandGraph.Port party)) := by
    have ext:=loaded.extent
    simp only [HistoryPortCatalogue.stride] at ext
    have fits : i<2^W := by cases side <;>dsimp [HistoryGatherExecution.cap] at hi <;>omega
    have count:=((portActive_iff J post side i fits).mp on).2
    have index : side.toNat<HistoryPortCatalogue.stride J.demandCap J.supplyCap J.digitCap :=
      by cases side <;> simp [HistoryPortCatalogue.stride]; omega
    rw [loaded.word side.toNat index] at count
    cases side <;> exact count
  constructor
  · intro side i hi
    by_cases enabled:portActive J post side i
    · have k:=actual side i hi enabled
      cases side with
      | false =>exact (live.2.2.2.1 ⟨i,k⟩).le.trans (di _)
      | true =>exact (live.2.2.2.2 ⟨i,k⟩).le.trans (si _)
    · simp [physicalWidth,enabled]
  · intro side i hi on
    have k:=actual side i hi on
    cases side with
    | false =>
      let v : Fin (Fintype.card (demandGraph.Port party)):=⟨i,k⟩
      have port:=loaded.demand live.1 v active
      let e:=((dp party) v).val.1
      have cell:=HistoryGatherExecution.shrink_issued_address T₀ s D rem hD small A branch H J post geometry kernel
        m₀ i false e.val stride positive strideFit fields.1 (recorded_port_word port.2) e.isLt
      rw [cell];exact loD.trans (Nat.le_add_right ..)
    | true =>
      let v : Fin (Fintype.card (supplyGraph.Port party)):=⟨i,k⟩
      have port:=loaded.supply live.2.1 v active
      let e:=((sp party) v).val.1
      have cell:=HistoryGatherExecution.shrink_issued_address T₀ s D rem hD small A branch H J post geometry kernel
        m₀ i true e.val stride positive strideFit fields.1 (recorded_port_word port.2) e.isLt
      rw [cell];exact loS.trans (Nat.le_add_right ..)

end PublishedParty
end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
