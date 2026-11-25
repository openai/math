import OAI.ThreeFlat.Diagonal.PhysicalShrinkStagePrice
import OAI.ThreeFlat.Diagonal.PhysicalShrinkTilePrices
import OAI.ThreeFlat.Diagonal.PhysicalShrinkAssembly

namespace OAI
/-! # The paid price of the elected shrink kernel in its original graph coordinates -/

namespace ThreeFlat.Diagonal

private theorem fibre_sum_instances {α : Type*} {a b : Fintype α} (f : α → ℕ) :
    Finset.sum (@Finset.univ α a) f = Finset.sum (@Finset.univ α b) f := by
  cases Subsingleton.elim a b
  rfl

end ThreeFlat.Diagonal

namespace ThreeFlat.Diagonal.CompressorPacking
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression HistoryContraction MotifKernel MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 260000
set_option maxRecDepth 8000
set_option quotPrecheck false

variable {c d Q : ℕ} {V H Tag L F Pins : Type} [Field F] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c → ℕ)
    (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q) (bundled : ∀ m, (num m).1=P.bundle m)
    (base : P.Motif → Fin 2 → ℕ) (r : P.Motif → ℕ) (T : ∀ m, FixedMotifTile demandGraph supplyGraph (base m) F)
    (fits : ∀ m e, demandWidth P w num m e ≤ base m e*r m) {terms : ℕ} (hist : Fin terms ≃ Histories P base r T)
    (hn : ∀ a : Tag, -a=a) (good : TagConditions P.slots (shift P) P.offset) (n : Fin 4 → ℕ)
    (positive : ∀ i, 0<n i) (order : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ) (padding : LiftedSlots (V×Tag) pad L)
    (idx : Fin terms)

variable {U E : Type} [Fintype U] [Fintype E] {source : PortGraph U E} {width : E → ℕ}
    (I : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape (oldGraph P) w))
    (layout : WordLayout source width Pins)
    (edgeWidth : ∀ e,width e=w (I.edge e)) (keep : ∀ e z,(I.label e z).val=z.val)
variable (counts : Site V Tag L → ℕ) (ord : ∀ v, Fin (counts v) ≃ {i // P.placement (historyLayout P base r T (hist idx)) i=v})
    (sites : Site V Tag L → ℕ) (motifs : ∀ v, Fin (sites v) ≃ Active (partySite P (historyLayout P base r T (hist idx))) v)

local notation "metricStep" => histogramStep P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding
local notation "lay" => historyLayout P base r T (hist idx)
local notation "packed" => I.pushWord (G:=source) (H:=oldGraph P) (w:=width) (b:=w) layout
local notation "raw" => shrinkAssembly P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding idx packed counts ord sites motifs
local notation "fresh" => shrinkWordLayout (Pins:=Pins) P base r T hist hn good n order hc pad padding idx

def shrink_chart_cost (v : Site V Tag L) : ℕ :=
    (I.onStage (G:=source) (H:=oldGraph P) (w:=width) (b:=w) (R:=metricStep) (idx:=idx)
      layout raw edgeWidth keep).freshResources v

theorem shrink_chart_cost_le (v : Site V Tag L) (C u D : ℕ)
    (tiles : ∀ m : Active (partySite P lay) v, shrinkTariff P base T m.val ≤ C)
    (heights : ∀ m : Active (partySite P lay) v, HistogramTileNetwork.siteHeight (r m.val) (T m.val).bitCap ≤ u)
    (bounded : sites v ≤ D) :
    shrink_chart_cost P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding
      idx I layout edgeWidth keep counts ord sites motifs v ≤
      (2+(1+D+2*C*(D+1)))*(u+1)^3*
        (1+((packed).ports.hidden (R:=metricStep) (t:=idx) counts ord v+(fresh).ports.halfBits v)+
          ∑ m : Active (partySite P lay) v,r m.val) :=
  shrink_fresh_on_chart P w code hQ num bundled base r T fits hist hn good n positive order hc pad padding
    idx I layout edgeWidth keep counts ord sites motifs v C u D tiles heights bounded

section SelectedTable
attribute [local irreducible] historyLayout ShrinkMotif.chooseWidths motifNumbers demandWidth PhysicalShrink.picked
  Finset.sum Finset.univ Fintype.card Fintype.equivFin PhysicalShrink.r
open PhysicalShrink
open private count_pos from OAI.ThreeFlat.Diagonal.PhysicalShrink

variable (tab : ShrinkMotif.Table F) (hc' : 2≤c) (hd : 0<d)
local notation "number" => motifNumbers P code hc'
local notation "β" => widths tab P w code hc'
local notation "ρ" => PhysicalShrink.r tab P w code hc'
local notation "τ" => tile tab P w code hc'
variable {N : ℕ} (history : Fin N ≃ Hists tab P w code hc')
  (k : Fin N) (negtag : ∀ a : Tag,-a=a)
  (geo : TagConditions P.slots (shift P) P.offset)
  (degree : Fin 4 → ℕ) (degreePos : ∀ t,0<degree t) (rank : ShrinkEdge P degree ↪ ℕ)
  (extra : ℕ) (padded : LiftedSlots (V×Tag) extra L)
  (iso : HistoryRelabel.Iso (WordLayout.shape source width) (WordLayout.shape (oldGraph P) w))
  (ports : WordLayout source width Pins) (readAt : ∀ e,width e=w (iso.edge e))
  (pinAt : ∀ e x,(iso.label e x).val=x.val)

local notation "selectedLayout" => historyLayout P β ρ τ (history k)
variable (lanes : Site V Tag L→ℕ) (children : ∀ v,Fin (lanes v)≃{x // P.placement (historyLayout P (widths tab P w code hc') (PhysicalShrink.r tab P w code hc') (tile tab P w code hc') (history k)) x=v})
  (occupancy : Site V Tag L→ℕ) (members : ∀ v,Fin (occupancy v)≃Active (partySite P (historyLayout P (widths tab P w code hc') (PhysicalShrink.r tab P w code hc') (tile tab P w code hc') (history k))) v)

local notation "kernel" => histogramStep P w code (count_pos hd hc') number (motifNumbers_bundle P code hc')
  β ρ τ (PhysicalShrink.fits tab P w code hc') history negtag geo degree degreePos rank hc' extra padded
local notation "afterWords" => shrinkWordLayout (Pins:=Pins) P β ρ τ history negtag geo degree rank hc' extra padded k
local notation "beforeWords" => iso.pushWord (G:=source) (H:=oldGraph P) (w:=width) (b:=w) ports

def selected_chart_cost (site : Site V Tag L) : ℕ :=
  shrink_chart_cost (F:=F) (V:=V) (H:=H) (Tag:=Tag) (L:=L) (d:=d) (c:=c) (Q:=count (c:=c) (d:=d))
    (terms:=N) (U:=U) (E:=E) (source:=source) (width:=width) P w code (count_pos hd hc') number (motifNumbers_bundle P code hc')
    β ρ τ (PhysicalShrink.fits tab P w code hc') history negtag geo degree degreePos rank hc' extra padded
    k iso ports readAt pinAt lanes children occupancy members site

include readAt pinAt children members in
theorem selected_chart_charge (site : Site V Tag L) (C u D : ℕ)
    (priced : ∀ m : Active (partySite P selectedLayout) site,shrinkTariff P β τ m.val≤C)
    (heights : ∀ m : Active (partySite P selectedLayout) site,HistogramTileNetwork.siteHeight (ρ m.val) (τ m.val).bitCap≤u)
    (card : occupancy site≤D) (population : Fintype (Active (partySite P selectedLayout) site)) :
    selected_chart_cost P w code tab hc' hd history k negtag geo degree degreePos rank extra padded iso ports readAt pinAt
        lanes children occupancy members site ≤
      (2+(1+D+2*C*(D+1)))*(u+1)^3*(1+((∑ i : Fin (lanes site),(beforeWords).ports.halfBits ((children site) i).val)+
        (afterWords).ports.halfBits site)+Finset.sum (@Finset.univ _ population) (fun m => ρ m.val)) := by
  have rawFee := shrink_chart_cost_le (F:=F) (V:=V) (H:=H) (Tag:=Tag) (L:=L) (d:=d) (c:=c) (Q:=count (c:=c) (d:=d))
    (terms:=N) (U:=U) (E:=E) (source:=source) (width:=width) P w code (count_pos hd hc') number (motifNumbers_bundle P code hc')
    β ρ τ (PhysicalShrink.fits tab P w code hc') history negtag geo degree degreePos rank hc' extra padded
    k iso ports readAt pinAt lanes children occupancy members site C u D priced heights card
  exact rawFee.trans_eq (congrArg
    (fun copies : ℕ => (2+(1+D+2*C*(D+1)))*(u+1)^3*(1+((∑ i : Fin (lanes site),
      (beforeWords).ports.halfBits ((children site) i).val)+(afterWords).ports.halfBits site)+copies))
    (fibre_sum_instances (b:=population) (fun m : Active (partySite P selectedLayout) site => ρ m.val)))

end SelectedTable

end
end ThreeFlat.Diagonal.CompressorPacking

namespace ThreeFlat.Diagonal.PhysicalStage

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression CompressorPacking PhysicalShrink HistoryContraction MotifKernel
open MotifOuterTerms
open scoped Classical BigOperators
open private cpos from OAI.ThreeFlat.Diagonal.PhysicalStageShrink
open private count_pos from OAI.ThreeFlat.Diagonal.PhysicalShrink
noncomputable section

variable {F Pins : Type} [Field F] [Fintype F]

private theorem parallel_positive {c d D : ℕ} (hd : 0<d) (hD : 0<D)
    (small : ((2^c*d*d:ℕ):ℝ)/(D:ℝ)≤1/1024) (i : Fin 4) : 0<parallel c d D i :=
  (SlotEnergy.slotCount_mass (by positivity : 0<((2^c*d*d:ℕ):ℝ)/(D:ℝ)) small i).1

private theorem member_le_volume {α : Type*} [Fintype α] (qty : α → ℕ) (m : α) : qty m≤∑ a,qty a :=
  Finset.single_le_sum (fun a _=>Nat.zero_le (qty a)) (Finset.mem_univ m)

private theorem fibre_width_sum {U V S : Type} [Fintype U] [Fintype V] (chart : U ≃ V) (owner : V → S)
    (v : S) {n : ℕ} (order : Fin n ≃ {x : V // owner x=v}) (physical : V → ℕ) (width : U → ℕ)
    (read : ∀ x,physical (chart x)=width x) :
    (∑ i,physical (order i).val)=∑ x : {x : U // owner (chart x)=v},width x.val := by
  let sites : {x : U // owner (chart x)=v} ≃ {x : V // owner x=v} :=
    ⟨fun u=>⟨chart u.val,u.property⟩,
     fun z=>⟨chart.symm z.val,(congrArg owner (chart.apply_symm_apply z.val)).trans z.property⟩,
     fun u=>Subtype.ext (chart.symm_apply_apply _),fun z=>Subtype.ext (chart.apply_symm_apply _)⟩
  calc
    _ = ∑ x : {x : V // owner x=v},physical x.val := order.sum_comp _
    _ = ∑ x : {x : U // owner (chart x)=v},physical (chart x.val) := (sites.sum_comp (fun x=>physical x.val)).symm
    _ = _ := Finset.sum_congr rfl (fun x _ => read x.val)


namespace Block

variable (B : Block F) (level : Fin B.levels)
local notation "s" => B.exponent level.val
local notation "d" => 2^s
local notation "c" => 2*d+1
local notation "D" => 2^B.exponent (level.val+1)
local notation "T" => B.shrink
variable (W V : ℕ)
    (bitCaps : ∀k : Fin (B.shrink.more.length+1),(B.shrink.block (B.shrink.row k)).bitCap≤V)
    (fitsWord : V*max 1 V≤2^W)

variable {lanes rem hbits tags : ℕ} (A : State (2^(B.exponent level.val)) lanes)
    (u : BitWord lanes ≃+ BitWord (2*(2^(B.exponent level.val))+1) × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) (2^(B.exponent level.val)) (2*(2^(B.exponent level.val))+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset) (hd : 0<(2^(B.exponent level.val))) (hD : 0<(2^(B.exponent (level.val+1))))
    (small : ((2^(2*(2^(B.exponent level.val))+1)*(2^(B.exponent level.val))*(2^(B.exponent level.val)):ℕ):ℝ)/(((2^(B.exponent (level.val+1))) : ℕ):ℝ)≤1/1024) (tagSize : 1<2^tags)
    (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) (2^(B.exponent level.val)) (2*(2^(B.exponent level.val))+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*(2^(B.exponent level.val))+1) (2^(B.exponent level.val)) (2^(B.exponent (level.val+1)))) ↪ ℕ)
set_option quotPrecheck false
set_option maxRecDepth 10000
set_option maxHeartbeats 900000

local notation "hc" => cpos hd
local notation "old" => oldWidth A u
local notation "I" => StageAddress.shrinkInputIso A.graph A.chart u P agree A.width
local notation "base" => widths T P old code hc
local notation "many" => r T P old code hc
local notation "tiles" => tile T P old code hc
local notation "hist" => (Fintype.equivFin (shrinkBranches T A u P hd code)).symm
local notation "n" => parallel c d D
local notation "pad" => padding c d D
local notation "padded" => tagPadding (Native.adjacentMask tagSize) (Native.adjacent_ne tagSize) pad
local notation "positive" => parallel_positive hd hD small
local notation "hQ" => count_pos hd hc
local notation "nums" => motifNumbers P code hc
local notation "bundled" => motifNumbers_bundle P code hc
local notation "ok" => fits T P old code hc

variable (L : A.Words Pins) (idx : Fin (Fintype.card (shrinkBranches B.shrink A u P hd code)))
    (prev : A.Site→ℕ) (v : Site A.Base (BitWord tags) (BitWord rem))

local notation "lay" => historyLayout P base many tiles (hist idx)
local notation "packed" => (I).pushWord L
local notation "counts" => (fun _ : Site A.Base (BitWord tags) (BitWord rem) => d*2^c)
local notation "children" => (fun z => Owner.childOrder P lay z)
local notation "motifs" => Local.assemblyCount P lay
local notation "enum" => Local.assemblyOrder P lay
local notation "widthAt" => (fun e => (congrArg A.width ((StageAddress.splitEdge u).symm_apply_apply e)).symm)
local notation "fresh" => shrinkWordLayout (Pins:=Pins) P base many tiles hist binary_neg good n order hc pad padded idx
local notation "active" => Active (partySite P lay) v
local notation "copies" => (∑ a : active,many a.val)
local notation "fibre" => {x : A.Site // P.placement lay ((I).site x)=v}

attribute [local irreducible] Finset.sum Finset.univ Fintype.card Fintype.equivFin motifNumbers demandWidth PhysicalShrink.picked
attribute [local irreducible] selected_chart_cost historyLayout shrinkingGraph SlotRefinement.actualWidth allPieceSlots
  ShrinkMotif.chooseWidths PhysicalShrink.r Owner.childOrder Local.assemblyOrder shrinkSite

local notation "chartFee" => selected_chart_cost (V:=A.Base) (H:=BitWord hbits) (Tag:=BitWord tags) (L:=BitWord rem)
  («d»:=d) («c»:=c) (U:=A.Site) (E:=(A.Base × Fin d) × BitWord lanes) (source:=A.shape.graph) (width:=A.width)
  P old code T hc hd hist idx binary_neg good n positive order pad padded I L widthAt (fun _ _=>rfl)
  counts children motifs enum v
local notation "oldPorts" => ∑ i : Fin (counts v),(packed).ports.halfBits ((children v) i).val
local notation "scale" => 2+(1+B.shrinkMotifCap level+2*B.shrinkPrice*(B.shrinkMotifCap level+1))

include B level A u P agree hd code L idx v in
omit [Fintype F] in
private theorem packed_original_widths : oldPorts=∑ x : fibre,A.incidentWidth x.val := by
  have measured := fibre_width_sum (I).site (P.placement lay) v (children v) (packed).ports.halfBits A.incidentWidth
    (fun x => ((I).pushWord_halfBits L widthAt x).trans (A.words_incidentWidth L x))
  exact measured.trans (fibre_sum_instances (fun x : fibre => A.incidentWidth x.val))

include B level W V bitCaps fitsWord A u P agree good hd hD small tagSize code order L idx v in
set_option maxHeartbeats 1600000 in
omit [Fintype F] in
private theorem packed_chart_price (newWidth : ℕ) (bill : 1+newWidth+copies≤V) :
    chartFee ≤ scale*(W+1)^3*(1+(oldPorts+(fresh).ports.halfBits v)+copies) := by
  have tilePrice (m : active) : shrinkTariff P base tiles m.val≤B.shrinkPrice :=
    B.elected_tile_price P old code hc m.val
  have height (m : active) : HistogramTileNetwork.siteHeight (many m.val) (tiles m.val).bitCap≤W := by
    have one : many m.val≤copies := member_le_volume (fun a : active => many a.val) m
    exact B.elected_tile_height P old code hc m.val (one.trans ((Nat.le_add_left copies (1+newWidth)).trans bill)) bitCaps fitsWord
  exact selected_chart_charge (V:=A.Base) (H:=BitWord hbits) (Tag:=BitWord tags) (L:=BitWord rem)
    («d»:=d) («c»:=c) (U:=A.Site) (E:=(A.Base × Fin d) × BitWord lanes) (source:=A.shape.graph) (width:=A.width)
    P old code T hc hd hist idx binary_neg good n positive order pad padded I L widthAt (fun _ _=>rfl) counts children motifs enum v
    B.shrinkPrice W (B.shrinkMotifCap level) tilePrice height (elected_count_bound P lay v) (inferInstance : Fintype active)

omit [Fintype F] in
private theorem paid_chart_bound {α : Type} [Fintype α] (prev widths : α → ℕ)
    (actual before after copied newWidth W price : ℕ) (hidden : before=∑ a,widths a) (target : after=newWidth)
    (incoming : ∀ a,widths a≤prev a) (rate : price≤B.localCoefficient)
    (charge : actual≤price*(W+1)^3*(1+(before+after)+copied)) :
    actual≤(B.localCoefficient*(W+1)^3)*((1+newWidth+copied)+∑ a,prev a) := by
  subst before after
  exact B.local_cost_to_push prev widths (1+newWidth+copied) copied newWidth actual price W W incoming
    le_rfl le_rfl rate charge

include B level W V bitCaps fitsWord A u P agree good hd hD small tagSize code order L idx prev v
omit [Fintype F] in
/-- The installed kernel uses the elected histogram and the exact fibres of
the source chart. Its charged width can be read in any successor word order. -/
theorem paid_packed_shrink (newWidth : ℕ) (incoming : ∀ x,1+A.incidentWidth x≤prev x)
    (bill : 1+newWidth+copies≤V) (measure : (fresh).ports.halfBits v=newWidth) :
    chartFee ≤ (B.localCoefficient*(W+1)^3)*((1+newWidth+copies)+∑ x : fibre,prev x.val) := by
  exact B.paid_chart_bound (fun x : fibre => prev x.val) (fun x : fibre => A.incidentWidth x.val)
    chartFee oldPorts ((fresh).ports.halfBits v) copies newWidth W scale
    (by apply packed_original_widths) measure (fun x=>(Nat.le_add_left _ 1).trans (incoming x.val))
    (B.shrink_local_coefficient level)
    (B.packed_chart_price level W V bitCaps fitsWord A u P agree good hd hD small tagSize code order L idx v newWidth bill)

end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
