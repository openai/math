import OAI.ThreeFlat.Diagonal.ShrinkPublishedIncidents
import OAI.ThreeFlat.Diagonal.ShrinkPublishedHalves
import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
import OAI.ThreeFlat.Diagonal.ShrinkRecordBase
import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.PhysicalIncidentWidth
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.Diagonal.NavigationStageBounds
import OAI.ThreeFlat.Diagonal.CompressorHalfPorts
import OAI.ThreeFlat.RAM.NavigationNodeRows

namespace OAI
/-! # Numbered successor sites and the child, half-width and motif rows of a shrink layer -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.ShrinkStage.DescriptorSpan Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav NavigationNodeRows
open scoped Classical BigOperators Fin.NatCast
noncomputable section
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
set_option quotPrecheck false
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (B).Base
local notation "P" => shrinkRecordPacking s rem A
local notation "d" => (2^s:ℕ)
local notation "k" => (2*d+1:ℕ)
local notation "hc" => palette_two s
local notation "S" => shrinkStage s D
local notation "t" => tagBits d
local notation "x" => dims S N t rem
local notation "prior" => shrinkRecordWidth s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A
variable {W K : ℕ} (cur : Word W) (m : Memory W) (c : Cursor) (branch : Fin (shrinkBinary T s D rem hD small A).rules.count)
local notation "en" => allocate K c (.shrink x)
local notation "lay" => ShrinkMotif.chooseWidths (supply branch)
local notation "layer" => nodeLayer K c (.shrink x)
local notation "f" => DescriptorSpan.fields K c x lay
local notation "packSite" => Computability.VPVNP.Compression.Site (B).Base (BitWord t) (BitWord rem)

def shrinkPackOrder : packSite ≃ Fin (x).outputSites :=
  (Equiv.prodAssoc (B).Base (BitWord t) (BitWord rem)).symm.trans
    (RefreshStageLayout.pair (RefreshStageLayout.pair (B).order (tagOrdinal t)) (tagOrdinal rem))

theorem shrinkPackOrder_val (v : packSite) :
    (shrinkPackOrder s D rem A v).val=Incidents.siteNumber (B).order v := by
  have outer := RefreshStageLayout.pair_index
    (RefreshStageLayout.pair (B).order (tagOrdinal t)) (tagOrdinal rem) ((v.1,v.2.1),v.2.2)
  have inner := RefreshStageLayout.pair_index (B).order (tagOrdinal t) (v.1,v.2.1)
  refine outer.trans ((congrArg (fun n : ℕ => n*2^rem+(tagOrdinal rem v.2.2).val) inner).trans ?_)
  unfold Incidents.siteNumber
  ac_rfl

def shrinkNextOrder : ((M).next branch).Base×BitWord rem ≃ Fin (x).outputSites :=
  (RefreshStageLayout.pair ((M).next branch).order (tagOrdinal rem)).trans
    (finCongr (by
      change Fintype.card ((M).next branch).Base * 2^rem = Fintype.card (B).Base * 2^t * 2^rem
      rw [shrinkBinary_next_base T s D rem hD small A branch,shrink_record_base s rem A]))

theorem shrinkNextOrder_val (v : ((M).next branch).Base×BitWord rem) :
    (shrinkNextOrder T s D rem hD small A branch v).val=Halves.siteNumber ((M).next branch).order v := by
  exact RefreshStageLayout.pair_index ((M).next branch).order (tagOrdinal rem) v

def shrinkArchiveSites : ((M).next branch).ArchiveSites :=
  ⟨layer,((M).next branch).chart.symm.trans (shrinkNextOrder T s D rem hD small A branch)⟩

def shrinkLayerData (O : ∀v:packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order lay v W) : LayerData layer where
  child j i := let site := (shrinkPackOrder s D rem A).symm j
    c.node+ChildRows.oldNumber P (B).order (Owner.childOrder P lay site i).val
  halfWidth j := let next := (M).next branch
    let site := (shrinkNextOrder T s D rem hD small A branch).symm j
    List.ofFn (fun a:Fin (2*D)=>next.width (Halves.sourceHalf next.graph site a))
  motifCopies j := let site := (shrinkPackOrder s D rem A).symm j
    List.ofFn (fun a : Fin (Incidents.siteKeys («S» := shrinkStage s D) (w:=W) P (B).order lay site).length=>
      shrinkRecordCopies T s rem A ((O site).equiv a).val)

private theorem ordered_half_sum {degree lanes count : ℕ} (state : State degree lanes)
    (order : state.Base × BitWord lanes ≃ Fin count) (v : state.Site) :
    (List.ofFn (fun j : Fin (2*degree) => state.width
      (Halves.sourceHalf state.graph (order.symm (order (state.chart.symm v))) j))).sum =
        state.incidentWidth v := by
  rw [order.symm_apply_apply, List.sum_ofFn]
  exact half_total state.graph state.width (state.chart.symm v)

/-- The two halves of the actual successor node charge the outgoing and incoming arc
widths of that same physical site, including each occurrence of a loop. -/
theorem shrinkLayerData_half_sum (O : ∀v:packSite,Incidents.SiteOrder («S» := shrinkStage s D) P (B).order lay v W) (v : ((M).next branch).Site) :
    ((shrinkLayerData T s D rem hD small A (K:=K) c branch O).halfWidth
      ((shrinkArchiveSites T s D rem hD small A (K:=K) c branch).ord v)).sum=((M).next branch).incidentWidth v := by
  exact ordered_half_sum ((M).next branch) (shrinkNextOrder T s D rem hD small A branch) v


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
