import OAI.Computability.BorderVNP.PackedNativeDemandImage
import OAI.Computability.BorderVNP.FiniteProfileCommonLabels

/-! # The public traffic rows of the signed network after actual directory publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP BurstRAM TeamContraction ProcessorSlots PackedHistoryCircuit Packing RoutingOutputs Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical Packing.Directory BorderVNP.Cube
open Cube.Physical Cube.MeanChoice Cube.LabelIndex
open private transfer_rows from OAI.Computability.BorderVNP.FiniteProfileCommonLabels
open scoped Classical

variable {D s n d k b w : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (a : CubeArena.Layout) (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin a.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin n)
    (F : Fields s a.cables n a.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (wordFit : b ≤ w) (positive : 0<a.cells)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (pub : Arg → Word w) (base origin gap : ℕ) (before mid : Memory w)

local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "pr" => privateLayout head origin a.cables a.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tables" => bases origin a.cables a.cells dir.entries
local notation3 (prettyPrint := false) "pp" => ISA.placement (readings mid) (pr).raw
local notation3 (prettyPrint := false) "lp" => ISA.placement (readings mid) (tables).livePairs
local notation3 (prettyPrint := false) "rows" => dir.directory pp lp
local notation3 (prettyPrint := false) "published" => readings (ISA.publish mid head base rows)
local notation3 (prettyPrint := false) "geometry" => LabelIndex.layout head published
local notation3 (prettyPrint := false) "list" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds

include net ids wireFit hk wordFit positive liveWidth in
set_option maxHeartbeats 850000 in
/-- The real returned private-placement RAM determines every label input. Its
data receiver and width are the original signed demand row's receiver and
width, independently of the chosen physical exterior. The sparse IDs and the
canonical numerical cell enumeration address the hardware directory itself. -/
theorem signed_published_mean_rows {I : Type} [Fintype I] {sc : I → Fin a.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {pins}
    (write : SlottedWriter a dir pp lp pins pub mid base sc sid sw)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (placed : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin a.cables a.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates ≤ origin) (originFits : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w) (literal : dir.literal<2^w)
    (cells : a.cells≤2^w) (stride : a.cellStride≤2^w) :
    list = rows ∧ ∃ (count : (geometry).cells=a.cells) (ep : Endpoints geometry published)
      (edges : N.CrossingEdge cell ↪ Fin (geometry).cableCount) (data : Fin (list).length ≃ Fin (geometry).deliveryCount),
      RowPlacement (networkRows N cell recv (fun i : Fin (list).length => list[i.val].width))
        (fromTables geometry published ep) (finCongr count.symm) (edges.sumMap data.toEmbedding) := by
  have same := NativeDemands.rows_eq_native N cell edgeID portID dir original live gap aux siteID F x
    head origin (readings before) (readings mid) net ids wireFit bounds liveWidth img placed fit
  have chosen := FiniteDiagonal.slotted_label_placement a dir N cell aux siteID edgeID portID F x net ids wireFit
    hk wordFit positive original live liveWidth pub base origin gap before mid write img placed fit hdr scratch
    originFits teams procs fields literal cells stride
  obtain ⟨count,ep,edges,data,receiver,cellID,network⟩ := chosen
  exact ⟨same,count,ep,transfer_rows N cell list rows same recv
    (NativeDemands.receiver_val N cell edgeID portID dir original live gap bounds) geometry published count ep
    ⟨count,ep,edges,data,receiver,cellID,network⟩⟩

include net ids wireFit hk wordFit positive liveWidth in
set_option maxHeartbeats 950000 in
/-- The common input rows retain the particular occupied cable slot used
by the original signed packet at each crossing.
All four directory pointers/counts are read from the actual published RAM. -/
theorem signed_published_cable_rows {I : Type} [Fintype I] {sc : I → Fin a.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {pins}
    (write : SlottedWriter a dir pp lp pins pub mid base sc sid sw)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (placed : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin a.cables a.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates ≤ origin) (originFits : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w) (literal : dir.literal<2^w)
    (cells : a.cells≤2^w) (stride : a.cellStride≤2^w) :
    (geometry).cables=origin ∧ (geometry).cableCount=a.cables ∧ (geometry).deliveries=base ∧
      (geometry).deliveryCount=(list).length ∧ ∃ (count : (geometry).cells=a.cells)
        (ep : Endpoints geometry published) (edges : N.CrossingEdge cell ↪ Fin (geometry).cableCount)
        (data : Fin (list).length ≃ Fin (geometry).deliveryCount),
        (∀ e, (edges e).val=(edgeID e.val).val) ∧
        RowPlacement (networkRows N cell recv (fun i : Fin (list).length => list[i.val].width))
          (fromTables geometry published ep) (finCongr count.symm) (edges.sumMap data.toEmbedding) := by
  have same := NativeDemands.rows_eq_native N cell edgeID portID dir original live gap aux siteID F x
    head origin (readings before) (readings mid) net ids wireFit bounds liveWidth img placed fit
  have num : (rows).length ≤ dir.candidates := dir.directory_length_le pp lp
  have low : head+112 ≤ base := write.rawStart
  have early : head+11<origin := by omega
  have src : readings before (head+8)=base :=
    (private_before_ends placed _ (by dsimp [bases]; omega)).symm.trans write.pointers.1
  obtain ⟨ca,cc,de,rc,cn⟩ := chooser_header (readings before) mid rows hdr src early (by omega) placed (by omega)
  change (geometry).cables=origin at ca
  change (geometry).cableCount=a.cables at cc
  change (geometry).deliveries=base at de
  change (geometry).deliveryCount=(rows).length at rc
  change (geometry).cells=a.cells at cn
  let named : LabelIndex.Layout :=
    {geometry with cables:=origin,cableCount:=a.cables,deliveries:=base,deliveryCount:=(list).length,cells:=a.cells}
  have dataCount := rc.trans (congrArg List.length same.symm)
  have unchanged (l : LabelIndex.Layout) (v e u t c : ℕ) (h₁ : v=l.cables) (h₂ : e=l.cableCount)
      (h₃ : u=l.deliveries) (h₄ : t=l.deliveryCount) (h₅ : c=l.cells) :
      {l with cables:=v,cableCount:=e,deliveries:=u,deliveryCount:=t,cells:=c}=l := by
    subst_vars
    rfl
  have numbered : named=geometry := unchanged _ _ _ _ _ _ ca.symm cc.symm de.symm dataCount.symm cn.symm
  have shortRows : base+7*(list).length ≤ origin :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 7 ((congrArg List.length same).le.trans num)) base).trans scratch
  let wordsFit (rs : List Directory.Row) := ∀ i : Fin rs.length,∀ j ∈ rs[i.val].words,j<2^w
  have rawFits : wordsFit list := (congrArg wordsFit same).mpr
    (FiniteDiagonal.slotted_row_words write teams procs fields literal cells stride)
  obtain ⟨ep,data,model⟩ := NativeDemands.published_placement named N cell aux siteID edgeID portID F x net ids
    wireFit hk wordFit positive dir original live liveWidth bounds head gap (readings before) mid img placed fit
    rfl (by change head+9<origin; omega) (by change head+9<base; omega)
    (Or.inr shortRows) rawFits
  let image (names : LabelIndex.Layout) (rs : List Directory.Row) :=
    ∃ (count : names.cells=a.cells) (ep : Endpoints names (readings (ISA.publish mid head base rs)))
      (edges : N.CrossingEdge cell ↪ Fin names.cableCount) (data : Fin (list).length ≃ Fin names.deliveryCount),
      (∀ e, (edges e).val=(edgeID e.val).val) ∧
        RowPlacement (networkRows N cell recv (fun i : Fin (list).length => list[i.val].width))
          (fromTables names _ ep) (finCongr count.symm) (edges.sumMap data.toEmbedding)
  have fixed : image named list := ⟨rfl,ep,CableTriples.wireOrd N cell edgeID,data,fun _ => rfl,model⟩
  exact ⟨ca,cc,de,dataCount,(congrArg₂ image numbered same).mp fixed⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
