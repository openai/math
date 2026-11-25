import OAI.Computability.BorderVNP.CellSparseExteriorSupplementalCost
import OAI.Computability.BorderVNP.CellSparseExteriorTeamCost

/-! # Native charge for the produced tasks with compressed exterior inputs

The seven-word row producer uses global cell ordinals in the physical owner
table. Its cost can therefore be summed in the same cell order as the
group-schedule geometry and delivery bounds. Each compressed field contributes
its encoded prefix and its actual count and individual-use suffix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open BorderVNP.Cube Cube.Physical Cube.TeamRowClock Crossing Packing.CellAddresses
open CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacketGeometry
open DiagonalTallyCellReports VPVNP.BurstRAM

private theorem assigned_cell_count {n m : ℕ} (same : n=m) (owner cost : ℕ → ℕ) (team : ℕ) :
    assignedSum (fun c : Fin n => owner c.val) team (fun c => cost c.val) =
      assignedSum (fun c : Fin m => owner c.val) team (fun c => cost c.val) := by
  subst m
  rfl

/-- Bound the native initializer and call-directory charges of the actual
compacted rows using the two geometry sorts, the scheduled deliveries, the
encoded supplied prefixes, and the original per-use power slots. -/
theorem prepared_nativeCharge_le {Site E I A : Type} [Fintype A] {s dim blocks b K h : ℕ}
    {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ}
    {D : LengthDeclaration dim g.groups} {label : Fin g.cells → Label (dim+1) g.groups}
    {recv : A → Fin g.cells} {incoming : A → ℕ}
    (schedule : GroupWeights.ScheduleResult g teams orig assigned)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (X w description : ℕ) (hw : 0 < w) (positive : 1 ≤ description)
    (pass : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X:ℚ)/256)
    (l : CellControlRows.Layout) (mem : ℕ → ℕ) (sl : Layout) (cells : ℕ → Owned)
    (places : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (cellCount : l.cells=g.cells) (teamId : l.team=team.val)
    (T : LiveWords.Template E I Site s (g.cells+1)) (site : Fin s → Fin (g.cells+1)) (arg : E → ℕ)
    (fields : Fin s → I → ℕ)
    (shape : TypedBatch.SourceFootprint (fun c => places c.val) (T.directory site arg fields))
    (p d : ℕ) (pf : (g.cells+1)+T.atoms.length+(g.cells+1) ≤ 2^p)
    (df : (g.cells+1)+(Schema.coords T.chunkLabels.length).length+(g.cells+1) ≤ 2^d)
    (rl : ReportLayout) (r : Fin g.cells → ReportCell rl) (cursor : Fin g.cells → LocalReportCursor)
    (bundleBase : Fin g.cells → ℕ) (memory : Fin g.cells → ℕ → ℕ)
    (rc : ∀ c : Fin g.cells, (places c.val).reports.length=rl.gadgets)
    (digits : ∀ c : Fin g.cells, ∀ v ∈ (places c.val).reports, v.length=rl.countWidth)
    (tail : ∀ c : Fin g.cells, assigned (teams.owners+(label c D.1).val)=team.val → (cells c.val).field.tail.length=(r c).tailWidth)
    (hidden : BitDelivery (fun j : (c : Fin g.cells) × Fin ((places c.val).boxes.filterMap Sum.getRight?).length => j.1)
      (fun _ => description) recv incoming)
    (bundles : BitDelivery (fun j : (c : Fin g.cells) × Fin (r c).bundles.length => j.1)
      (fun _ => description) recv incoming)
    (f : CellDispatch.Frame) (m mt : Memory w)
    (stored : ∀ i < l.before mem l.cells, (supplementalRow l mem sl cells places geom extra i).typed.cell.Stored m)
    (body : ∀ c < l.cells, l.owner mem c=l.team → ∀ j,
      (places c).headerWidth+(boxBody ((places c).factors j)).length ≤ description)
    (limit R H B : ℕ) :
    let owner := fun c : Fin g.cells => assigned (teams.owners+(label c D.1).val)
    (∀ c : Fin g.cells, l.owner mem c.val=owner c) →
    assignedSum owner team.val (fun c => (cells c.val).field.prefix.length) ≤ limit →
    (∀ c, owner c=team.val → extra c.val=bindingRows (r c).bundles (cursor c)) →
    (∀ c, owner c=team.val → bundleInputs w rl description (r c).bundles (cursor c) (bundleBase c) (memory c)) →
    (((c : {c : Fin g.cells // owner c=team.val}) × UsePositions (r c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B) →
    Supplement.Batch.nativeCharge (supplementalRow l mem sl cells places geom extra) f mt (l.before mem l.cells) ≤
      64+11*f.count+100*(l.before mem l.cells)+
        308*(2*(w+1)*(2^p+2^d)+18*(w+1)*X+2*X+limit+R*(H*B)) := by
  intro owner owners supplied bindings input original
  let compact (c : Fin g.cells) := (cells c.val).placed sl (places c.val)
  have exterior (c : Fin g.cells) (hc : owner c=team.val) : (compact c).external.length =
      (cells c.val).field.prefix.length+(r c).tailWidth := by
    change (cells c.val).field.bytes.length = _
    rw [Field.bytes_eq,List.length_append,tail c hc]
  have shapes := TypedBatch.real_geometry_counts_of_footprint T site arg fields places shape pf df
  have units := TypedBatch.prepared_by_width schedule image team X w description positive pass
    compact p d shapes rl r cursor bundleBase memory rc digits (fun c => (cells c.val).field.prefix.length)
    limit exterior hidden bundles R H B supplied input original
  let cost (c : ℕ) := Supplement.units ((cells c).placed sl (places c)) (extra c) w description
  have paid : assignedSum (fun c : Fin l.cells => l.owner mem c.val) l.team (fun c => cost c.val) ≤
      2*(w+1)*(2^p+2^d)+18*(w+1)*X+2*X+limit+R*(H*B) := by
    rw [assigned_cell_count cellCount (l.owner mem) cost,teamId,show (fun c : Fin g.cells => l.owner mem c.val)=owner
      from funext owners]
    apply le_trans _ units
    rw [TypedBatch.assigned_eq_sum,TypedBatch.assigned_eq_sum]
    apply Finset.sum_le_sum
    intro c hc
    change Supplement.units (compact c) (extra c.val) w description ≤ _
    rw [bindings c (Finset.mem_filter.mp hc).2]
  have native := produced_nativeCharge_le l mem sl cells places geom extra description f m mt hw stored body
  exact native.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 308 paid) _)

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
