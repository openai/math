import OAI.Computability.BorderVNP.CellSparseExteriorProducedCharge
import OAI.Computability.BorderVNP.CellSparseExteriorSignedScales
import OAI.Computability.BorderVNP.RoutingISAScheduleClockSparseCalls

/-! # The signed cell clock on the native sparse call and report programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open BorderVNP.Cube Cube.Physical Cube.TeamRowClock Crossing Packing.CellAddresses Packing.Directory
open CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source CellPacketGeometry
open DiagonalTallyCellReports Diagonal.ExternalSew.Fragments VPVNP.BurstRAM

/-- Identify the native compact task ordinals with the global cells selected by
the actual group-schedule owner words. -/
noncomputable def programOrder {C : ℕ} (l : CellControlRows.Layout) (mem : ℕ → ℕ)
    (owner : Fin C → ℕ) (team : ℕ) (cellCount : l.cells=C) (teamId : l.team=team)
    (owners : ∀ c : Fin C, l.owner mem c.val=owner c) :
    Fin (l.before mem l.cells) ≃ {c : Fin C // owner c=team} :=
  (TypedTaskBuilder.ownedOrder l.toLayout mem).symm.trans ((finCongr cellCount).subtypeEquiv
    (fun c => by change l.owner mem c.val=l.team ↔ owner (Fin.cast cellCount c)=team
                 rw [←owners,teamId]; rfl))

/-- The numeric ordinal used by the exterior encoder and the report scan is the
global cell returned by the seven-word row producer. -/
theorem programOrder_val {C : ℕ} (l : CellControlRows.Layout) (mem : ℕ → ℕ)
    (owner : Fin C → ℕ) (team : ℕ) (cellCount : l.cells=C) (teamId : l.team=team)
    (owners : ∀ c : Fin C, l.owner mem c.val=owner c) (i : Fin (l.before mem l.cells)) :
    ((programOrder l mem owner team cellCount teamId owners i).val).val =
      TypedTaskBuilder.globalCell l.toLayout mem i.val := by
  rw [TypedTaskBuilder.globalCell,dite_eq_left i.isLt]
  rfl

/-- Bound the three native argument passes, the probes of their published bursts,
and report preparation in the true compact cell order. All encoded and expanded
loads are charged to the crossing ends, installed deliveries and original power slots. -/
theorem programCharge_le {Site E I A P : Type} [Fintype A] [Fintype P]
    {s dim blocks b K h z ne np nc : ℕ} {bits : P → ℕ}
    {g : GroupWeights.Layout} {teams : TeamNative.Layout} {orig assigned : ℕ → ℕ}
    {D : LengthDeclaration dim g.groups} {label : Fin g.cells → Label (dim+1) g.groups}
    {recv : A → Fin g.cells} {incoming : A → ℕ}
    (schedule : GroupWeights.ScheduleResult g teams orig assigned)
    (image : GroupWeights.PhysicalImage g orig blocks b K h D label recv incoming)
    (team : Fin (teams.r+1)) (X w description : ℕ) (hw : 0 < w) (positive : 1 ≤ description)
    (pass : TeamNative.unscale (assigned (teams.totals+team.val)) ≤ (X:ℚ)/256)
    (N : Network z P bits) (host : N.Site → Fin g.cells) (edgeID : N.Edge ↪ Fin ne)
    (portID : P ↪ Fin np) (ord : N.CrossingEdge host ≃ Fin nc)
    (cables : HostScatter.Layout) (bank supplied : ℕ → ℕ) (rows : List Row) (data : ℕ → ℕ → Bool)
    (rect : CableRows N host edgeID portID cables bank)
    (installed : RowLocations rows (Fin.val : Fin g.cells → ℕ) recv incoming)
    (cap : ∀ pair, load (cablePair ord (crossSrc N host) (crossDst N host) label)
      (crossWidth N host ∘ ord.symm) pair ≤ blocks*(h*b))
    (l : CellControlRows.Layout) (mem : ℕ → ℕ) (sl : Layout) (cells : ℕ → Owned)
    (places : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (cellCount : l.cells=g.cells) (teamId : l.team=team.val) (rowCount : sl.count=l.before mem l.cells)
    (source : ∀ c : Fin g.cells, assigned (teams.owners+(label c D.1).val)=team.val → (cells c.val).field.spans=spans (stream cables bank supplied rows) data c.val)
    (ordered : ∀ c : Fin g.cells, assigned (teams.owners+(label c D.1).val)=team.val → Ordered (cells c.val).field.width 0 (cells c.val).field.spans)
    (width : ∀ c : Fin g.cells, assigned (teams.owners+(label c D.1).val)=team.val → (cells c.val).field.width<2^w)
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
    (pub : Arg → Word w) (m mt : Memory w) (frameCount : (CellDispatch.Frame.ofMemory pub m).count=g.cells)
    (stored : ∀ i < l.before mem l.cells, (supplementalRow l mem sl cells places geom extra i).typed.cell.Stored m)
    (body : ∀ c < l.cells, l.owner mem c=l.team → ∀ j,
      (places c).headerWidth+(boxBody ((places c).factors j)).length ≤ description)
    (R H B : ℕ) (q : ReportCursor) (base : ℕ) (reportMem : ℕ → ℕ) :
    let owner := fun c : Fin g.cells => assigned (teams.owners+(label c D.1).val)
    ∀ owners : ∀ c : Fin g.cells, l.owner mem c.val=owner c,
    let order := programOrder l mem owner team.val cellCount teamId owners
    let reportRows := List.ofFn (fun i => r (order i).val)
    let os := fun i => cells (TypedTaskBuilder.globalCell l.toLayout mem i)
    let tasks := fun i => (supplementalRow l mem sl cells places geom extra i).typed
    (∀ c, owner c=team.val → extra c.val=bindingRows (r c).bundles (cursor c)) →
    (∀ c, owner c=team.val → bundleInputs w rl description (r c).bundles (cursor c) (bundleBase c) (memory c)) →
    (((c : {c : Fin g.cells // owner c=team.val}) × UsePositions (r c.val).bundles) ↪
      Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B) →
    cellInputs w description reportRows q base reportMem →
    Evaluator.ScheduleClock.sparseCallTicks sl os tasks (CellDispatch.Frame.ofMemory pub m) mt (l.before mem l.cells)+
      (prepareSetup.slots+cellTicks reportRows q+(writeFrame 32 60 61 35).slots) ≤
      5000*((w+1)*(2^p+2^d))+700000000*((w+1)*X)+500*(R*(H*B)) := by
  intro owner owners order reportRows os tasks bindings bundleInput original reportInput
  let field (c : Fin g.cells) := (cells c.val).field
  let volume := 2*(1000000*X/256)+X
  let limit := assignedSum owner team.val (fun c => (field c).prefix.length)
  have spansEq (c : Fin g.cells) (hc : owner c=team.val) : (field c).spans = _ := source c hc
  have active : assignedSum owner team.val (fun c => activeWidth (field c).spans) ≤ volume := by
    apply le_trans _ (active_load N host edgeID portID ord cables bank supplied rows data rect installed schedule image team X pass cap)
    rw [TypedBatch.assigned_eq_sum,TypedBatch.assigned_eq_sum]
    exact Finset.sum_le_sum fun c hc => (congrArg activeWidth (spansEq c (Finset.mem_filter.mp hc).2)).le
  have pos (c : Fin g.cells) (hc : owner c=team.val) (s : Span) (hs : s ∈ (field c).spans) : 0 < s.bits.length :=
    stream_positive cables bank supplied rows data c.val s (spansEq c hc ▸ hs)
  have prefixBound := team_prefix owner team.val w volume field ordered width pos active
  obtain ⟨publicWords,_⟩ := TypedBatch.real_geometry_counts_of_footprint T site arg fields places shape pf df owner team.val
  have tails : assignedSum owner team.val (fun c => (field c).tail.length) ≤ 2^p+R*(H*B) := by
    change assignedSum owner team.val (fun c => (cells c.val).field.tail.length) ≤ _
    apply le_trans _ (team_tails owner team.val order rl r (fun c => places c.val) rc digits publicWords original)
    rw [TypedBatch.assigned_eq_sum,TypedBatch.assigned_eq_sum]
    exact Finset.sum_le_sum fun c hc => (tail c (Finset.mem_filter.mp hc).2).le
  have rowFields (i : Fin (l.before mem l.cells)) : (os i.val).field=field (order i).val := by
    dsimp only [os,field]
    rw [programOrder_val l mem owner team.val cellCount teamId owners i]
  have compression := team_prepare owner team.val w volume (2^p+R*(H*B)) order field os rowFields pos active tails
  have native := prepared_nativeCharge_le schedule image team X w description hw positive pass l mem sl cells places geom
    extra cellCount teamId T site arg fields shape p d pf df rl r cursor bundleBase memory rc digits tail hidden bundles
    (CellDispatch.Frame.ofMemory pub m) m mt stored body limit R H B owners le_rfl bindings bundleInput original
  rw [frameCount] at native
  have incomingLoad := (assigned_input_bounds schedule image team X pass).1
  have reports := occurrence_charge owner team.val w description X positive order rl r recv incoming incomingLoad bundles
    (fun c => places c.val) publicWords rc digits R H B original q base reportMem reportInput
  have charged := Evaluator.sparse_cell_charge (by omega : g.cells≤2^p)
    ((l.before_le mem l.cells).trans_eq cellCount) prefixBound le_rfl native compression reports
  have actual : tasks = fun i => (os i).typed sl (Supplement.Batch.produced l mem places geom extra i).typed := rfl
  rw [actual,Evaluator.ScheduleClock.sparseCallTicks_eq_nativeCharge sl os (Supplement.Batch.produced l mem places geom extra),
    rowCount]
  exact charged

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
