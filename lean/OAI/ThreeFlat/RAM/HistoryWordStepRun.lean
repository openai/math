import OAI.ThreeFlat.RAM.HistoryStageTariff
import OAI.ThreeFlat.Diagonal.ShrinkWordWires
import OAI.ThreeFlat.Diagonal.NavigationRecordedWordStep
import OAI.ThreeFlat.RAM.HistoryWordStepStored
import OAI.ThreeFlat.RAM.HistoryWordStepResult
import OAI.ThreeFlat.Diagonal.HistoryStageChartWires
import OAI.ThreeFlat.RAM.HistoryStageNumericRun

namespace OAI
/-! # The native join and cache of a physical chronological word step -/
namespace ThreeFlat.RAM.HistoryWordStepRun
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction Diagonal.PhysicalStage Diagonal.TickWorkspace
open HistoryStageRoot HistoryStageBody HistoryStageSetup HistoryStageSnapshots
open HistoryPartyBatchExec HistoryStageBody.Physical HistoryStageBankArena HistoryBoundedBody
open HistoryStageShapeWires NavigationNodeRows
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pins E : Type} [Field F] {d l D lanes W : ℕ} {S : State d l} {R : Move F S D lanes}
  {branch : Fin R.rules.count} (L : S.Words Pins) (step : R.WordStep Pins L branch)
  {old : S.ArchiveSites} {charge : (R.next branch).Site→ℕ} (record : R.ArchiveStep branch old charge)
  (v : (R.next branch).Site) (u seedCount : ℕ) (bank : Archive) (family : Family) (m : Memory W)
  (trees : Forest F L.ports.form) (orig : ∀ x,Fin (L.ext x)→E) (pointer : E→ℕ) (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "A" => Physical.layout u bank family
local notation "C" => family.childBound
local notation "V" => volume u
local notation "T" => numInput A C (numeric m)
local notation "X" => HistoryStageSetup.run A C m
local notation "B" => (X).compiled
local notation "z" => Move.WordStep.targetSite (R:=R) (i:=branch) v
local notation "D₀" => step.stage
local notation "N" => fun k=>((D₀).tapeFactor trees z k).compile
local notation "ar" => (D₀).tapeArity trees z
local notation "wire" => (D₀).tapePin trees z
local notation "q" => Typed.copy T (numeric m) N wire
local notation "ops" => Tape.tape (W:=W) N wire tag q
local notation "produced" => adjust A C T .result ((B).output ops)
local notation "Y" => childCount T (numeric m)
local notation "idx" => record.sites.id v
local notation "target" => NodeValue.ofSite (Run.nodeOfSite step.words (step.nextForest trees)
  (Run.pushedOrigin step orig) v) pointer (T).stream (T).ext

private theorem cast_half {inputShape outputShape : Shape} (e : outputShape=inputShape) (U : PortLayout inputShape Pins) (v : inputShape.Site) :
    ((e.symm ▸ U : PortLayout outputShape Pins)).halfBits ((Equiv.cast (congrArg Shape.Site e)).symm v)=U.halfBits v := by
  cases e;rfl

/-- Both native receipt constructors install the numerical port map used by the
bounded-join opcode. The archived family selects its literal shrink or refresh table. -/
theorem recorded_wires {K hEnd eEnd : ℕ} {cur ctr : Word W} {issuedMemory : Memory W}
    {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd issuedMemory Pins allow
      R branch L step old charge record) :
    At L.ports D₀ z (step.words.ext v) := by
  rcases visit with sh|rf
  · exact sh.wires v
  · cases rf with
    | native receipt limit frame bounds oldArrays words permitted =>
      apply refreshBinary_assembler_wires

/-- The numerical wire equation comes from the literal shrink or refresh receipt's
recharted stage. The native source tables, the older selected children, and all
inherited endpoints are read in their actual physical chronological order. -/
theorem run_priced_above {K hEnd eEnd : ℕ} {cur ctr : Word W} {issuedMemory : Memory W} {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd issuedMemory Pins allow
      R branch L step old charge record) (order : step.ChildOrder record)
    (g : Ranges u idx bank family m N q) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (b : Banks) (directory : DirectoryRow b record.sites.layer (record.sites.ord v) m)
    (source : record.data.Reads (numeric m)) (nodes : b.nodes=base u 44)
    (countRoom : record.sites.layer.childCount<2^W)
    (listRoom : record.sites.layer.children+(record.sites.ord v).val*record.sites.layer.childCount<2^W)
    (ports : HistoryStageRoot.Ports L.ports ((R.target_eq branch).symm ▸ step.words.ports)
      (D₀).count (D₀).child z T (numeric m))
    (childSize : ∀ k : Fin record.sites.layer.childCount,L.ext (record.row.children v k).val≤V)
    (child : ∀ k : Fin record.sites.layer.childCount,let id:=record.data.child (record.sites.ord v) k
      (NodeValue.ofSite (Run.nodeOfSite L trees orig (record.row.children v k).val) pointer
        (streamAt u seedCount id) (endsAt u seedCount id)).Cached tag u id m)
    (rootPins : (atResult (numeric m) (T).kernel).pins=(D₀).rootWidth z)
    (rootRows : (atResult (numeric m) (T).kernel).rows=((D₀).root z).compile.cells)
    (rootBits : (atResult (numeric m) (T).kernel).bits=((D₀).root z).compile.internal)
    (kernel : HistoryCompiledRows.Records tag ((D₀).root z).compile (atResult (numeric m) (T).kernel).stream m)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→base u 20≤numeric m (HistoryStageRoot.node T+3)+k)
    (incident : ∀ j : Fin 2,base u 20≤numeric m (HistoryStageRoot.node T+6)+j.val)
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      base u 20≤HistoryStageBounds.lastIncident T (numeric m)+j)
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : ((D₀).assemble trees z).compile.internal<2^W)
    (pins : step.words.ports.form.width v<2^W) (ids : ∀ tt,tag tt<2^W)
    (rowVolume : 4*(∑ k,(N k).cells)≤V) (large : 162≤V) (exts : step.words.ext v≤V) :
    (HistoryStageBody.join A C W).Exec m produced ((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops)) ∧
      (target).Cached tag u idx produced ∧
    (X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops) ≤
      (6*StageRun.rootRate A C)*(step.nextForest trees v).resources := by
  have wires:=recorded_wires L step record v visit
  have baseNodes : (T).nodeBase=b.nodes:=nodes.symm
  have prior (k : Fin record.sites.layer.childCount) : ∃ stream ext,
      (NodeValue.ofSite (Run.nodeOfSite L trees orig (record.row.children v k).val) pointer stream ext).Cached
        tag u (record.data.child (record.sites.ord v) k) m:=⟨_,_,child k⟩
  obtain ⟨stored,arity,ends⟩:=stage_stored L step record order v T u m b trees orig pointer tag
    directory source g.join.index baseNodes rfl countRoom listRoom prior rootPins rootRows rootBits kernel
  have ancestry:=stage_endpoint_sources L step record order v u seedCount bank family m b directory source g.join.index
    nodes countRoom listRoom g.join.arena large trees orig pointer tag childSize child
  have eqn:=(step.originOrder v).choose
  have ext : outer T (numeric m)=step.words.ext v:=ports.external.trans eqn.symm
  have fresh:=ports.fresh.trans (cast_half (R.target_eq branch) step.words.ports v)
  have actual : outPins T (numeric m)=step.words.ports.form.width v:=by rw [outPins,ext,fresh];rfl
  have pair:=HistoryWordStepResult.forest_pair step trees v
  have parent:=actual.trans (congrArg Sigma.fst pair).symm
  have native:=At.wiring trees T (numeric m) wires ports.degree ext parent arity ends
  have small : (D₀).hidden z<2^W:=by change (D₀).hidden z+(∑ k,(N k).internal)<2^W at bits;omega
  obtain ⟨⟨exec,rawRows⟩,loaded⟩:=HistoryStageNumericRun.run_source_above u idx bank family m N wire tag g native stored head cells inputs
    earlier listCells incident last widths small (lt_of_eq_of_lt (congrArg Sigma.fst pair) pins) ids rowVolume
  have finalRows:=HistoryWordStepResult.records step trees v produced tag (T).stream rawRows
  have shape:=HistoryWordStepResult.values step trees v T (numeric m) m tag native stored ext
  have cacheSpace:=Ranges.resultSpace_above u idx bank family m N wire tag q g earlier listCells incident last
  have endAt : (T).stream+V=(T).ext:=by
    have bankSector (b : ℕ) :
        HistoryScratch.sector family.motifs family.parties ⟨0,0,5,b⟩=160+b := by
      simp [HistoryScratch.sector]
    change base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,0⟩)*V+0+V =
      base u 12+((T).id*V+HistoryScratch.sector family.motifs family.parties ⟨0,0,5,1⟩)*V+0
    rw [bankSector,bankSector]
    ring
  have cellCount:=congrArg (fun x : (Σ k,BitNetwork F k)=>x.2.cells) pair
  have bitCount:=congrArg (fun x : (Σ k,BitNetwork F k)=>x.2.internal) pair
  change (∑ k,(N k).cells)=(step.nextForest trees v).compile.cells at cellCount
  change ((D₀).assemble trees z).compile.internal=(step.nextForest trees v).compile.internal at bitCount
  have words (j : Fin 6) : result T (numeric m) j<2^W:=by
    rw [shape]
    have lim : 20*Diagonal.TickWorkspace.stride u<2^W:=g.join.words
    have bud : V+400+32*(C+1) ≤ Diagonal.TickWorkspace.stride u:=g.join.scratch
    have ee : (T).ext+V≤14*Diagonal.TickWorkspace.stride u:=g.extEnd
    fin_cases j
    · change (T).stream<2^W;omega
    · exact pins
    · change (step.nextForest trees v).compile.cells<2^W;omega
    · change (step.nextForest trees v).compile.internal<2^W
      exact lt_of_eq_of_lt bitCount.symm bits
    · change (T).ext<2^W;omega
    · change step.words.ext v<2^W;omega
  have paid:=(X).stage_cost_from_ports A rfl L.ports ((R.target_eq branch).symm ▸ step.words.ports)
    D₀ trees z ports tag q head loaded
  have tariff := congrArg (fun n : ℕ => (6*StageRun.rootRate A C)*n)
    (HistoryWordStepResult.resource_eq step trees v)
  exact ⟨exec,Physical.cached_at u idx bank family m N wire tag q g.join cacheSpace cells large head
    (fun k=>by rw [endAt];exact (g.dest k).2) target shape words rfl exts ancestry finalRows,le_trans paid (le_of_eq tariff)⟩

/-- The numerical wire equation comes from the literal shrink or refresh receipt's
recharted stage. The native source tables, the older selected children, and all
inherited endpoints are read in their actual physical chronological order. -/
theorem run_priced {K hEnd eEnd : ℕ} {cur ctr : Word W} {issuedMemory : Memory W} {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd issuedMemory Pins allow
      R branch L step old charge record) (order : step.ChildOrder record)
    (g : Ranges u idx bank family m N q) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (b : Banks) (directory : DirectoryRow b record.sites.layer (record.sites.ord v) m)
    (source : record.data.Reads (numeric m)) (nodes : b.nodes=base u 44)
    (countRoom : record.sites.layer.childCount<2^W)
    (listRoom : record.sites.layer.children+(record.sites.ord v).val*record.sites.layer.childCount<2^W)
    (ports : HistoryStageRoot.Ports L.ports ((R.target_eq branch).symm ▸ step.words.ports)
      (D₀).count (D₀).child z T (numeric m))
    (childSize : ∀ k : Fin record.sites.layer.childCount,L.ext (record.row.children v k).val≤V)
    (child : ∀ k : Fin record.sites.layer.childCount,let id:=record.data.child (record.sites.ord v) k
      (NodeValue.ofSite (Run.nodeOfSite L trees orig (record.row.children v k).val) pointer
        (streamAt u seedCount id) (endsAt u seedCount id)).Cached tag u id m)
    (rootPins : (atResult (numeric m) (T).kernel).pins=(D₀).rootWidth z)
    (rootRows : (atResult (numeric m) (T).kernel).rows=((D₀).root z).compile.cells)
    (rootBits : (atResult (numeric m) (T).kernel).bits=((D₀).root z).compile.internal)
    (kernel : HistoryCompiledRows.Records tag ((D₀).root z).compile (atResult (numeric m) (T).kernel).stream m)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+k))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric m (HistoryStageRoot.node T+6)+j.val))
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+j))
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : ((D₀).assemble trees z).compile.internal<2^W)
    (pins : step.words.ports.form.width v<2^W) (ids : ∀ tt,tag tt<2^W)
    (rowVolume : 4*(∑ k,(N k).cells)≤V) (large : 162≤V) (exts : step.words.ext v≤V) :
    (HistoryStageBody.join A C W).Exec m produced ((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops)) ∧
      (target).Cached tag u idx produced ∧
    (X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops) ≤
      (6*StageRun.rootRate A C)*(step.nextForest trees v).resources :=
  run_priced_above L step record v u seedCount bank family m trees orig pointer tag
    visit order g head cells inputs b directory source nodes countRoom listRoom ports childSize child
    rootPins rootRows rootBits kernel earlier
    (fun k hk=>(listCells k hk).1) (fun j=>(incident j).1) (fun h j l r=>(last h j l r).1)
    widths bits pins ids rowVolume large exts

theorem run {K hEnd eEnd : ℕ} {cur ctr : Word W} {issuedMemory : Memory W} {allow : StaticMotif F→Prop}
    (visit : Diagonal.NavigationPass.RecordedWordStep K cur ctr hEnd eEnd issuedMemory Pins allow
      R branch L step old charge record) (order : step.ChildOrder record)
    (g : Ranges u idx bank family m N q) (head : (X).Header)
    (cells : SourceCells A C T (numeric m) W) (inputs : ∀ j,(T).words j<2^W)
    (b : Banks) (directory : DirectoryRow b record.sites.layer (record.sites.ord v) m)
    (source : record.data.Reads (numeric m)) (nodes : b.nodes=base u 44)
    (countRoom : record.sites.layer.childCount<2^W)
    (listRoom : record.sites.layer.children+(record.sites.ord v).val*record.sites.layer.childCount<2^W)
    (ports : HistoryStageRoot.Ports L.ports ((R.target_eq branch).symm ▸ step.words.ports)
      (D₀).count (D₀).child z T (numeric m))
    (childSize : ∀ k : Fin record.sites.layer.childCount,L.ext (record.row.children v k).val≤V)
    (child : ∀ k : Fin record.sites.layer.childCount,let id:=record.data.child (record.sites.ord v) k
      (NodeValue.ofSite (Run.nodeOfSite L trees orig (record.row.children v k).val) pointer
        (streamAt u seedCount id) (endsAt u seedCount id)).Cached tag u id m)
    (rootPins : (atResult (numeric m) (T).kernel).pins=(D₀).rootWidth z)
    (rootRows : (atResult (numeric m) (T).kernel).rows=((D₀).root z).compile.cells)
    (rootBits : (atResult (numeric m) (T).kernel).bits=((D₀).root z).compile.internal)
    (kernel : HistoryCompiledRows.Records tag ((D₀).root z).compile (atResult (numeric m) (T).kernel).stream m)
    (earlier : ∀ k,k<Y→numeric m (numeric m (HistoryStageRoot.node T+3)+k)<(T).id)
    (listCells : ∀ k,k<Y→NavigationCell u (numeric m (HistoryStageRoot.node T+3)+k))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric m (HistoryStageRoot.node T+6)+j.val))
    (last : 0<numeric m (numeric m (HistoryStageRoot.node T+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T (numeric m)+j))
    (widths : ∀ k,2+ar k+(N k).internal<2^W) (bits : ((D₀).assemble trees z).compile.internal<2^W)
    (pins : step.words.ports.form.width v<2^W) (ids : ∀ tt,tag tt<2^W)
    (rowVolume : 4*(∑ k,(N k).cells)≤V) (large : 162≤V) (exts : step.words.ext v≤V) :
    (HistoryStageBody.join A C W).Exec m produced ((X).prepareCost+(B).ticks ops+writeCost A C T .result ((B).output ops)) ∧
      (target).Cached tag u idx produced := by
  have result:=run_priced L step record v u seedCount bank family m trees orig pointer tag
    visit order g head cells inputs b directory source nodes countRoom listRoom ports childSize child
    rootPins rootRows rootBits kernel earlier listCells incident last widths bits pins ids rowVolume large exts
  exact ⟨result.1,result.2.1⟩


end
end ThreeFlat.RAM.HistoryWordStepRun

end OAI
