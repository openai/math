import OAI.Hierarchy.DescentRecordedPeriod
import OAI.Hierarchy.DescentTerminalSiteTokens
import OAI.Hierarchy.DescentReentryExteriorTokens
import OAI.Hierarchy.DescentGrainMeasurements

namespace OAI
/-! # Local scalar nodes and original hub pins on the selected chronological reset -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentKernelHistory DescentPacking DescentStageEdgeReceipt
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail p : ℕ}
variable {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (b : ClosedReset cap ctl) (issued : b.Recorded p) (a : Archive W)
local notation "key" => (DescentOrderedReset.grains W b.count b.order)
local notation "vertex" => (b.frame.host.symm.toEmbedding.trans cap.vertex)
local notation "rank" => ((b.reset.rawHostRank b.terminals vertex).trans Fin.valEmbedding)
local notation "rows" => (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) rank)
local notation "ps" => (DescentPhysicalOrder.rename (b.raw.siteFrom rows b.valid.coordinates))
local notation "rawId" => ((b.reset.nativeResetEdges b.terminals vertex key).order.trans Fin.valEmbedding)
local notation "pe" => (DescentPhysicalOrder.rename (DescentResetLocalOrder.allCode b.raw rawId S
  b.valid (b.raw.siteFrom rows b.valid.coordinates)))
local notation "old" => (fun v=>cap.placement.hub (cap.placement.pos v).2)
local notation "fresh" => (fun v=>b.next.placement.hub (b.next.placement.pos v).2)
local notation "rawTag" => (fun v=>b.raw.hub (b.raw.pos v).2)
local notation "inc" => (W.granular b.count (z*G.b) b.fit)
local notation "post" => (b.reset.orderedReentry b.terminals key)
local notation "ordinary" => (b.reset.orderedOrdinary b.terminals key)
local notation "count" => (fun e : (post).graph.Edge=>(post).graph.width e/b.reset.unit)
local notation "whole" => ((Nat.div_mul_cancel issued.divides).symm)

/-- The two native permutations come from the published site and edge tapes
of the same receipt as the scalar operation lists. -/
theorem resetArchive_tokenized (token : a.bit.Tokenized cap.placement.records) :
    (resetArchive b p issued.positive issued.divides a).bit.Tokenized b.next.placement.records := by
  let source:=BitDescription.granular W b.count (z*G.b) b.fit a.bit
  have pre : source.Tokenized cap.placement.records:=token
  let freshOps:=source.batchedReset b.reset b.terminals key (b.reset.unit/p) p issued.positive whole (resetMenu b)
  have installed : freshOps.Tokenized
      (b.reset.recipeRecords b.terminals cap.placement.records (b.reset.laneRecipe key _ p issued.positive whole)) := by
    exact BitDescription.Tokenized.reset source cap.placement.records b.reset b.terminals pre key _ _
      (b.reset.lane_valid key _ p issued.positive whole (resetMenu b))
  have raw : freshOps.Tokenized b.raw.records := fun v=>by rw [issued.sizes v];exact installed v
  have pieces:=BitDescription.Tokenized.split freshOps b.raw.records raw count b.reset.unit (b.reset.counts_fit b.terminals)
  exact BitDescription.Tokenized.renamed _ b.raw.records pieces ps pe

include issued in
theorem resetArchive_exterior (balance : W.HubExterior old) (owns : ∀x,old (W.graph.attach x)=true) :
    b.reblock.result.HubExterior fresh ∧ ∀x,fresh (b.reblock.result.graph.attach x)=true := by
  have same : b.reset.hub=old:=funext b.frame.originalHub
  have oldBalance : (inc).HubExterior b.reset.hub := by
    rw [same]
    intro v tag
    exact (MarkedWorld.granular_units W b.count (z*G.b) b.fit old
      (fun _ => ([] : List Unit)) 1 256 0 v).trans (balance v tag)
  have rawEq : rawTag=b.reset.reentryTag b.terminals:=funext issued.tagged
  have unbundled : (ordinary).HubExterior rawTag := by
    rw [rawEq]
    exact b.reset.ordinary_exterior_balance b.terminals oldBalance
  have attached : ∀x,rawTag ((ordinary).graph.attach x)=true := by
    intro x
    rw [rawEq]
    exact b.reset.reentry_exterior_owners b.terminals (fun y=>(b.frame.originalHub _).trans (owns y)) x
  refine ⟨PhysicalRename.hub_balance ordinary ps pe rawTag unbundled,?_⟩
  intro x
  change rawTag ((ps).symm ((ps) ((ordinary).graph.attach x)))=true
  rw [Equiv.symm_apply_apply]
  exact attached x

end
end Hierarchy.DescentSixParty.Chronology

end OAI
