import OAI.Hierarchy.HistorySelectedReached
import OAI.ThreeFlat.RAM.FoldShrinkCache

namespace OAI
/-! # Shrink and refresh visits of the reached receiver -/

namespace ThreeFlat.Diagonal.PhysicalStage.Run.StageOccurrence
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.NavigationPass Diagonal.TickWorkspace RAM RAM.NavigationNodeRows
open Diagonal.HistoryContraction Diagonal.NavigationDirectory HistoryPartyBatchExec HistoryStageBody.Physical
open HistoryStageSetup HistoryWordStepRun HistoryNodeDirectory.Selected NativeNavigation
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
variable {F Pins E : Type} [Field F] [Fintype F] {a l c k u K heads heap n fee levels degree : ℕ}
    {X : State a l} {R : Move F X c k} {i : Fin R.rules.count} {L : X.Words Pins}
    {step : R.WordStep Pins L i} {O : X.ArchiveSites} {pay : (R.next i).Site→ℕ}
    {row : R.ArchiveStep i O pay}
local notation "W" => (16*u^10)
local notation "V" => (volume u)
local notation "peak" => (2^((3*u^10+4)/5):ℕ)
local notation "tag₀" => HistoryRefreshEmitter.tag (K:=F)
local notation "rom" => base u 38
local notation "keep₀" => TickTerminalRoot.slotKeep u
variable (B : Block F) {cur ctr : Word (16*u^10)} {mid out warm prev : Memory (16*u^10)} {b : Banks}
    {xs : List NodeRow} {D₀ : HistoryNodeDirectory.Selected.Directory (16*u^10) n} {j : Fin n} {vals : Fin n→NodeValue F}
    (seedCount : ℕ) (trees : Forest F L.ports.form) (orig : ∀ x,Fin (L.ext x)→E)
    (pointer : E→ℕ) (v : (R.next i).Site)
local notation "node" => row.sites.id v
local notation "rnk" => row.sites.ord v
local notation "entry" => bump (ownerData W u) prev
local notation "srcNode" => nodeOfSite step.words (step.nextForest trees) (pushedOrigin step orig) v
local notation "childN" h:arg => NodeValue.ofSite (nodeOfSite L trees orig (row.row.children v h).val)
  pointer (streamAt u seedCount (row.data.child rnk h)) (endsAt u seedCount (row.data.child rnk h))

variable {shape : TraceBucketAtom.Layout} {pub : Fin TraceEndpointROM.params→Word (16*u^10)}
local notation "physical" => Source (K:=K) (heads:=heads) (heap:=heap) (levels:=levels) (fee:=fee)
  (degree:=degree) (cur:=cur) (ctr:=ctr) (xs:=xs) (D₀:=D₀) (j:=j) (vals:=vals)
  (b:=b) (mid:=mid) (out:=out) (warm:=warm) (prev:=prev) (step:=step) (row:=row)
  B seedCount trees orig pointer v shape pub


/-- A recovered nonleaf emits at the selected ID. Metadata, cost, gate stream
and inherited endpoint sources come from its own archived shrink/refresh receipt
and the reached ledger of older child caches. -/
theorem emitReceiver (s : physical) (leaf : PhysicalProcedure.Procedure W) :
    let arm := fun i : Fin n => B.nativeArmTime levels fee b (numeric out) i.val
    Hierarchy.HistorySelectedReceiverLoop.Emitted (u:=u)
      (archive B rom W K) leaf (families B rom W) D₀ vals tag₀
      (B.nativeVisitCost levels fee b (numeric out)) arm (fun i _=>arm i) j entry := by
  obtain ⟨⟨f,found⟩,real⟩ := write_selected (B:=B) (seedCount:=seedCount) (trees:=trees)
    (orig:=orig) (pointer:=pointer) (v:=v) s
  obtain ⟨o,chosen,saved,frame⟩ := real.result
  cases chosen with
  | seed miss _ => rw [found] at miss; contradiction
  | stage g hit run =>
    exact Hierarchy.HistorySelectedReceiverLoop.Emitted.ofStage g hit
      real.headerFits real.stageFits real.priced run saved frame

end
end ThreeFlat.Diagonal.PhysicalStage.Run.StageOccurrence

end OAI
