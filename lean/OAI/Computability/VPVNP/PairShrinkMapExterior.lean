import OAI.Computability.VPVNP.PairShrinkRoleMapActions
import OAI.Computability.VPVNP.PairSimulationMapScanAcceptance
import OAI.Computability.VPVNP.PairShrinkRoutedExterior

/-!
# Exterior scratch after the scheduled shrinking map scan

The scan runs the actions in the actual resident row order. The selected
job's fitted workspace and published operands protect every word below the
hidden storage that is outside the histogram, including all child arguments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.MapWitness

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots ShrinkMapImage.Registers
open ResidentMapLoop.Exact MapResidentRows NodeArguments
open scoped Fin.CommRing

variable {g w n t limit packetEnd : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (ord : B.Entry → Fin t) (i : Fin S.steps)
variable (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)
open private acceptanceBase from OAI.Computability.VPVNP.PairShrinkRoleMapActions
private noncomputable local instance exteriorBaseDecidable : DecidableEq X.Base :=
  acceptanceBase i X
set_option allowUnsafeReducibility true in
attribute [local reducible] exteriorBaseDecidable
set_option allowUnsafeReducibility true in
attribute [local irreducible] selectedLayout

local notation "side" => selectedLayout X B.shrink sel
local notation "F" => ShrinkVertexImage.matrixFamily B ord i
local notation "G" => ShrinkVertexImage.gatherFamily B ord i
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
variable (jobs : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
  ShrinkPartyNative.Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w)

local notation "entry" => jobInput (g := g) (w := w) B i X sel v hidden jobs
local notation "atRow" => rowEquiv (a := S.degreeExponent i.castSucc) (g := g) X side v
variable (mem : Memory w) (level term : Word w)
variable (src : MapRowSource X sel (selectedLayout X B.shrink sel) mem level term)
variable (hw : MapConstants.widthThreshold B.shrink ≤ w)
variable (pub : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v → Fin 5 → Word w)
variable (ok : ∀ q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v,
  ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
    (u := MotifConversion.repetitions B.shrink (ShrinkPreparedCall.widthsDemand X q.1.1)) B.shrink
    (ShrinkPreparedCall.widthsDemand X q.1.1) (sel q.1.1).val (jobs q).scratch
    (ShrinkMotifOrder.stateNumber X q.1.1).val
    (ShrinkCallDemandCells.cdBase X q.1.1 (jobs q).arena (jobs q).nodes))

set_option maxHeartbeats 1500000 in
-- Align each resident's dependent workspace with the input indexed by its party and motif.
/-- The genuine schedule workspace of each selected job in the row. -/
noncomputable def mapWorkspaces (q : X.packingData.ResidentMap side v) :
    MapHandlerOperand.Workspace (w := w) F demandMass_pos (entry q) :=
  ShrinkPartyNative.Job.mapWorkspace (a := S.degreeExponent i.castSucc)
    (b := S.degreeExponent i.succ) (g := g) (w := w) (n := n) (limit := limit)
    B (slotDegree S) ord X (S.shrink i) sel
    q.1.1 q.1.2 (jobs q) (q.2.symm ▸ hidden) (ok q)

set_option allowUnsafeReducibility true in
attribute [local irreducible] MapHandlerOperand.Workspace ShrinkVertexImage.matrixFamily

set_option maxHeartbeats 1800000 in
-- Instantiate the workspace at each selected row before it enters the scratch-dependent scan.
/-- The scheduled row with the fitted workspace at every resident occurrence. -/
noncomputable def fittedActions : List (Action w n) :=
  actions (g := g) (w := w) (endAddr := n) B ord i X sel v hidden jobs mem level term src hw pub
    fun q ↦ mapWorkspaces (g := g) (w := w) (n := n) (limit := limit) B ord i X sel v hidden
      jobs ok q

local notation "scheduled" => fittedActions (g := g) (w := w) (n := n) (limit := limit)
  B ord i X sel v hidden jobs mem level term src hw pub ok

set_option allowUnsafeReducibility true in
attribute [local irreducible] rowAction ShrinkPartyNative.Job.entryInput
  ShrinkPartyNative.Job.mapWorkspace

set_option maxHeartbeats 3000000 in
-- The action and workspace depend on the same physical row and its resident party.
/-- Every successful scheduled resident scan preserves the words below the hidden
storage outside the histogram. This applies to every incoming scratch value. -/
theorem scan_exterior (R : LeafArena.Regions) (node : Word w) (saved : Scratch w n)
    (labels : t ≤ R.histWords)
    (scratchHist : ∀ q, (jobs q).scratch.hist = R.histBase)
    (scratchBase : ∀ q, (jobs q).scratch.hidden = ShrinkCallABI.hiddenBase R n)
    (baseline : Word w → Word w) (packets : ∀ q, (jobs q).Packets packetEnd baseline)
    {T : IncidenceDirectory w} {origin : ℕ}
    (old : ∀ j : Fin (order X side v).length, let q := atRow j
      (jobs q).OldPublished (ShrinkCallABI.operands (slotDegree S)) (pub q)
        (rowOrdinalWord (a := S.degreeExponent i.castSucc) (g := g) (w := w) X side v j)
        mem level T origin)
    {events : List (Event w)} {out : Scratch w n}
    (run : scan (w := w) (endAddr := n) node scheduled saved = some (events, out))
    (address : Word w)
    (low : address.val < ShrinkCallABI.hiddenBase R n)
    (outside : address.val < R.histBase ∨ R.histBase + t ≤ address.val) :
    rawScratch out address = rawScratch saved address := by
  unfold fittedActions actions at run
  suffices h : rawScratch out address = rawScratch saved address +
      ∑ _j : Fin (order X side v).length, (0 : Word w) by simpa only [Finset.sum_const_zero,
        add_zero] using h
  refine scan_ofFn_add (endAddr := n) (n := (order X side v).length) node _
    (fun s ↦ rawScratch s address) (fun _ ↦ (0 : Word w)) ?_ run
  intro j initial trace next got
  let q := atRow j
  unfold mapWorkspaces jobInput at got
  have endHist : (jobs q).scratch.hist + t ≤ (jobs q).scratch.hidden := by
    rw [scratchHist q, scratchBase q]
    exact ShrinkResidentMemory.histogram_before_hidden R n t labels
  have under : address.val < (jobs q).scratch.staging :=
    (low.trans_le (scratchBase q).ge).trans_le (Nat.le_add_right ..)
  have away : address.val < (jobs q).scratch.hist ∨ (jobs q).scratch.hist + t ≤ address.val := by
    rwa [scratchHist q]
  exact (ShrinkPartyNative.Job.routed_preserves (g := g) (w := w) (endAddr := n)
    (n := n) (t := t) (limit := limit) (packetEnd := packetEnd) («side» := side)
    (T := T) (origin := origin) (baseline := baseline) (events := trace) (out := next)
    B ord i X sel q.1.1 q.1.2 (jobs q) (q.2.symm ▸ hidden) (ok q) hw (pub q) mem
    v level term src j initial (packets q) endHist (old j) got address under away).trans
    (add_zero _).symm

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
