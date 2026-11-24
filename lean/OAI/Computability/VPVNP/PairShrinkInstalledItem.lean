import OAI.Computability.VPVNP.PairShrinkRouteABI
import OAI.Computability.VPVNP.PairShrinkReadyAfterGather
import OAI.Computability.VPVNP.PairSimulationShrinkScheduledItem
import OAI.Computability.VPVNP.PairShrinkLiveOperands

/-! # A scheduled matrix item at the site of an individual party -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion NetworkKernel CompressorRecords
open ShrinkBlockInputs ShrinkSlots ShrinkVertexImage ShrinkMapImage.Registers
open MapHandlerOperand MapResidentRows
open scoped Fin.CommRing

variable {w p r t n limit endAddr g : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (ord : B.Entry → Fin t) (stage : Fin S.steps)
variable {X : State (a stage) (packingLaneBits (a stage) g)}
variable (sel : X.ShrinkSelection B.shrink) {motif : X.packingData.Motif} {party : Fin 6}
variable (J : Job X B.shrink (S.shrink stage) sel motif party w)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "widths" => ShrinkPreparedCall.width B.shrink X sel
local notation "Fam" => matrixFamily B ord stage
local notation "Gather" => gatherFamily B ord stage
local notation "degree" => slotDegree S

variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel))
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) motif party))
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (ShrinkPreparedCall.widthsDemand X motif)) B.shrink
  (ShrinkPreparedCall.widthsDemand X motif) (sel motif).val J.scratch
  (ShrinkMotifOrder.stateNumber X motif).val (ShrinkCallDemandCells.cdBase X motif J.arena J.nodes))
local notation "call" => Job.entryInput B X (S.shrink stage) sel motif party J hidden
local notation "work" =>
  Job.mapWorkspace B degree ord X (S.shrink stage) sel motif party J hidden ok

variable (pc : GatherAddress (matrixFamily B ord stage) (gatherFamily B ord stage) → Fin p)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
  (locals : Fin (maps B ord stage).code.privateRegs ↪ Fin r) (ret : Fin p)
  (M : Machine w p r 11)
local notation "cm" => Function.Embedding.trans (gatherShared Fam Gather) locals
local notation "own" => Function.Embedding.trans (gatherMatrix Fam Gather) locals
local notation "gr" => Function.Embedding.trans (gatherLocal Fam Gather) locals
local notation "tmp" => locals (layoutTemp Fam Gather)
local notation "key" => MapHandlerOperand.index demandMass_pos call
local notation "lp" => loop Fam mapRegisters (corePC Fam Gather pc) cm ret

variable (v : MapResidentRows.Site X) (mem : Memory w) (level term : Word w)
variable (source : MapRowSource X sel (selectedLayout X B.shrink sel) mem level term)
  (i : Fin (order X (selectedLayout X B.shrink sel) v).length) (P : Fin 5 → Word w)
  (hw : MapConstants.widthThreshold B.shrink ≤ w) (inv : Word w → Config w p r → Prop)
local notation "st" => rowOrdinalWord (w := w) (a := a stage) (g := g) X side v i
local notation "src" => rowCursor X sel side v mem level term source i
local notation "action" => rowAction (endAddr := endAddr) Fam Gather X sel v mem level term
  source i call J hw P work
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout rowOrdinalWord

set_option maxHeartbeats 3000000 in
-- The fixed matrix input and the gathered workspace carry the same stage and party.
/-- The concrete job supplies its exact matrix action, including the external
row dispatch and the native memory frame on both branches. -/
theorem Job.installedItem
    (link : GatherLinked Fam Gather mapRegisters pc dfs saved cm own gr tmp ret M)
    (ds : ∀ j k, locals j ≠ dfs k) (ss : ∀ j k, locals j ≠ saved k)
    (positive : 0 < w) (atRow : (MapResidentRows.entry X side v i) = (motif, party))
    (allowed : ℕ → Prop)
    (safe : ∀ c k, (J.row c k).ReadSafe
      (setups (ShrinkCallABI.operands degree) ShrinkCallABI.node (a stage) (b stage)
        party side c k) allowed P st mem)
    {T U : IncidenceDirectory w} {origin layer pitch : ℕ} {heads : SlotLevel.Heads}
    {absolute : Word w}
    (old : J.OldPublished (ShrinkCallABI.operands degree) P st mem level T origin)
    (next : J.SupplyPublished (ShrinkCallABI.operands degree) ShrinkCallABI.node P st mem
      heads absolute U layer pitch)
    (stack : endAddr ≤ J.scratch.hist) (hist : J.scratch.hist + t ≤ J.scratch.hidden)
    (live : ∀ node c, inv node c → LiveOperands (endAddr := endAddr)
      Fam mapRegisters dfs saved cm tmp call J P st mem level term work inv node c) :
    ResidentMapLoop.Exact.Item (endAddr := endAddr) lp M mem dfs inv src
      (fun _ s => action s) := by
  have banks := hosted_banks Fam Gather dfs saved locals ds ss
  have abi := route_abi B ord stage dfs saved locals ds ss key
  have atParty : (MapResidentRows.entry X side v i).2 = (call).party := congrArg Prod.snd atRow
  have grid : rowGrid (B := B.shrink) X side v i =
      demandGrid B.shrink demandMass_pos (call).demand :=
    congrArg (fun m => demandGrid B.shrink demandMass_pos (ShrinkPreparedCall.widthsDemand X m))
      (congrArg Prod.fst atRow)
  have room := J.call_bounds B degree ord X (S.shrink stage) sel motif party hidden ok
    mem P st level T origin old stack
  have histEnd := J.histogram_before_staging B degree ord X (S.shrink stage) sel motif party
    hidden ok hist
  exact exact_item (B := B.shrink) (g := g) (ready := S.shrink stage) (endAddr := endAddr)
    (jobMotif := motif) (absolute := absolute) (T := T) (U := U) (origin := origin)
    (layer := layer) (pitch := pitch) (heads := heads) («side» := side)
    Fam Gather mapRegisters pc dfs saved cm own gr tmp ret M link banks.1 banks.2.1
    X sel v mem level term source i call J hw P work inv positive banks.2.2 abi.1 abi.2.1 abi.2.2
    rfl atParty grid allowed safe old next room histEnd live

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
