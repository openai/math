import OAI.Computability.VPVNP.PairShrinkRoleMapActions
import OAI.Computability.VPVNP.PairSimulationShrinkRowFootprint

/-! # External memory of a scheduled shrinking action

The row selector enumerates exactly the resident actions. Each accepting
action concatenates its route, interval gather and matrix events. The
three read bounds therefore apply to the action at every scratch state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole.MapWitness

open BurstRAM DFS Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots ShrinkMapImage.Registers
open ResidentMapLoop.Exact MapResidentRows SourceTransport

variable {g : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  {t w endAddr : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)
  (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : X.ShrinkSelection B.shrink) (v : MapResidentRows.Site X)

private noncomputable local instance actionFootBase : DecidableEq X.Base := Classical.decEq _

local notation "side" => selectedLayout X B.shrink sel
local notation "F" => ShrinkVertexImage.matrixFamily B ord i
local notation "G" => ShrinkVertexImage.gatherFamily B ord i

variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel)) v)
  (jobs : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    ShrinkPartyNative.Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w)

variable (m : Memory w) (level term : Word w)
  (R : MapRowSource X sel (selectedLayout X B.shrink sel) m level term)
  (hw : MapConstants.widthThreshold B.shrink ≤ w)
  (pub : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v → Fin 5 → Word w)
  (workspace : (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v) →
    MapHandlerOperand.Workspace (w := w) (ShrinkVertexImage.matrixFamily B ord i)
      demandMass_pos (jobInput B i X sel v hidden jobs q))

local notation "row" j => rowEquiv X side v j
local notation "input" j => jobInput B i X sel v hidden jobs (row j)
local notation "key" j => MapHandlerOperand.index demandMass_pos (input j)
local notation "state" j => rowOrdinalWord (w := w) X side v j

set_option maxHeartbeats 1600000 in
-- Instantiate the native traces with the resident's dependent party index and workspace.
/-- All external writes are absent. Three bounds on the actual read traces
suffice for any member of the scheduled shrinking action list. -/
theorem actionFootprint (allow : ℕ → Prop)
    (routes : ∀ j, Reads allow (routeEvents X sel side v m level term R j))
    (gathers : ∀ j, Reads allow ((jobs (row j)).trace ((G).operands (key j)) ((G).node (key j))
      (pub (row j)) (state j) m))
    (matrices : ∀ j, Reads allow ((F).successEvents demandMass_pos (input j) hw
      (pub (row j)) (state j) m))
    (act : Action w endAddr)
    (member : act ∈ actions B ord i X sel v hidden jobs m level term R hw pub workspace)
    (node : Word w) (saved : Scratch w endAddr) (es : List (Event w)) (updated : Scratch w endAddr)
    (got : act node saved = some (es, updated)) : Reads allow es ∧ Writes (fun _ ↦ False) es := by
  unfold actions at member
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp member
  let q := rowEquiv X side v j
  let I := jobInput B i X sel v hidden jobs q
  have eqn := rowAction_trace (g := g) (w := w) (endAddr := endAddr) (ready := S.shrink i)
    (jobMotif := q.1.1) (F) (G) X sel v m level term R j I (jobs q) hw (pub q)
    (workspace q) saved got
  rw [eqn]
  refine ⟨TerminalFootprint.reads_append (routes j)
    (TerminalFootprint.reads_append (gathers j) (matrices j)), ?_⟩
  intro a b hit
  obtain h | h := List.mem_append.mp hit
  · exact routeEvents_noWrites X sel side v m level term R j a b h
  obtain h | h := List.mem_append.mp h
  · exact (jobs q).trace_noWrites ((G).operands (key j)) ((G).node (key j))
      (pub q) (state j) m a b h
  · exact (F).successEvents_noWrites demandMass_pos I hw (pub q) (state j) m a b h

end PairSimulation.ShrinkRole.MapWitness

end VPVNP
end Computability
end OAI
