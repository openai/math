import OAI.Computability.VPVNP.PairSelectedNativeRoles
import OAI.Computability.VPVNP.PairVertexRatedRoles

/-! # Complete local refresh contracts on one selected branch -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM LiveProgram PairStages.Group.Auxiliary
open Compression CompressorRecords DescriptorSpace DFS TreeDecode LocalHistory TraversalRows
open TraversalRoles VertexImage NodeArguments
open scoped Fin.CommRing

variable {k A : Type} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
    (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
    (G : PairStages.Group) (n p q : ℕ) {labels : ℕ} (order : B.Entry ≃ Fin labels)
    {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)
    (m : Memory G.w)

local notation "pub" => terminalOperands G
local notation "hdr" => vertexHeader G
local notation "L" => BlockProgram.layout B (Fin.val (pub 2)) X.positions T
local notation "base" => endAddress (L)
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => selected B f hf T hT X z
local notation "size" => tagWords B.recordLimit (tags)
local notation "width" => State.totalWidth (StateExecution.finalState (B.execute f hf T hT X) z)
local notation "offset" => (((size) + (width) : ℕ) : Word G.w)
local notation "area" => TerminalLayout.privateRegions (slotDegree S) n ((base) + (size)) labels
local notation "data" => NativeFrame.leafWords (slotDegree S) pub hdr (offset) m
local notation "hist" => privateHistogram (W := G.w) (endAddr := n) order.symm
  (LeafArena.Regions.histBase (area))
local notation "image" => nativeSegments B G.constants p q order
local notation "V" => placement (image)
local notation "M" => PrivateRAM.Template.instantiate (template (image)) G.w pub
local notation "rate" => RatedRoles.scan B order

/-- One reader proves both acceptance on every prepared refresh row and
the exact local monomial update of every selected refresh occurrence. -/
def RefreshRows : Prop :=
  ∃ refresh : HookParser G.w n, ∀ vals : LeafSourceLoad.Static 34 → Word G.w,
    let dom := RoleDomains.Domain X B.recordLimit (base) (passes) (area) (data) (offset)
      vals (hist) (n ^ 9000) (n * n ^ 9000)
    let valid := Budgeted (W := G.w) (endAddr := n) (area).arguments
      (SelectedPacketFormat B f hf T hT X z (base)) (VertexFrameData (area) (data) (offset) vals)
      (selectedDesc B f hf T hT X z (base)) (hist) (n ^ 9000) (n * n ^ 9000)
    refresh.ExactOn (dom .refresh) (M) ((V).entry .refresh) ((V).dfsPC 3) (V).dfs m ∧
      ∀ leaf shrink : HookParser G.w n, ∀ i : Fin (passes).length,
        tagLevel B f hf (passes)[i] = .refresh →
          LevelChecks B f hf (dispatcher (RoleDomains.handlers leaf shrink refresh) m (offset))
            valid (hist) (JobGuard (V) (M) m (TerminalLink.workerCell hdr)
              (ordinalJobCost n 1 (rate))) B.recordLimit
            (layerBase B.recordLimit (base) (tags) i.val) (passes)[i]

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
