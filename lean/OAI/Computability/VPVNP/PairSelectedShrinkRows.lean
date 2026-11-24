import OAI.Computability.VPVNP.PairSelectedNativeRoles
import OAI.Computability.VPVNP.PairVertexRatedRoles

/-! # Native shrinking-role contracts at a selected physical vertex -/

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

/-- The same physical site readers give the accepted native shrinking tapes and
the monomial of every shrinking occurrence in the chronological history. -/
def ShrinkRows : Prop :=
  ∃ readers : ShrinkRoleDirectory.ShrinkSite (passes) → HookParser G.w n,
    let first : TaggedLayer := ⟨leafLayer (siteOrder X), .cursor⟩
    let shrink := ShrinkRoleDirectory.parser B.recordLimit (base) first (passes) readers
    ∀ vals : LeafSourceLoad.Static 34 → Word G.w,
    let dom := RoleDomains.Domain X B.recordLimit (base) (passes) (area) (data) (offset)
      vals (hist) (n ^ 9000) (n * n ^ 9000)
    let valid := Budgeted (W := G.w) (endAddr := n) (area).arguments
      (SelectedPacketFormat B f hf T hT X z (base)) (VertexFrameData (area) (data) (offset) vals)
      (selectedDesc B f hf T hT X z (base)) (hist) (n ^ 9000) (n * n ^ 9000)
    shrink.ExactOn (dom .shrink) (M) ((V).entry .shrink) ((V).dfsPC 3) (V).dfs m ∧
      ∀ leaf refresh : HookParser G.w n, ∀ i : Fin (passes).length,
        tagLevel B f hf (passes)[i] = .shrink →
          LevelChecks B f hf (dispatcher (RoleDomains.handlers leaf shrink refresh) m (offset))
            valid (hist) (JobGuard (V) (M) m (TerminalLink.workerCell hdr)
              (ordinalJobCost n 1 (rate))) B.recordLimit
            (layerBase B.recordLimit (base) (tags) i.val) (passes)[i]

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
