import OAI.Computability.VPVNP.CompressorRefreshPlacementPacket
import OAI.Computability.VPVNP.CompressorSelectedDirectoryEmission
import OAI.Computability.VPVNP.CompressorSelectedChildDirectory

/-!
# Readback of the refresh placement and publication packets

The placement and metadata reports publish the selected directory, child
operands and traversal geometry. The final two windows add the term and
successor pointers while retaining the published words.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshPlacement

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule PhaseRecipe SourceOnline
open SelectedDirectoryHistory PairSimulation.TraversalRows SourceTransport
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (base : Word w) (positions blocks t cap : ℕ)
variable (f : B.Entry → R) (hf : B.IsSolution f) (X : State S.portExponent (S.portExponent + g))
variable (c : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => (first) + S.steps
local notation "head" => levelStart L (cur)
local notation "nextHead" => levelStart L (cur + 1)
local notation "start" => tableBase L (cur) (4 : Fin 6)
local notation "level" => selectedLevel B f hf X c sel
local notation "data" => packed w start X.positions
local notation "W₃" => BlockGroups.refresh B 3
local notation "W₄" => BlockGroups.refresh B 4
local notation "W₅" => BlockGroups.refresh B 5
local notation "W₆" => BlockGroups.refresh B 6
local notation "off" => List.length (Script.initial scr) + t * List.length (Script.block scr)

/-- Exact frame of the singleton scan and its three metadata publications. -/
def OutsideMetadata (n x : ℕ) : Prop :=
  (x < start ∨ start + 3 * n ≤ x) ∧ (x < head + 15 ∨ head + 27 ≤ x) ∧
    x ≠ nextHead + 14 ∧ x ≠ nextHead + 27

set_option maxHeartbeats 1200000 in
/-- The two consecutive windows have filled a directory and published its
header. The physical directory ends before the successor header. -/
structure MetadataResult (m : Memory w) (ps : List (Packet scr w)) : Prop where
  group : SourceOnline.Group scr L base cap (off + (W₃).before.length) (directoryRows L) m ps
  phases : ps.map (fun p => p.stage.phase) = (W₃).indices ++ (W₄).indices
  charge : RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) =
    4 * X.positions + 17
  emits : ∃ e : Emission L (cur) level m (post m ps), e.dir.pub = data
  recordWords : post m ps (head + 15) = ((B.recordLimit + 2 : ℕ) : Word w)
  geometry : ∀ (n newRows : ℕ), m (levelStart L 0 + 29) = (n : Word w) →
    PortRefresh.TraversalHeaders.HeadBank L (cur + 1) newRows m →
    PortRefresh.TraversalHeaders.Geometry (Fintype.card X.Base) g head nextHead (arrayBase L (cur))
      ⟨n, PairSimulation.NodeArguments.frameStride (slotDegree S) n⟩
      (packedIncidence L w (cur) (level).oldSlots) (packedIncidence L w (cur + 1) newRows)
      (post m ps)
  child : ∀ n : ℕ, m (levelStart L 0+29) = (n : Word w) →
    SelectedChildDirectory.Stored B L (cur) n X (post m ps)
  tapes : ps.flatMap (fun p => p.stage.choices) = List.replicate (X.positions+3) []
  frame : ∀ x, OutsideMetadata B base positions blocks t X.positions x → post m ps x = m x

local notation "shape" => RefreshBlockPlan.shape B
local notation "arena" => arrayBase L (cur)
local notation "tmp" => PortRefresh.Allocation.plan X (S.degreeExponent 0)
  (PortRefresh.LevelRecipe.Shape.dH shape) (PortRefresh.LevelRecipe.Shape.ties shape)
  (PortRefresh.LevelRecipe.Shape.stride shape) arena

set_option maxHeartbeats 1200000 in
/-- Readback and source-group accounting for all four trailing windows. -/
structure TailResult (m : Memory w) (ps : List (Packet scr w)) : Prop where
  group : SourceOnline.Group scr L base cap (off + (W₃).before.length) (directoryRows L) m ps
  phases : ps.map (fun p => p.stage.phase) =
    ((W₃).indices ++ (W₄).indices) ++ ((W₅).indices ++ (W₆).indices)
  charge : RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) =
    4 * X.positions + 27
  emits : ∃ e : Emission L (cur) level m (post m ps), e.dir.pub = data
  termHead : post m ps (head + 36) = ((tmp).term : Word w)
  termStride : post m ps (head + 37) = ((shape).stride : Word w)
  side : post m ps (head + 38) = 0
  absolute : post m ps (head + 39) = 0
  successorHead : post m ps (head + 40) = (nextHead : Word w)
  recordWords : post m ps (head + 15) = ((B.recordLimit + 2 : ℕ) : Word w)
  geometry : ∀ (n newRows : ℕ), m (levelStart L 0 + 29) = (n : Word w) →
    PortRefresh.TraversalHeaders.HeadBank L (cur + 1) newRows m →
    PortRefresh.TraversalHeaders.Geometry (Fintype.card X.Base) g head nextHead (arrayBase L (cur))
      ⟨n, PairSimulation.NodeArguments.frameStride (slotDegree S) n⟩
      (packedIncidence L w (cur) (level).oldSlots) (packedIncidence L w (cur + 1) newRows)
      (post m ps)
  child : ∀ n : ℕ, m (levelStart L 0+29) = (n : Word w) →
    SelectedChildDirectory.Stored B L (cur) n X (post m ps)
  tapes : ps.flatMap (fun p => p.stage.choices) = List.replicate (X.positions+8) []
  frame : ∀ x, OutsideMetadata B base positions blocks t X.positions x →
    (x < head + 36 ∨ head + 41 ≤ x) → post m ps x = m x

end CompressorRecords.RefreshPlacement

end

end VPVNP
end Computability
end OAI
