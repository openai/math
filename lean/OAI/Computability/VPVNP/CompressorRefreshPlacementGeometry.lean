import OAI.Computability.VPVNP.CompressorBlockMetadataRefreshReadback
import OAI.Computability.VPVNP.CompressorRefreshPlacementPacket

/-!
# Traversal geometry after the final refresh publications

The placement scan fills table four before the metadata workers publish the
argument arena and stride. The final term and successor pointer publications
write offsets 36 through 40, disjoint from every traversal geometry field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshPlacement

open BurstRAM BlockPlanner Compression DescriptorSpace Schedule PortRefresh.TraversalHeaders
open scoped Fin.CommRing

/-- Geometry after the term and successor-head packets, using their exact
five-word footprint in the old header. -/
theorem keep_geometry_heads {w V g oldHead newHead start : ℕ}
    {A : PairSimulation.NodeArguments.Arena} {T U : IncidenceDirectory w} {m out : Memory w}
    (geom : Geometry V g oldHead newHead start A T U m)
    (gap : oldHead+66 ≤ newHead)
    (keep : ∀ x, x < oldHead+36 ∨ oldHead+41 ≤ x → out x = m x) :
    Geometry V g oldHead newHead start A T U out := by
  refine ⟨geom.oldRoom, geom.newRoom, (keep _ (.inl (by omega))).trans geom.vertices,
    (keep _ (.inl (by omega))).trans geom.residual, (keep _ (.inl (by omega))).trans geom.arena,
    (keep _ (.inl (by omega))).trans geom.stride,
    fun c => (keep _ (.inr (by omega))).trans (geom.oldIncidence c),
    fun c => (keep _ (.inr (by omega))).trans (geom.newIncidence c),
    (keep _ (.inr (by omega))).trans geom.scratch⟩

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (base : Word w) (positions blocks t : ℕ)
variable (f : B.Entry → R) (hf : B.IsSolution f) (X : State S.portExponent (S.portExponent+g))
variable (c : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh) (sel : List Bool)

local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => (first) + S.steps
local notation "head" => levelStart L (cur)
local notation "start" => tableBase L (cur) (4 : Fin 6)
local notation "level" => selectedLevel B f hf X c sel

open private space from OAI.Computability.VPVNP.CompressorRefreshPlacementPacket

/-- Read back the actual metadata burst after its singleton placement scan.
The scan preserves the startup length word and the successor header bank. -/
theorem metadata_geometry {m mid : Memory w} {rs : List (Report w)} {n newRows dH : ℕ}
    (published : BlockMetadata.Published B base positions blocks t S.steps .refresh
      (BlockMetadata.refreshFields B) mid X.positions rs)
    (live : t < blocks) (size : X.positions ≤ positions) (fit : endAddress L < 2^w)
    (rows : mid (pt).rows.val = (directoryRows L : Word w))
    (pitch : mid ((pt).directory-1).val = (levelWords L : Word w))
    (old : LevelFields.Published L (cur) level dH mid)
    (oldBank : HeadBank L (cur) (level).oldSlots mid)
    (frame : ∀ x, x < start ∨ start+3*X.positions ≤ x → mid x = m x)
    (length : m (levelStart L 0+29) = (n : Word w))
    (new : HeadBank L (cur+1) newRows m) :
    Geometry (Fintype.card X.Base) g head (levelStart L (cur+1)) (arrayBase L (cur))
      ⟨n, PairSimulation.NodeArguments.frameStride (slotDegree S) n⟩
      (packedIncidence L w (cur) (level).oldSlots) (packedIncidence L w (cur+1) newRows)
      (after mid (eventLog rs)) := by
  have upto := (space B base positions blocks t size live fit).1
  have lower := levelStart_mono L (Nat.zero_le (cur))
  have headerLen : levelHeaderWords L = 66 := rfl
  have before : head + 66 ≤ start := by unfold tableBase arrayBase incidenceStart; omega
  have saved := (frame _ (.inl (by omega : levelStart L 0+29 < start))).trans length
  have bank := new.keep (m' := mid) (fun i _ => frame _ (.inr (upto.trans (Nat.le_add_right ..))))
  let entry : LevelFields.Entry L (first) (pt).data (levelStart L (first) : Word w) mid := ⟨rfl,pitch⟩
  have native := BlockMetadata.Published.refresh_geometry B level base positions blocks t published
    live fit rows pitch (LevelFields.eval_dimensions entry old).1 saved old oldBank
    (by simpa only [← Nat.add_assoc] using bank)
  simpa only [← Nat.add_assoc] using native

end CompressorRecords.RefreshPlacement

end VPVNP
end Computability
end OAI
