import OAI.Computability.VPVNP.CompressorBlockMetadataWindows
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-! # Refresh DFS geometry on the installed metadata packet's actual memory -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockMetadata

open BurstRAM BlockPlanner DescriptorSpace Schedule Compression PortRefresh.TraversalHeaders
open scoped Fin.CommRing

variable {w : ℕ}

private theorem unique_source {pub : Fin 5 → Word w} {s : Word w} {v : BlockPlanner.Visit} {m : Memory w}
    {rs ss : List (Report w)} (a : Source pub s v m rs) (b : Source pub s v m ss) : rs=ss := by
  obtain ⟨f,r,rfl,_,_,_,run⟩ := a
  obtain ⟨g,q,rfl,_,_,_,run'⟩ := b
  unfold BlockHeaderRun.rawCall at run run'
  have rf := BurstRAM.execute_extend run g
  have rg := BurstRAM.execute_extend run' f
  rw [Nat.add_comm g f] at rg
  rw [rf] at rg
  rw [Option.some.inj rg]

private theorem unique_walk {pub : Fin 5 → Word w} {s : Word w} {vs : List BlockPlanner.Visit} {m : Memory w}
    {rs ss : List (Report w)} (walk : SourceWalk (Source pub s) vs m rs)
    (other : SourceWalk (Source pub s) vs m ss) : rs = ss := by
  induction walk generalizing ss with
  | done => cases other; rfl
  | next h _ ih =>
    cases other with
    | next h' tail =>
      obtain rfl := unique_source h h'
      exact congrArg (_ ++ ·) (ih tail)

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable {f : B.Entry → R} {hf : B.IsSolution f} (v : SelectedLevel B f hf)
variable (base : Word w) (positions blocks t : ℕ)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "pub" => Ports.data pt
local notation "first" => Script.levelsPerBlock scr*t
local notation "st" => (levelStart L first : Word w)
local notation "prev" => first+S.steps
local notation "lastHead" => first+(S.steps+1)

/-- The private refresh evaluator recovers its input/output incidence and
argument-stack pointers after these very three native reports. -/
theorem Published.refresh_geometry {oldSites n oldRows newRows dH : ℕ} {m : Memory w} {rs : List (Report w)}
    (P : Published B base positions blocks t S.steps .refresh (refreshFields B) m oldSites rs)
    (ht : t<blocks) (fit : endAddress L < 2^w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory-1).val = (levelWords L : Word w))
    (sites : (LevelFields.sites S.steps).eval pub st m = (oldSites : Word w))
    (nCell : m (levelStart L 0+29) = (n : Word w))
    (oldScalars : LevelFields.Published L prev v dH m)
    (old : PortRefresh.TraversalHeaders.HeadBank L prev oldRows m)
    (new : PortRefresh.TraversalHeaders.HeadBank L lastHead newRows m) :
    PortRefresh.TraversalHeaders.Geometry (Fintype.card v.input.Base) v.outputLanes
      (levelStart L prev) (levelStart L lastHead) (arrayBase L prev)
      ⟨n,PairSimulation.NodeArguments.frameStride (slotDegree S) n⟩
      (packedIncidence L w prev oldRows) (packedIncidence L w lastHead newRows) (after m (eventLog rs)) := by
  have hl : lastHead < (L).levels := by
    have mul := Nat.mul_le_mul_left (S.steps+1) ht
    change (S.steps+1)*t+(S.steps+1) < 1+(S.steps+1)*blocks
    rw [Nat.mul_succ] at mul; omega
  let entry : LevelFields.Entry L first pub st m := ⟨rfl,pitch⟩
  have head := BlockHeaderPlan.firstHeader_eval L base m st (Fin.cast_val_eq_self _).symm rows
  have lo := Window.lowCells (A := scr) L base rfl rfl ((levelStart_mono L (Nat.zero_le _)).trans_lt fit)
  obtain ⟨ss,walk,geom⟩ := PortRefresh.TraversalHeaders.run_metadata (v := v) m entry B.recordLimit (slotDegree S)
    (refreshFields B) sites head nCell oldScalars old new rfl (by change 0<6; decide) hl fit
    (lo.2.trans_le (levelStart_mono L (Nat.zero_le _)))
  exact (unique_walk P.source walk).symm ▸ geom

end CompressorRecords.BlockMetadata

end

end VPVNP
end Computability
end OAI
