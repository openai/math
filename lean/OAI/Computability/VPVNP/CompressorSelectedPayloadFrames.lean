import OAI.Computability.VPVNP.CompressorSelectedPayloadHistory
import OAI.Computability.VPVNP.CompressorShrinkScheduledTail
import OAI.Computability.VPVNP.CompressorRefreshCoreBuild
import OAI.Computability.VPVNP.CompressorRefreshCopyGroup
import OAI.Computability.VPVNP.CompressorRefreshPlacementTrace

/-!
# Frames of the native groups used by the selected payload history

The old incidence bank remains readable during scalar publication,
scratch-array scans, and the final term/data header writes. Consecutive
group frames compose in the actual intermediate memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedPayloadHistory

open BurstRAM Compression DescriptorSpace SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {L : Layout} {i : ℕ} {m n out : Memory w}

/-- The two regions shared with all previously emitted parser data. -/
structure InputFrame (L : Layout) (i : ℕ) (m out : Memory w) : Prop where
  earlier : ∀ x, levelsBase L ≤ x → x < levelStart L i → out x = m x
  graph : Agree (GraphCells L i) m out

theorem InputFrame.trans (h : InputFrame L i m n) (h' : InputFrame L i n out) :
    InputFrame L i m out :=
  ⟨fun x lo hi => (h'.earlier x lo hi).trans (h.earlier x lo hi),
    fun x hx => (h.graph x hx).trans (h'.graph x hx)⟩

/-- Readback below the scratch allocation, as supplied by the shrink slot
group and its successor copies, suffices for both history regions. -/
theorem InputFrame.below_array (same : ∀ x, levelsBase L ≤ x → x < arrayBase L i → out x = m x) :
    InputFrame L i m out := by
  have low : levelsBase L ≤ levelStart L i := Nat.le_add_right ..
  have high : levelStart L i ≤ arrayBase L i := by unfold arrayBase incidenceStart; omega
  exact ⟨fun x lo hi => same x lo (hi.trans_le high),
    fun x hx => (same x (low.trans ((Nat.le_add_right ..).trans hx.1)) hx.2).symm⟩

/-- Workers can also publish scalar fields of their own input level.
The pointer words and old incidence still agree in the two images. -/
theorem InputFrame.of_writes {es : List (Event w)}
    (writes : Writes (fun x => x < levelsBase L ∨
      (levelStart L i ≤ x ∧ x < levelStart L i+L.shape.scalarFields) ∨ arrayBase L i ≤ x) es) :
    InputFrame L i m (after m es) := by
  have low : levelsBase L ≤ levelStart L i := Nat.le_add_right ..
  have head : levelStart L i ≤ arrayBase L i := by unfold arrayBase incidenceStart; omega
  refine ⟨fun x lo hi => after_outside m writes (by omega),?_⟩
  intro x hx
  obtain ⟨a,b⟩ := hx
  exact (after_outside m writes (by omega)).symm

/-- A scratch worker can write any word starting at the input's array base.
Its scheduler may also update the low control area. -/
theorem InputFrame.of_array {es : List (Event w)}
    (writes : Writes (fun x => x < levelsBase L ∨ arrayBase L i ≤ x) es) : InputFrame L i m (after m es) :=
  of_writes fun a v hv => (writes a v hv).elim Or.inl (fun h => Or.inr (Or.inr h))

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
variable {f : B.Entry → R} {hf : B.IsSolution f} {v : SelectedLevel B f hf}

open private array_before from OAI.Computability.VPVNP.CompressorSelectedPayloadHistory

theorem InputFrame.substep {i j : Fin L.levels} {six : 6 ≤ L.shape.scalarFields}
    (p : BlockHeaderRun.Substep v L i j six m) (next : i.val+1 = j.val) :
    InputFrame L i.val m (BlockHeaderRun.finalMemory v L i j m) := by
  refine ⟨fun x _ hi => p.before v next x hi,?_⟩
  have bound := array_before L i
  rw [next] at bound
  intro x hx
  obtain ⟨lo,hi⟩ := hx
  exact (p.outside x (.inr (by omega)) (.inl (by omega)) (.inl (by omega))).symm

variable {base : Word w} {positions blocks t step : ℕ}
local notation "plan" => BlockProgram.script B
local notation "layout" => BlockProgram.layout B base.val positions blocks
local notation "first" => BlockPlanner.Script.levelsPerBlock plan*t

/-- The old metadata packet and the two successor scalar writes preserve
the input pointer bank and canonical incidence, as well as earlier levels. -/
theorem InputFrame.metadata {role : BlockMetadata.Role} {fields : BlockMetadata.Fields} {oldSites : ℕ}
    {rs : List (Report w)} (p : BlockMetadata.Published B base positions blocks t step role fields m oldSites rs) :
    InputFrame layout (first+step) m (after m (eventLog rs)) := by
  have bound := array_before layout (first+step)
  rw [Nat.add_assoc] at bound
  have old : levelStart layout (first+step) ≤ levelStart layout (first+(step+1)) := levelStart_mono layout (by omega)
  refine ⟨fun x _ hi => p.outside x (.inl (by omega)) (by omega) (by omega),?_⟩
  intro x hx
  obtain ⟨lo,hi⟩ := hx
  change levelStart layout (first+step)+54 ≤ x at lo
  exact (p.outside x (.inr (by omega)) (by omega) (by omega)).symm

theorem InputFrame.shrinkTail {j : Fin S.steps} {g cap : ℕ}
    {X : State (ShrinkBlockInputs.a j) (packingLaneBits (ShrinkBlockInputs.a j) g)} {ms ps}
    (r : ShrinkScheduledTail.Result B base positions blocks t cap j X m ms ps) :
    InputFrame layout (first+j.val) m (SourceOnline.post m ps) := by
  have bound := array_before layout (first+j.val)
  rw [Nat.add_assoc] at bound
  exact ⟨fun x _ hx => r.earlier x hx,fun x hx => (r.old_data x hx.1 (hx.2.trans_le bound)).symm⟩

theorem InputFrame.refreshCore {g cap : ℕ} {X : State S.portExponent (S.portExponent+g)} {c rs}
    (r : RefreshCore.Built B base positions blocks t X c cap m rs) :
    InputFrame layout (first+S.steps) m (after m (eventLog rs)) :=
  of_array fun a v hv => Or.inr (r.writes a v hv).1

/-- The six copies install the output graph after the current level, so the
input pointer bank and all previous levels retain their actual words. -/
theorem InputFrame.refreshCopies {a g : ℕ} {Y : State a g} {p : PortRefresh.Allocation.Plan}
    {rs : List (Report w)} (r : RefreshCopyPackets.CopyResult Y p L (i+1) m rs) :
    InputFrame L i m (after m (eventLog rs)) := by
  apply of_array
  intro addr val hw
  exact Or.inr ((array_before L i).trans ((Nat.le_add_right ..).trans (r.write addr val hw).1))

/-- The refresh's singleton placement scan writes only its packed table. -/
theorem InputFrame.refreshPlacement {start sites : ℕ} (table : arrayBase L i ≤ start)
    (room : start+3*sites < 2^w) :
    InputFrame L i m (after m (eventLog (RefreshPlacement.log (RefreshPlacement.packed w start sites) 0 sites))) :=
  of_array fun a v hv => Or.inr (table.trans ((RefreshPlacement.packed_log_access room
    (Nat.zero_add sites).le).2 a v hv).1)

end CompressorRecords.SelectedPayloadHistory

end VPVNP
end Computability
end OAI
