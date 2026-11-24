import OAI.Computability.VPVNP.CompressorDeterministicGroup
import OAI.Computability.VPVNP.CompressorScheduledTraceData

/-! # Transferring selected source records through a deterministic group

The output agrees with the source's actual post-memory throughout the
data arena. The directory guard, ordinal, stride and protected bank are
read from the same native endpoint, so the following pass can start in
that memory with the chosen mathematical history.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM BlockPlanner DescriptorSpace Schedule SourceTransport Compression
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
  {w small cap ordinal total : ℕ} {L : Layout} {pub : Fin 11 → Word w} {raw m : Memory w}
  {resident : Resident B f hf w} {a g : ℕ} {X : State a g} {past : List (SelectedLevel B f hf)}
local notation "A" => BlockProgram.script B
set_option quotPrecheck false in
local notation "pt" => Workspace.ports (arity (BlockProgram.script B).catalog) (pub 2)
set_option quotPrecheck false in
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex (BlockProgram.script B).size (BlockProgram.script B).size)

/-- A completed source-group derivation supplies all scheduler fields of a
pass boundary and the true cost of the small-clock reports. Only the
application's data-region preservation law is required for its resident
mathematical state. -/
theorem boundary_of_group {ps : List (SourceOnline.Packet (A) w)}
    (group : SourceOnline.Group (A) L (pub 2) small ordinal total raw ps)
    (quiet : ∀ p ∈ ps, p.stage.choices = List.replicate p.stage.choices.length [])
    (clock : small ≤ cap) (bounds : Online.Run.ControlBounds (A).plan small (w := w))
    (arityEq : arity (A).catalog = L.shape.arity) (baseEq : (pub 2).val = L.base)
    (fit : levelStart L 0 < 2^w) (count : ordinal+ps.length ≤ total) (room : total ≤ directoryRows L)
    (agree : Agree (levelStart L 0 ≤ ·) raw m)
    (bank : Workspace.Installed (arity (A).catalog) (pub 2) m) (htag : m (pt).tag.val = tag)
    (ord : (m (pt).ordinal.val).val = ordinal) (rows : (m (pt).rows.val).val = total)
    (stride : m ((pt).directory-1).val = (levelWords L : Word w))
    (stored : resident past X (SourceOnline.post raw ps))
    (transfer : ∀ u v, Agree (levelStart L 0 ≤ ·) u v → resident past X u → resident past X v) :
    ∃ out : QuietInterval (A) pub cap small (some 0) m,
      Boundary resident pub (levelWords L : Word w) total (ordinal+ps.length) past X out.segment.memory ∧
      Agree (levelStart L 0 ≤ ·) (SourceOnline.post raw ps) out.segment.memory ∧
      RAMBuckets.cost Report.probes out.source.logs ≤ groupCost (A) ps := by
  obtain ⟨out,agreement,bank',tag',ordinal',total',stride',cost⟩ :=
    deterministicGroup group quiet clock bounds arityEq baseEq fit count room agree bank htag ord rows stride
  exact ⟨out,⟨bank',tag',ordinal',total',stride',transfer _ _ agreement stored⟩,agreement,cost⟩

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
