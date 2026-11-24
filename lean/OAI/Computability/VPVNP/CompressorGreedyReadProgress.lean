import OAI.Computability.VPVNP.CompressorGreedyWalkValid
import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy
import OAI.Computability.VPVNP.CompressorSourceOnline

/-!
# Cursor progress of the native greedy readers

The immutable header of each color or offset record supplies the address of
the next record. The last header returns the exclusive bound. These are the
cursor comparisons used to replay the native reports in the online schedule.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena

open BurstRAM Compression Greedy SourceOnline

namespace Assignment

open private read_induction from OAI.Computability.VPVNP.CompressorGreedyWalkValid

variable {w N width d arity n : ℕ} {V A : Type*}
variable {L : WalkLayout w N width} {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N}
    {rows : OperandRows d} {m : Memory w} {encode : A → Word w} {label : V → A}

/-- The actual reader advances by one directory record per report, even if
there are no scheduler control cells in its input memory. -/
theorem read_progress (r : Assignment L T G order rows arity n m encode label)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width)
    (space : L.limit < 2 ^ w) (fit : n < 2 ^ w) :
    Progress (L.base N) (L.base 0) r.reads := by
  have native := r.readRun
  rw [r.prepMemory] at native
  exact read_induction L _ m arity n size space fit (fun st _ rs ↦ Progress (L.base N) st rs)
    (fun _ _ ↦ .done le_rfl) (fun _ _ _ _ _ active ret tail ↦ .next active ret tail) _ native

end Assignment

namespace Run

variable {w a g origin : ℕ} {X : ShrinkingState a g} {T : IncidenceDirectory w}
    {m : Memory w} (r : Run X T origin m)

local notation "N" => Fintype.card X.Base

/-- Cursor guards for the native color reader in the shrinking run. -/
theorem color_read_progress :
    let L := colorLayout w origin N a r.room
    Progress (L.base N) (L.base 0) r.color.reads := by
  have hb := bounds origin N a
  have room := r.room
  exact r.color.read_progress (fun _ ↦ rowWords_color_length _ _ _ _)
    (by rw [color_limit]; omega) (colorFits origin N a w Fintype.card_pos room)

/-- Cursor guards for the native offset reader in the shrinking run. -/
theorem tag_read_progress :
    let L := tagLayout w origin N a r.room
    Progress (L.base N) (L.base 0) r.offsets.reads := by
  have hb := bounds origin N a
  have room := r.room
  have fit := (packingTagBits_sufficient (2 ^ a)).trans_le (Nat.pow_le_pow_right (by decide) r.tagFit)
  exact r.offsets.read_progress (fun _ ↦ by rw [rowWords_tag_length, tagTests_length, Nat.mul_comm])
    (by rw [tag_limit]; omega) fit

end Run

end CompressorRecords.GreedyArena

end VPVNP
end Computability
end OAI
