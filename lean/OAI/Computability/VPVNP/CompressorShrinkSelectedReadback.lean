import OAI.Computability.VPVNP.CompressorShrinkSelectedTailPackets
import OAI.Computability.VPVNP.CompressorShrinkScoreOperands
import OAI.Computability.VPVNP.CompressorShrinkBundleOperandSupport

/-! # Selected placement and child-directory operands from the published shrinking header -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedTailPackets

open BurstRAM Compression BlockPlanner ShrinkBlockInputs DescriptorSpace PhaseRecipe SourceTransport
open scoped Fin.CommRing Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
local notation "I" => selectedInputs B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)
local notation "p₀" => ShrinkInput.placementBank X T start
local notation "term" => ShrinkInput.termHead (w := w) X start

open private eval_sites eval_slots from OAI.Computability.VPVNP.CompressorShrinkBundlePlan

theorem header_values (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w)
    {L : Layout} {first : ℕ} (h : ShrinkHeaderReads.Header i X T start L first mem)
    (entry : LevelFields.Entry L first pub st mem) (room : ShrinkInput.termEnd X start 10 < 2^w)
    (width : 10<2^w) (D : ℕ → Prop) (pitch : D (pub 1-1).val)
    (cells : ∀ n≤60, D (levelStart L (first+i.val)+n)) :
    SelectedPlan.Reads I X p₀ T term pub st mem ∧ Footprint I D pub st mem := by
  have rd := h.reads B entry
  obtain ⟨count,head⟩ := ScorePackets.term_values B i X T start pub st mem rd room
  obtain ⟨countR,headR⟩ := ScorePackets.term_support B i X T start pub st mem h entry D pitch cells
  have newValue : (newSites i).eval pub st mem = (ShrinkPreimages.newCount X : Word w) := by
    change (LevelFields.vertices i.val).eval pub st mem*(((2^(Shrink.J (a i)) : ℕ) : Word w)*
      (LevelFields.residualLanes i.val).eval pub st mem) = _
    rw [rd.vertices,rd.residual,← Nat.cast_mul,← Nat.cast_mul]
  refine ⟨⟨eval_sites X rd,newValue,eval_slots X rd,count,head,width,rd.incidence 3,
    congrFun (ShrinkBundlePlan.placement_bank X rd)⟩,?_⟩
  have field (n : ℕ) (hn : n≤60) : (LevelFields.scalar i.val n).ReadsFrom D pub st mem :=
    GreedyVisit.scalar_support D L first i.val n entry pitch (cells n hn) ((Nat.add_le_add_left hn _).trans_lt h.room)
  have place := ShrinkBundlePackets.expr_reads B i h entry D pitch cells .positions
  exact ⟨⟨field 0 (by decide),field 2 (by decide)⟩,⟨field 0 (by decide),trivial,field 3 (by decide)⟩,
    ⟨⟨field 0 (by decide),field 2 (by decide)⟩,field 1 (by decide)⟩,countR,headR,field 57 (by decide),place.params⟩

end CompressorRecords.SelectedTailPackets

end

end VPVNP
end Computability
end OAI
