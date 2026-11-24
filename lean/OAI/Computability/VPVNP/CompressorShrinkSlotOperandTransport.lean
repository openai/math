import OAI.Computability.VPVNP.CompressorShrinkSlotFixedOperands
import OAI.Computability.VPVNP.CompressorWindowPrepared

/-!
# Replaying shrinking slot operands after earlier workers

When memory agrees on the original roots, every load computes the same
address. The structural footprint therefore holds in the next memory and
may be widened to the scheduler's persistent operand region.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM PhaseRecipe SourceTransport

variable {w : ℕ} {small data : ℕ → Prop} {pub : Fin 5 → Word w} {state : Word w} {m m' : Memory w}

/-- A footprint is preserved when its input cells retain their contents,
including for a load whose address is computed by a nested load. -/
theorem PhaseRecipe.Expr.reads_transport (e : Expr) (reads : e.ReadsFrom small pub state m)
    (same : Agree small m m') (widen : ∀ x, small x → data x) : e.ReadsFrom data pub state m' := by
  induction e with
  | lit | state | publicWord => trivial
  | binary op a b ha hb => exact ⟨ha reads.1,hb reads.2⟩
  | load a ha =>
    refine ⟨ha reads.1,?_⟩
    rw [← a.eval_eq_of_reads reads.1 same]
    exact widen _ reads.2

/-- The pitch belongs to the online operand region. Both header intervals
lie in the data suffix, as does the chosen score cell when its address is
at or above the first header. -/
theorem ShrinkSlotCalendar.rootCell_operandRegion (A : BlockPlanner.Script) (L : DescriptorSpace.Layout)
    (base : Word w) (old next score : ℕ) (scoreLow : DescriptorSpace.levelStart L 0 ≤ score) :
    ∀ x, ShrinkSlotCalendar.RootCell ((Workspace.ports (Schedule.arity A.catalog) base).directory-1).val
      (DescriptorSpace.levelStart L old) (DescriptorSpace.levelStart L next) score x →
      BlockPlanner.Window.operandRegion A L base x := by
  intro x hx
  rcases hx with pitch | ⟨lo,_⟩ | ⟨lo,_⟩ | rfl
  · exact Or.inr (Or.inl pitch)
  · exact Or.inr (Or.inr ((DescriptorSpace.levelStart_mono L (Nat.zero_le old)).trans lo))
  · exact Or.inr (Or.inr ((DescriptorSpace.levelStart_mono L (Nat.zero_le next)).trans lo))
  · exact Or.inr (Or.inr scoreLow)

namespace ShrinkSlotPlan.Scheduled

theorem Roots.transport {P : Plan} (roots : Roots P small pub state m)
    (same : Agree small m m') (widen : ∀ x, small x → data x) : Roots P data pub state m' := by
  have keep (e : Expr) (read : e.ReadsFrom small pub state m) : e.ReadsFrom data pub state m' :=
    e.reads_transport read same widen
  exact ⟨keep _ roots.bases,keep _ roots.lanes,keep _ roots.oldArc,keep _ roots.role,
    keep _ roots.subdivisions,keep _ roots.nextSite,keep _ roots.scratch,keep _ roots.chosen,
    keep _ roots.split,fun c ↦ keep _ (roots.columns c)⟩

/-- The evaluated worker bounds and bank agree between the original and
current packet inputs on the same stage, even when the entry layouts differ elsewhere. -/
theorem Stage.eval_transport (P : Plan) (stage : Stage) (roots : Roots P small pub state m)
    (same : Agree small m m') :
    let v := stage.visit P
    v.initial.eval pub state m = v.initial.eval pub state m' ∧
      v.stop.eval pub state m = v.stop.eval pub state m' ∧
      ∀ j, (v.params j).eval pub state m = (v.params j).eval pub state m' := by
  intro v
  obtain ⟨hi,hs,hp⟩ := Stage.reads P stage roots
  exact ⟨v.initial.eval_eq_of_reads hi same,v.stop.eval_eq_of_reads hs same,
    fun j ↦ (v.params j).eval_eq_of_reads (hp j) same⟩

end ShrinkSlotPlan.Scheduled
end CompressorRecords

end VPVNP
end Computability
end OAI
