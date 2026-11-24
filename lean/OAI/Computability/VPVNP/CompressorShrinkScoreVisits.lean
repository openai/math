import OAI.Computability.VPVNP.CompressorShrinkScoreBounds
import OAI.Computability.VPVNP.CompressorBlockHeaderPacket
import OAI.Computability.VPVNP.CompressorHeaderOperands

/-! # Typed planner launches for the score workers -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ScorePackets

open scoped Fin.CommRing

open BurstRAM TermScores SourceTransport SourceOnline DescriptorSpace PhaseRecipe

variable {w : ℕ} (I : SelectedPlan.Inputs) (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w)

/-- Per-call instruction budget for a score worker, seven for clearing, twenty-seven for an
axis, and ten for comparison. -/
def Stage.fuel : Stage → ℕ | .clear => 7 | .axis _ => 27 | .compare => 10

theorem Stage.fuel_le (j : Stage) : j.fuel ≤ 27 := by cases j <;> simp [Stage.fuel]

theorem supported (D : ℕ → Prop) (j : Stage) (term : I.termBase.ReadsFrom D pub st mem)
    (motifs : I.motifs.ReadsFrom D pub st mem) :
    HeaderOperands.Supported D pub st mem (j.visit I) := by
  have score : (SelectedPlan.scoreBase I).ReadsFrom D pub st mem := ⟨term,motifs,trivial⟩
  cases j with
  | clear => exact ⟨trivial,trivial,fun _ => score⟩
  | axis j =>
    refine ⟨trivial,motifs,?_⟩
    intro u; change (SelectedPlan.axisBank I j u).ReadsFrom D pub st mem
    fin_cases u <;> first | exact term | exact score | trivial
  | compare =>
    refine ⟨trivial,trivial,?_⟩
    intro u; fin_cases u
    exacts [score,⟨score,trivial⟩]

variable (T : Tables w) (n : ℕ)

/-- Relates the planner operands to the native score table by matching the term base, motif
count, term stride, selector width, score base, and layout cell. -/
structure Readback : Prop where
  term : I.termBase.eval pub st mem = T.termBase
  rows : I.motifs.eval pub st mem = word n
  stride : (I.termStride : Word w) = T.termStride
  selectors : (I.selectorBits : Word w) = T.selectorBits
  score : (SelectedPlan.scoreBase I).eval pub st mem = T.scoreBase
  cell : (SelectedPlan.layoutCell I).eval pub st mem = T.levelCell

theorem Native.run (D : Layout) (low : levelStart D 0 ≤ T.termBase.val) (region : Region T n)
    (values : Readback I pub st mem T n) (j : Stage) (rs : List (Report w)) (h : Native T n j mem rs) :
    HeaderPacket.Run D pub st (j.visit I) mem rs j.fuel (List.replicate (j.limit n) []) := by
  have bounds := h.bounds T n region j mem rs
  have pos : 0 < j.fuel := by cases j <;> simp [Stage.fuel]
  have initial : (j.visit I).initial.eval pub st mem = 0 := by cases j <;> rfl
  have stop : (j.visit I).stop.eval pub st mem = word (j.limit n) := by
    cases j <;> first | rfl | exact values.rows
  refine ⟨pos,?_,(initial ▸ stop ▸ bounds.1),fun a v ha => low.trans (bounds.2.1 a v ha),
    fun a v ha => low.trans (bounds.2.2 a v ha)⟩
  cases j with
  | clear =>
    subst rs
    change runSegment (((SelectedPlan.clear I).worker.table.instantiate w
      (fun _ => (SelectedPlan.scoreBase I).eval pub st mem)).program) 7 (some 0) mem [[]] = _
    rw [values.score,runSegment,SelectedPlan.clear_native]; rfl
  | compare =>
    subst rs
    have bank : (fun u : Fin 2 => (![SelectedPlan.scoreBase I,SelectedPlan.layoutCell I] u).eval pub st mem) = ![T.scoreBase,T.levelCell] := by
      funext u; fin_cases u
      exacts [values.score,values.cell]
    change runSegment ((SelectedPlan.compareTable.instantiate w (fun u : Fin 2 => (![SelectedPlan.scoreBase I,SelectedPlan.layoutCell I] u).eval pub st mem)).program) 10 (some 0) mem [[]] = _
    rw [bank,runSegment,SelectedPlan.compare_native]; rfl
  | axis j =>
    have bank : (fun u => (SelectedPlan.axisBank I j u).eval pub st mem) = params T (SelectedScore.axes j) := by
      funext u; fin_cases u <;> first | exact values.term | exact values.stride | exact values.score | exact values.selectors | rfl
    change runSegment (((PrimedStackRAM.template TermScores.worker 0).instantiate w
      (fun u => (SelectedPlan.axisBank I j u).eval pub st mem)).program) 27 (some 0) mem (List.replicate n []) = _
    rw [bank]; exact h

end CompressorRecords.ScorePackets

end

end VPVNP
end Computability
end OAI
