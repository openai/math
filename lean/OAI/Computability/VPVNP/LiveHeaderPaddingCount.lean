import OAI.Computability.VPVNP.LiveHeaderFieldFormats

/-!
# The specified group count enforces both native padding guards

On evaluation paths the incoming-format check supplies the left cut's
padding. A nonzero outgoing pair count supplies the right exponents' padding,
and a nonzero outgoing tail count supplies a canonical evaluator cut. Unit
paths use the all-zero cuts on both sides.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.Fields

open ChainAssignments CutSchedule LiveHeader LiveHeaderDescriptors LiveHeaderSchedule
open ExponentTrace LiveEvaluatorEncoding
open scoped Classical

variable {s : Sizes} {t Z M w : ℕ} {E : UniversalMachine.Program}
variable {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag}

private theorem padding_of_pair (ev : tag ≠ .unit) (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta)
    (side : Side) (i : Fin (2^s.h)) (atCut : incidentCut side g = firstCut i)
    (pad : pairPadding t Z (liveCutEquiv s.h s.delta cuts).1 i) :
    ValidPadding s cuts g tag side := by
  have hi : 0 < (incidentCut side g).val := by rw [atCut]; exact Nat.succ_pos _
  have half : (incidentCut side g).val ≤ 2^s.h := by rw [atCut]; exact i.isLt
  unfold ValidPadding
  rw [interval_pair s g tag ev side .padding (by omega) hi half, he]
  unfold incidentWidth
  rw [atCut]
  exact pad

private theorem padding_of_read (ev : tag ≠ .unit) (hc : s.config = fieldWords M*w)
    (layout : LiveEvaluatorTail.Layout E.extra M w s.delta)
    (side : Side) (k : Fin (2^s.h-1)) (atCut : incidentCut side g = laterCut k)
    (read : (LiveEvaluatorTail.readCut layout k (cuts (laterCut k))).isSome = true) :
    ValidPadding s cuts g tag side := by
  have half : 2^s.h < (incidentCut side g).val := by rw [atCut]; change _ < _+(k.val+1); omega
  have hend : (incidentCut side g).val < 2^(s.h+1) := by
    rw [atCut]
    change 2^s.h+(k.val+1) < 2^(s.h+1)
    rw [pow_succ]
    have := k.isLt
    omega
  have fit : 1+s.config ≤ s.delta := hc ▸ layout.cutWidth
  unfold ValidPadding
  rw [interval_tail s g tag ev side .padding (by omega) half hend, hc]
  unfold incidentWidth
  rw [atCut]
  apply (Physical.tail_padding_zero (show 2^s.h ≤ (laterCut k).val from by dsimp [laterCut]; omega)
    (show (laterCut k).val < 2^(s.h+1) from atCut ▸ hend) layout.cutWidth _).mpr
  unfold LiveEvaluatorTail.readCut at read
  dsimp only at read
  split at read
  · rename_i checked
    exact checked.2
  · contradiction

variable {Nom : Type*} [Fintype Nom]
variable {Path : Exterior s.h s.delta → Fin (2^s.h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]

private theorem evaluation_padding (ev : tag ≠ .unit) (he : s.e = t*Z) (hc : s.config = fieldWords M*w)
    (fit : 1+t*Z ≤ s.delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (E : UniversalMachine.Program) (layout : LiveEvaluatorTail.Layout E.extra M w s.delta)
    (init : (Fin t → ℕ) → Code E.extra M) (incoming : incomingChecks t Z layout cuts g)
    (count : groupEvaluation fit inc E layout init cuts g ≠ 0) :
    ∀ side, ValidPadding s cuts g tag side := by
  intro side
  rcases coverCuts (incidentCut side g) with zero | last | ⟨i,first⟩ | ⟨k,later⟩
  · exact validPadding_endpoint side (Or.inl (zero ▸ rfl))
  · exact validPadding_endpoint side (Or.inr (last ▸ rfl))
  · apply padding_of_pair ev he fit side i first
    cases side with
    | left => exact incoming.1 i first
    | right =>
      have same : g = halves s.h (.inl i) := by
        apply Fin.ext
        change g.val = i.val
        have h := congrArg Fin.val first
        change g.val+1 = i.val+1 at h
        omega
      rw [same] at count
      simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inl] at count
      exact pairCount_padding fit inc _ i count
  · apply padding_of_read ev hc layout side k later
    cases side with
    | left => exact incoming.2 k later
    | right =>
      let j : Fin (2^s.h) := ⟨k.val,by have := k.isLt; omega⟩
      have same : g = halves s.h (.inr j) := by
        apply Fin.ext
        change g.val = 2^s.h+k.val
        have h := congrArg Fin.val later
        change g.val+1 = 2^s.h+(k.val+1) at h
        omega
      rw [same] at count
      simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inr] at count
      exact tailCount_decoded layout _ (liveCutEquiv s.h s.delta cuts).2 k count

/-- A nonzero mathematical group count forces both scheduled physical padding
scans to accept, for the actual mode selected on those cuts. -/
theorem specifiedGroupCount_ne_zero_valid (he : s.e = t*Z) (hc : s.config = fieldWords M*w)
    (fit : 1+t*Z ≤ s.delta) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
    (E : UniversalMachine.Program) (layout : LiveEvaluatorTail.Layout E.extra M w s.delta)
    (init : (Fin t → ℕ) → Code E.extra M) (selected : physicalTag cuts g = some tag)
    (count : specifiedGroupCount fit inc E layout init cuts g ≠ 0) :
    ∀ side, ValidPadding s cuts g tag side := by
  rw [← routed_specifiedGroupCount fit inc E layout init cuts g s.e s.config, selected] at count
  cases tag with
  | unit =>
    apply (validPadding_unit_iff s cuts g).mpr
    by_contra bad
    simp [routedCount, bad] at count
  | pair | tail =>
    by_cases incoming : incomingChecks t Z layout cuts g
    · simp only [routedCount, ite_eq_left incoming] at count
      exact evaluation_padding (by decide) he hc fit inc E layout init incoming count
    · simp [routedCount, incoming] at count

end LiveHeaderProgram.Fields

end VPVNP
end Computability
end OAI
