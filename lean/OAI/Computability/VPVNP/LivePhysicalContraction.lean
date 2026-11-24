import OAI.Computability.VPVNP.ChainModeProduct
import OAI.Computability.VPVNP.GroupContraction
import OAI.Computability.VPVNP.LiveIncomingPadding

/-! # The integer count from the physical live program

The group program's specification is local. On each group it checks the two
incident mode bits, then accepts in unit mode or runs the first-half pair or
the tail transition. Reindexing the raw shared bits and summing these native
counts yields one unit path plus the full evaluator sum, on the same processor
prefix and advice as the primed contraction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open ExponentTrace LiveChain LiveEvaluatorEncoding
open BurstRAM BurstRAM.PrivateRAM
open scoped Classical

variable {h Δ t Z M w : ℕ} {Nom : Type*} [Fintype Nom]
variable {Path : Exterior h Δ → Fin (2^h) → Nom → Type*} [∀ ξ i μ, Fintype (Path ξ i μ)]
variable (fit : 1 + t * Z ≤ Δ) (inc : ∀ ξ i μ, Path ξ i μ → Fin t → ℕ)
variable (E : UniversalMachine.Program) (layout : LiveEvaluatorTail.Layout E.extra M w Δ)
variable (init : (Fin t → ℕ) → Code E.extra M)

/-- First-half and tail checks, selected by the one-based group number in
its header. Agreement of the mode bits is imposed separately. -/
noncomputable def groupEvaluation (cuts : AllCuts h Δ) (j : Fin (2^(h+1))) : ℕ :=
  let c := liveCutEquiv h Δ cuts
  Sum.elim (pairCount fit inc c.1)
    (tailCount E layout (init (fun a => (counters fit c.1 (Fin.last _) a).val)) c.2)
    ((halves h).symm j)

/-- The integer count required from one native group, including mixed mode,
clamped endpoints, and failure of a first-half or tail check. -/
noncomputable def specifiedGroupCount (c : AllCuts h Δ) (j : Fin (2^(h+1))) : ℕ :=
  unitGroupCount c j + if evalCutMode c j.castSucc ∧ evalCutMode c j.succ ∧ incomingChecks t Z layout c j
    then groupEvaluation fit inc E layout init c j else 0

private theorem groupEvaluation_active (c : AllCuts h Δ)
    (ok : (∏ j, groupEvaluation fit inc E layout init c j) ≠ 0) : activeCuts c := by
  have hn := Finset.prod_ne_zero_iff.mp ok
  intro j
  rcases coverCuts j with rfl | rfl | ⟨i,rfl⟩ | ⟨i,rfl⟩
  · intro ht; exact (Nat.lt_irrefl _ ht).elim
  · intro _ ht; exact (Nat.lt_irrefl _ ht).elim
  · intro _ _
    have hx := hn (halves h (.inl i)) (Finset.mem_univ _)
    simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inl] at hx
    exact pairCount_mode fit inc (liveCutEquiv h Δ c).1 i hx
  · intro _ _
    let s : Fin (2^h) := ⟨i.val, by have := i.isLt; omega⟩
    have hx := hn (halves h (.inr s)) (Finset.mem_univ _)
    simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inr] at hx
    exact tailCount_mode E layout _ (liveCutEquiv h Δ c).2 i hx

/-- Every nonzero product supplies the canonical incoming first-half or tail
format from the predecessor's own successful outgoing check. -/
theorem groupEvaluation_incoming (c : AllCuts h Δ)
    (ok : (∏ j, groupEvaluation fit inc E layout init c j) ≠ 0) (j : Fin (2^(h+1))) :
    incomingChecks t Z layout c j := by
  have hn := Finset.prod_ne_zero_iff.mp ok
  constructor
  · intro i _
    have hx := hn (halves h (.inl i)) (Finset.mem_univ _)
    simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inl] at hx
    exact pairCount_padding fit inc _ i hx
  · intro k _
    let i : Fin (2^h) := ⟨k.val,by have := k.isLt; omega⟩
    have hx := hn (halves h (.inr i)) (Finset.mem_univ _)
    simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inr] at hx
    exact tailCount_decoded layout _ (liveCutEquiv h Δ c).2 k hx

/-- At fixed physical cuts, enforcing both incident formats in each
group preserves the original product. A malformed incoming cut already
forces a zero factor at its predecessor. -/
theorem specifiedGroupCount_product (c : AllCuts h Δ) :
    (∏ j, specifiedGroupCount fit inc E layout init c j) =
      (if c = (fun _ _ => false) then 1 else 0) + ∏ j, groupEvaluation fit inc E layout init c j := by
  let ev (c : AllCuts h Δ) (j : Fin (2^(h+1))) :=
    if evalCutMode c j.castSucc ∧ evalCutMode c j.succ ∧ incomingChecks t Z layout c j
    then groupEvaluation fit inc E layout init c j else 0
  have mode c j (ok : ev c j ≠ 0) : evalCutMode c j.castSucc ∧ evalCutMode c j.succ := by
    by_cases hc : evalCutMode c j.castSucc ∧ evalCutMode c j.succ ∧ incomingChecks t Z layout c j
    · exact ⟨hc.1, hc.2.1⟩
    · exact (ok (ite_eq_right hc)).elim
  change (∏ j, (unitGroupCount c j + ev c j)) = _
  rw [group_mode_product ev mode c]
  congr 1
  by_cases hp : (∏ j, groupEvaluation fit inc E layout init c j) = 0
  · obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.mp hp
    rw [hp]
    exact Finset.prod_eq_zero hj (by simp [ev, hz])
  · have active := groupEvaluation_active fit inc E layout init c hp
    exact Finset.prod_congr rfl fun j _ => ite_eq_left
      ⟨active _, active _, groupEvaluation_incoming fit inc E layout init c hp j⟩

private theorem group_sum : (∑ c : AllCuts h Δ, ∏ j, specifiedGroupCount fit inc E layout init c j) =
    1 + ∑ c : AllCuts h Δ, ∏ j, groupEvaluation fit inc E layout init c j := by
  simp_rw [specifiedGroupCount_product fit inc E layout init, Finset.sum_add_distrib]
  simp

/-- The integer identity from Section 14.3, reduced to the native site and
single-group specifications. It holds for the very same prefix whose clocked
path count occurs in the integer family. -/
theorem physical_two_modes {n a d e pc regs pubs : ℕ} (table : UniversalMachine.Program)
    (hf : ProcessorInput.Fits table n d (2^e) w) (advice : CutSchedule.Bits a)
    (D : Machine w pc regs pubs) (fuel : ℕ) (start : BurstRAM.Word w)
    (hw : 4 ≤ w) (hc : 2^d * 2^e < 2^w)
    (processor : ∀ (v : Fin (2^d)) (hdr : ProcessorInput.Header) bits,
      acceptingCount (ProcessorInput.encode table n v hdr bits hf) =
        Nat.card (D.IncidentPaths fuel start (ProcessorInput.headerWord hw hdr) (by omega) hc v bits))
    (group : ∀ (c : AllCuts h Δ) (j : Fin (2^(h+1))),
      Nat.card (ActualPaths D.program fuel start (RAMMemory.initialMemory (2^d)
        (liveHeader (d := d) hw advice c j)) (withinCaps (2^d) (2^e))) =
        specifiedGroupCount fit inc E layout init c j)
    (bound : ∀ ξ (μ : Fin (2^h) → Nom) (q : (i : Fin (2^h)) → Path ξ i (μ i)) (i : Fin (2^h)) a,
      partialSum (fun j => inc ξ j (μ j) (q j)) i.succ a < 2^Z)
    (initial : (Fin t → ℕ) → UniversalMachine.Config E.extra)
    (hi : ∀ e, (init e).toState = EvaluatorTail.canonical (initial e))
    (space : ∀ e, LiveEvaluatorTail.HistoriesFit E M (2^h) (initial e)) :
    PairedChain.original (h := h) (Δ := Δ) table hf advice = 1 +
      ∑ ξ : Exterior h Δ, ∑ μ : Fin (2^h) → Nom, ∑ q : (i : Fin (2^h)) → Path ξ i (μ i),
        UniversalMachine.paths E (2^h) (initial (fun a => ∑ i, inc ξ i (μ i) (q i) a)) := by
  rw [original_eq_group_counts table hf advice D fuel start hw hc processor]
  simp_rw [group]
  rw [group_sum, contract_halves (groupEvaluation fit inc E layout init)
    (pairCount fit inc) (fun fst lst => tailCount E layout
      (init (fun a => (counters fit fst (Fin.last _) a).val)) lst)]
  · rw [evaluation_contraction fit inc bound E layout initial init hi space]
  all_goals intro c i; simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

end ChainAssignments

end VPVNP
end Computability
end OAI
