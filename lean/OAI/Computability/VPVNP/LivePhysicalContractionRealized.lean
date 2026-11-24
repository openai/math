import OAI.Computability.VPVNP.LivePhysicalContraction
import OAI.Computability.VPVNP.GroupIncidentContraction

/-!
# Two live modes on actual RAM link assignments

The fixed table reads the realized physical link bits at each site. Regrouping
those coefficients and applying the mode and cut checks gives the integer
identity used in the diagonal argument.
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

/-- The integer identity from Section 14.3, reduced to the native site and
single-group specifications. It holds for the very same prefix whose clocked
path count occurs in the integer family. -/
theorem physical_two_modes_realized {n a d e pc regs pubs : ℕ} (table : UniversalMachine.Program)
    (hf : ProcessorInput.Fits table n d (2^e) w) (advice : CutSchedule.Bits a)
    (D : Machine w pc regs pubs) (fuel : ℕ) (start : BurstRAM.Word w)
    (hw : 4 ≤ w) (hc : 2^d * 2^e < 2^w)
    (processor : ∀ (v : Fin (2^d)) (hdr : ProcessorInput.Header) (sends : RAMLayout.SendArrays d (2^e) w),
      acceptingCount (ProcessorInput.encode table n v hdr (RAMLayout.incidentBits sends v) hf) =
        Nat.card (D.IncidentPaths fuel start (ProcessorInput.headerWord hw hdr) (by omega) hc v (RAMLayout.incidentBits sends v)))
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
  rw [original_eq_incident_counts table hf advice D fuel start hw hc processor]
  simp_rw [group]
  have sumModes : (∑ c : AllCuts h Δ, ∏ j, specifiedGroupCount fit inc E layout init c j) =
      1 + ∑ c : AllCuts h Δ, ∏ j, groupEvaluation fit inc E layout init c j := by
    simp_rw [specifiedGroupCount_product fit inc E layout init, Finset.sum_add_distrib]
    simp
  rw [sumModes, contract_halves (groupEvaluation fit inc E layout init)
    (pairCount fit inc) (fun fst lst => tailCount E layout
      (init (fun a => (counters fit fst (Fin.last _) a).val)) lst)]
  · rw [evaluation_contraction fit inc bound E layout initial init hi space]
  all_goals intro c i; simp only [groupEvaluation, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

end ChainAssignments

end VPVNP
end Computability
end OAI
