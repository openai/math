import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.TaggedPruneNetwork

namespace OAI
/-! # Pruning the shared physical batch host after closing its sockets -/

noncomputable section
namespace Hierarchy.Tagged.WideHost
open Catalyst CatalystSubstitution ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k : ℕ} {H : Type} [Fintype H]

open TaggedPrune

/-- Correct deterministic histories select the original summand even in
positive characteristic. The weight can include an entire dependent family
of summed site/edge slots. Verifying this weight is a pointwise task after
the selector and the legal history have been fixed. -/
theorem selector_of_unique_history {h w B : ℕ} {b : Fin k → ℕ}
    {count : Equiv.Perm (Row h) → ℕ} {T : Type} [Fintype T]
    (keep : Index count → Prop) (enc : Encoding count B) (route : Index count → Table F h w b)
    (x : OpenPins h w b → Bool) (s : Fin B → Bool) (decode : T → Option (Index count))
    (weight : T → F) (reject : ∀ t, decode t = none → weight t=0)
    (legal : ∀ t a, decode t = some a → keep a ∧ reads enc x s a)
    (unique : ∀ a, keep a → reads enc x s a → ∃! t,decode t=some a)
    (eval : ∀ t a,decode t = some a → weight t=route a x) :
    ∑ t,weight t = selected keep enc route x s := by
  classical
  by_cases found : ∃ a,keep a ∧ reads enc x s a
  · obtain ⟨a,accepted,read⟩ := found
    obtain ⟨t,ht,only⟩ := unique a accepted read
    rw [selected_of_reads _ _ _ _ _ a accepted read,←eval t a ht]
    apply Finset.sum_eq_single t
    · intro t' _ distinct
      cases pick : decode t' with
      | none => exact reject t' pick
      | some a' =>
        obtain rfl := reads_unique enc (legal t' a' pick).2 read
        exact (distinct (only t' pick)).elim
    · simp
  · rw [selected_of_no_read _ _ _ _ _ (fun a ha rd => found ⟨a,ha,rd⟩)]
    apply Finset.sum_eq_zero
    intro t _
    cases pick : decode t with
    | none => exact reject t pick
    | some a => exact (found ⟨a,legal t a pick⟩).elim

/-- The native host first closes the independent batch and control sockets,
then contracts the shared protocol workspace, then the unique selector word.
This is the precise coefficient presented to the pruning estimate. -/
theorem old_gap {h w selectors M : ℕ} (b : Fin k → ℕ) {D : Layout h w b}
    {count : Equiv.Perm (Row h) → ℕ} (enc : Encoding count selectors)
    (route : Index count → Table F h w b) (links : Index count → Links D M)
    (routing : ∀ perm, (∑ i : Fin (count perm),route ⟨perm,i⟩) = perTag perm)
    (tables : ∀ a, ((CorrectionProducts.raw (route a)).group D.port).Restricts
      (LinearAlgebra.SpectralBooks.ChordGraph.raw F
        (AdaptiveProbe.installedWidths (links a).ends (links a).bits)))
    (hm : 0<M) (hw : 0<w) (hk : 0<k)
    (localPart : BitNetwork F (Fintype.card (OpenPins h w b ⊕ (Fin selectors ⊕ H))))
    (os : List (Occurrence F k)) (boards : Parts F (OpenPins h w b ⊕ (Fin selectors ⊕ H)) os)
    (realizes : ∀ x s, (∑ y : H → Bool,closed localPart os boards (Sum.elim x (Sum.elim s y))) =
      selected (fun a => (links a).Keep (2^h)) enc route x s) :
    (tableApprox b (exactValue os (host b localPart os boards))).Gap (coeff F h w)
      ((2:ℝ)^h*w/M - 2*(k:ℝ)*((h:ℝ)*2^h+selectors)) := by
  apply pruning_gap hm hw hk _ D (encoded_count enc) route links routing tables
  funext x
  change Catalyst.Port (pins h w) b → Bool at x
  refine (tableApprox_coeff b (exactValue os (host b localPart os boards)) x).trans ?_
  refine (exactValue_host b localPart os boards x).trans ?_
  let value (a : Fin selectors ⊕ H → Bool) := closed localPart os boards (Sum.elim x a)
  trans ∑ a : Fin selectors ⊕ H → Bool, value a
  · apply Finset.sum_congr (congrArg (@Finset.univ (Fin selectors ⊕ H → Bool)) (Subsingleton.elim _ _))
    intro a _
    rfl
  refine ((Equiv.sumArrowEquivProdArrow (Fin selectors) H Bool).symm.sum_comp value).symm.trans ?_
  rw [Fintype.sum_prod_type]
  change (∑ s, ∑ y : H → Bool, closed localPart os boards (Sum.elim x (Sum.elim s y))) = _
  simp only [realizes]
  exact contract_selectors _ enc route x

/-- At fixed original tag and selector bits the native prefixScalar can reject
a malformed word before the terminal paid machine has any geometric
interpretation. For authentic, admitted words the prune read and the
signed contraction of the designated term determine the host coefficient. -/
theorem selected_of_prefix {F : Type*} [Field F] {h w k B : ℕ} {b : Fin k→ℕ}
    {count : Equiv.Perm (Row h)→ℕ} (keep : Index count→Prop) (enc : Encoding count B)
    (route : Index count→Table F h w b) (x : OpenPins h w b→Bool) (s : Fin B→Bool)
    (admitted : Prop) (prefixScalar terminal : F)
    (prefixValue : Function.Bijective (tag (fun i=>x (.inl i))) → prefixScalar=if admitted then 1 else 0)
    (tape : Function.Bijective (tag (fun i=>x (.inl i))) → (admitted ↔ ∃a,reads enc x s a))
    (paid : ∀a,reads enc x s a → terminal=if keep a then route a x else 0) :
    (if Function.Bijective (tag (fun i=>x (.inl i))) then 1 else 0)*prefixScalar*terminal =
      selected keep enc route x s := by
  classical
  by_cases valid : Function.Bijective (tag (fun i=>x (.inl i)))
  · by_cases active : admitted
    · obtain ⟨a,read⟩ := (tape valid).mp active
      by_cases retained : keep a
      · rw [selected_of_reads keep enc route x s a retained read]
        simp only [ite_eq_left valid, prefixValue valid, ite_eq_left active, paid a read, ite_eq_left retained, one_mul]
      · have empty : ∀a',keep a' → ¬reads enc x s a' := by
          intro a' h choose
          exact retained ((reads_unique enc choose read) ▸ h)
        rw [selected_of_no_read keep enc route x s empty]
        simp only [ite_eq_left valid, prefixValue valid, ite_eq_left active, paid a read, ite_eq_right retained, one_mul]
    · rw [selected_of_no_read keep enc route x s (fun a _ read=>active ((tape valid).mpr ⟨a,read⟩))]
      simp only [ite_eq_left valid, prefixValue valid, ite_eq_right active, one_mul, zero_mul]
  · have empty : ∀a,keep a → ¬reads enc x s a := by
      intro a _ read
      exact valid (read.1 ▸ a.1.bijective)
    rw [selected_of_no_read keep enc route x s empty]
    simp only [ite_eq_right valid, zero_mul]

end Hierarchy.Tagged.WideHost

end
end OAI
