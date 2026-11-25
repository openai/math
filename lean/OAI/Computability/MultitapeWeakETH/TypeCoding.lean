import OAI.Computability.MultitapeWeakETH.Coloring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalPrefixWords
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalRateBridge

/-! # Independent colors extracted from prescribed joint types -/

namespace OAI.Computability.MultitapeWeakETH

open MatrixMultiplication MatrixMultiplication.Foundation
open ConditionalPrefixWords StageHierarchyResources LabelHierarchyCounts HierarchySeparationRates
open Filter
open scoped BigOperators Topology Classical

private def prefixBit : (n : ℕ) → LabelRecord (fun _ => Bool) n → Fin n → Bool
  | 0, _, i => Fin.elim0 i
  | n+1, r, i => Fin.lastCases r.2 (prefixBit n r.1) i

private theorem prefixBit_source {A : Type*} (labels : ℕ → A → Bool) (x : A)
    (n : ℕ) (i : Fin n) : prefixBit n (labelRecordOf labels n x) i = labels i x := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [prefixBit,labelRecordOf]
    · simpa [prefixBit,labelRecordOf] using ih j

/-- An independent endpoint reads only its binary column. Every tuple of
colors admits a single joint array with exactly the prescribed multiplicity
of each source word. The budget is the finite coloring union bound. -/
theorem exact_type_colors {A : Type} [Fintype A] (counts : A → ℕ) (labels : ℕ → A → Bool)
    (depth t : ℕ) (separate : Function.Injective (labelRecordOf labels depth))
    (C : Fin depth → Type) [∀ j, Fintype (C j)]
    (budget : ∀ j : Fin depth,
      let R := Fin (t * ∑ x, counts x)
      let M := stageRefinementCount counts labels j t
      let k := Fintype.card (C j)
      (Fintype.card (ExactPrefix counts labels j t R)*k) *
        ((k-1)^M*k^(Fintype.card (R → Bool)-M)) < k^Fintype.card (R → Bool)) :
    let R := Fin (t * ∑ x, counts x)
    ∃ color : (j : Fin depth) → (R → Bool) → C j, ∀ target : (j : Fin depth) → C j,
      ∃ word : PopulationWords R (fun a => t*counts a), ∀ j : Fin depth,
        color j (fun i => labels j (word.val i)) = target j := by
  intro R
  have one (j : Fin depth) := exists_column_coloring
    (P := ExactPrefix counts labels j t R) (C := C j) conditionalFinset
    (conditionalFinset_card (counts := counts) (labels := labels)) (budget j)
  choose color hits using one
  refine ⟨color,fun target => ?_⟩
  have partialWord (n : ℕ) (hn : n ≤ depth) : ∃ pre : ExactPrefix counts labels n t R,
      ∀ j : Fin n, color (j.castLE hn) (fun i => prefixBit n (pre.val i) j) = target (j.castLE hn) := by
    induction n with
    | zero =>
      refine ⟨rootPrefixWord counts labels t R (by simp [R,Finset.mul_sum]),fun j => Fin.elim0 j⟩
    | succ n ih =>
      obtain ⟨old,correct⟩ := ih (by omega)
      let last : Fin depth := ⟨n,hn⟩
      obtain ⟨column,valid,chosen⟩ := hits last old (target last)
      let fine : conditionalPool old := ⟨column,(mem_conditionalFinset old column).mp valid⟩
      refine ⟨appendPrefix old fine, fun j => Fin.lastCases ?_ (fun l => ?_) j⟩
      · simp only [appendPrefix_val,prefixBit,Fin.lastCases_last]
        rw [show (Fin.last n).castLE hn = last from Fin.ext rfl]
        exact chosen
      · simp only [appendPrefix_val,prefixBit,Fin.lastCases_castSucc]
        rw [show l.castSucc.castLE hn = l.castLE (by omega : n ≤ depth) from Fin.ext rfl]
        exact correct l
  obtain ⟨pre,correct⟩ := partialWord depth le_rfl
  refine ⟨decodeSourceWord separate pre,fun j => ?_⟩
  have column (i : R) : labels j ((decodeSourceWord separate pre).val i) =
      prefixBit depth (pre.val i) j := by
    change labels j (sourceSymbol pre i) = _
    rw [← sourceSymbol_record pre i,prefixBit_source]
  have hit := correct j
  rw [show j.castLE (le_refl depth) = j from Fin.ext rfl] at hit
  simpa only [column] using hit

/-- The log-base-two growth rate of the compatible extension count is the
conditional entropy, in bits, of the next coordinate given its prefix. -/
theorem extension_entropy_limit {A : Type} [Fintype A] (counts : A → ℕ)
    (positive : 0 < ∑ a, counts a) (labels : ℕ → A → Bool) (depth : ℕ) (j : Fin depth) :
    Tendsto (fun t : ℕ => Real.logb 2 (stageRefinementCount counts labels j t) /
      ((t : ℝ)*(∑ a, counts a : ℕ))) atTop
      (𝓝 ((FiniteLabelHierarchy.ofLawLabels (ConditionalLabels.normalizedCountLaw counts positive)
        labels depth).refinementEntropy j / Real.log 2)) := by
  rw [← ConditionalLabels.stageEntropyRate_div_eq_normalizedCountLaw_refinementEntropy
    counts positive labels depth j j.isLt]
  have conv := ((tendsto_log_stageRefinementCount_div counts labels j).div_const
    ((∑ a, counts a : ℕ) : ℝ)).div_const (Real.log 2)
  apply conv.congr
  intro t
  rw [Real.logb]
  ring

end OAI.Computability.MultitapeWeakETH
