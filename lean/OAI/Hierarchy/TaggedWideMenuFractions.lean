import OAI.Hierarchy.ProbePhysicalTypeMenu

namespace OAI
/-! # A common price interval for every retained width code -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterBudget TaggedShorterSupergroups TaggedShorterPacking Real Filter Set
open scoped Classical BigOperators

/-- A single price interval works for every width code and every permitted
parent. It therefore determines just one fixed shortening offset. -/
theorem menu_fractions {u : ℝ→ℝ} {s A ε p q Q σ L δ η ξ : ℝ}
    (profile : TaggedWidthProfile.Admissible s u) (price : Choice u A ε p q Q σ L δ η ξ) (W m : ℕ) :
    ∃ U : ℝ, ∀ a∈Icc 1 A,∀ i : Fin (m+1), 3*ξ≤typeFraction u δ ξ a (W,i.val) ∧
      typeFraction u δ ξ a (W,i.val)≤U := by
  choose upper pos fits using fun i : Fin (m+1)=>typeFraction_bounded profile A δ ξ (W,i.val)
  refine ⟨∑i,upper i,?_⟩
  intro a ha i
  obtain ⟨_,_,slope,_,paid,_,_,_,_⟩ := price.exponents a ha
  refine ⟨fraction_lower price.xi_pos.le paid (show 0 ≤ 1-(-deriv u a)-δ by linarith) W i.val,?_⟩
  exact (fits i a ha).trans (Finset.single_le_sum (fun j _=>(pos j).le) (Finset.mem_univ i))

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
