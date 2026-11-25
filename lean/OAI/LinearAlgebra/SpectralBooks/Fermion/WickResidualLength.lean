import OAI.LinearAlgebra.SpectralBooks.Fermion.WickResidual
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickReversalSign

/-! # Lengths of the unmatched Wick blocks -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion.Matching

variable {α : Type*}

private theorem length_rest_add_edges {l r : List α} (p : Matching l r) :
    p.leftRest.length + p.edges = l.length ∧ p.rightRest.length + p.edges = r.length := by
  induction l generalizing r with
  | nil => simp [leftRest, rightRest, edges]
  | cons x l ih =>
    rcases p with p | ⟨j,p⟩
    · obtain ⟨hl, hr⟩ := ih p
      simp only [leftRest, rightRest, edges, List.length_cons]
      omega
    · obtain ⟨hl, hr⟩ := ih p
      rw [List.length_eraseIdx_of_lt j.isLt] at hr
      have := j.isLt
      simp only [leftRest, rightRest, edges, List.length_cons]
      omega

theorem leftRest_length {l r : List α} (p : Matching l r) :
    p.leftRest.length = l.length - p.edges := by
  have := (length_rest_add_edges p).1
  omega

theorem rightRest_length {l r : List α} (p : Matching l r) :
    p.rightRest.length = r.length - p.edges := by
  have := (length_rest_add_edges p).2
  omega

end Fermion.Matching

end SpectralBooks
end LinearAlgebra
end OAI
