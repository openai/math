import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordGeometry
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Prod

/-! # Removing crossing bundles

In the uncrossing induction a large crossing supplies a common number of bits
on each of its two diagonals. If no such crossing exists, discarding bundles
below the threshold leaves a noncrossing graph.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace ChordGraph

variable {k : ℕ}

/-- No two diagonals with alternating endpoints both carry positive width. -/
def Noncrossing (g : Widths k) : Prop :=
  ∀ {a b c d : Fin k} (hab : a < b) (hbc : b < c) (hcd : c < d),
    g (edge a c (hab.trans hbc)) = 0 ∨ g (edge b d (hbc.trans hcd)) = 0

theorem card_chord (k : ℕ) : Fintype.card (Chord k) = k.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using Fintype.card_product_filter_lt (α := Fin k)

theorem total_eq_sum (g : Widths k) : total g = ∑ e, g e := by
  conv_lhs => rw [← Finsupp.univ_sum_single g]
  simp only [map_sum, total_single]

/-- Split off the light bundles when the heavy ones do not cross. -/
theorem split_of_no_large_crossing (g : Widths k) (N : ℕ)
    (h : ∀ {a b c d : Fin k} (hab : a < b) (hbc : b < c) (hcd : c < d),
      ¬ (N ≤ g (edge a c (hab.trans hbc)) ∧ N ≤ g (edge b d (hbc.trans hcd)))) :
    ∃ s b : Widths k, g = s + b ∧ total s ≤ Fintype.card (Chord k) * N ∧
      Noncrossing b ∧ ∀ i, load i b ≤ load i g := by
  classical
  let s := g.filter (fun e => g e < N)
  let b := g.filter (fun e => ¬ g e < N)
  have hsum : g = s + b := (Finsupp.filter_add_filter_not g _).symm
  refine ⟨s, b, hsum, ?_, ?_, ?_⟩
  · rw [total_eq_sum]
    calc
      ∑ e, s e ≤ ∑ _e : Chord k, N := Finset.sum_le_sum fun e _ => by
        simp only [s, Finsupp.filter_apply]
        split <;> omega
      _ = _ := by simp
  · intro a b' c d hab hbc hcd
    by_cases hac : g (edge a c (hab.trans hbc)) < N
    · exact Or.inl (by simp [b, hac])
    · have hbd : g (edge b' d (hbc.trans hcd)) < N :=
        lt_of_not_ge fun hbd => h hab hbc hcd ⟨Nat.le_of_not_gt hac, hbd⟩
      exact Or.inr (by simp [b, hbd])
  · intro i
    have heq := congrArg (load i) hsum
    rw [map_add] at heq
    omega

/-- Remove the same number of bits from each diagonal of a crossing. -/
theorem exists_peel_crossing (g : Widths k) {a b c d : Fin k}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (j : ℕ)
    (hac : j ≤ g (edge a c (hab.trans hbc))) (hbd : j ≤ g (edge b d (hbc.trans hcd))) :
    ∃ r : Widths k, g = r + j • crossing hab hbc hcd := by
  classical
  let ac := edge a c (hab.trans hbc)
  let bd := edge b d (hbc.trans hcd)
  have hne : ac ≠ bd := fun h => hab.ne (congrArg (fun e : Chord k => e.1.1) h)
  let removed := j • crossing hab hbc hcd
  have hle (e : Chord k) : removed e ≤ g e := by
    change (j • (unitChord ac + unitChord bd)) e ≤ g e
    by_cases hea : e = ac
    · subst e
      simpa [unitChord, Finsupp.single_apply, hne.symm] using hac
    by_cases heb : e = bd
    · subst e
      simpa [unitChord, Finsupp.single_apply, hne] using hbd
    simp [unitChord, Ne.symm hea, Ne.symm heb]
  refine ⟨Finsupp.equivFunOnFinite.symm (fun e => g e - removed e), ?_⟩
  ext e
  exact (Nat.sub_add_cancel (hle e)).symm

end ChordGraph

end SpectralBooks
end LinearAlgebra
end OAI
