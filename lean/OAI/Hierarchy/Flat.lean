import OAI.Hierarchy.FlatPrices
import OAI.LinearAlgebra.SpectralBooks.EveryField

namespace OAI
/-! # Euclidean spectral flats of a fixed dimension

The tensor prices on an isometric placement of Euclidean space can be pulled back
to Euclidean space itself. This identifies the coordinate formulation of the flat
theorem with the finite-placement price system. -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks

namespace HasSpectralFlat

variable {F : Type*} [Field F]

/-- Intersect an isometric Euclidean placement with its first coordinate hyperplane. -/
theorem pred {d : ℕ} (h : HasSpectralFlat F (d+1)) : HasSpectralFlat F d := by
  obtain ⟨P⟩ := h
  let f (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d+1)) :=
    WithLp.toLp 2 (Fin.cons 0 (fun i => x i))
  refine ⟨P.pullback f (Isometry.of_dist_eq fun x y => ?_)⟩
  simp [EuclideanSpace.dist_eq, f, Fin.sum_univ_succ]

/-- Spectral flat dimensions are downward closed. -/
theorem of_le {d n : ℕ} (le : d≤n) : HasSpectralFlat F n → HasSpectralFlat F d := by
  induction n, le using Nat.le_induction with
  | base => exact id
  | succ n hn ih => exact fun H => ih H.pred

/-- The spectral plane exists in every characteristic. -/
theorem plane (F : Type*) [Field F] : HasSpectralFlat F 2 :=
  ⟨(matrix_spectral_plane F).choose⟩

/-- Failure in any dimension has a greatest realized dimension at least two and
a first missing dimension exactly one larger. -/
theorem maximal_of_missing {d : ℕ} (missing : ¬HasSpectralFlat F d) :
    ∃ k, 2≤k ∧ k<d ∧ HasSpectralFlat F k ∧
      (∀ t, HasSpectralFlat F t → t≤k) := by
  classical
  have h : ∃ n, ¬HasSpectralFlat F n := ⟨d,missing⟩
  let n := Nat.find h
  have no : ¬HasSpectralFlat F n := Nat.find_spec h
  have before {t : ℕ} (ht : t<n) : HasSpectralFlat F t := by
    simpa only [not_not] using (Nat.find_min h ht)
  have hn : 2<n := by
    by_contra! small
    exact no (of_le small (plane F))
  have nd : n≤d := Nat.find_min' h missing
  exact ⟨n-1,by omega,by omega,before (by omega),fun t flat => by
    by_contra! big
    exact no (of_le (by omega) flat)⟩

end HasSpectralFlat
end Hierarchy

end OAI
