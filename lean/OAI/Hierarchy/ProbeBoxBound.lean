import OAI.Hierarchy.ProbeDiscrepancy

namespace OAI
/-! # Bounding the true discrepancy using a zero spectral scale -/

namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical
noncomputable section

variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]

/-- Zero scale is an admissible physical test realization. Thus all price grids with
entries in [0,C] have discrepancy at most C, independent of local party naming. -/
theorem discrepancy_box_bound (edge : E→Chord k) (req : A→E) (p : E→ℝ) (C : ℝ) (hn : 0≤C)
    (box : ∀e,0≤p e ∧ p e≤C) : discrepancy F edge req p≤C := by
  classical
  let e := edge (Classical.arbitrary E)
  let : Nontrivial (Fin k) := ⟨e.1.1,e.1.2,e.2.ne⟩
  let φ : Spectrum F k := (spectrum_nonempty.{0} (Fin k) F).to_subtype.some
  refine (discrepancy_le F edge req p φ (le_refl (0:ℝ))).trans ?_
  apply Finset.sup'_le
  intro l _; cases l with
  | inl l => change max 0 (0*distance φ _ - p l) ≤ C; simp [max_eq_left (neg_nonpos.mpr (box l).1),hn]
  | inr a => change |0*distance φ _-p (req a)|≤C; simpa [abs_of_nonneg (box _).1] using (box (req a)).2

end
end Hierarchy.Probe

end OAI
