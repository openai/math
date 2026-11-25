import OAI.Optimization.LinearProgramming.Geometry.Admissible
import OAI.Optimization.LinearProgramming.Geometry.MinorKeys
import OAI.Optimization.LinearProgramming.Geometry.CircuitFamily

/-! Register all signed circuit representatives against the same canonical two-matrix
minor assignment as the rounded pivot rows. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Submodule Compression

variable {n r s : ℕ} {κ : Type*}

/-- Full-height rows use exactly the unordered prefix-minor keys used by the pivot construction. -/
noncomputable def minorCircuitFamily (A : Matrix (Fin r) (Fin n) ℚ)
    (keyLog : ℕ × Finset (Fin n) → ℚ) : Finset (Fin n → ℝ) :=
  fullCircuitFamily r (A.map (Rat.castHom ℝ)) (fun J j => (keyLog (prefixMinorKey J j) : ℝ))

private theorem abs_signedCircuit_real {k : ℕ} (A : Matrix (Fin (k+1)) (Fin n) ℚ)
    (code : (Fin k → Fin n) × Bool) (j : Fin n) :
    |signedCircuit (A.map (Rat.castHom ℝ)) code j| = |((circuitMinor A code.1 j : ℚ) : ℝ)| := by
  have hmap : circuitMinor (A.map (Rat.castHom ℝ)) code.1 j = ((circuitMinor A code.1 j : ℚ) : ℝ) :=
    ((Rat.castHom ℝ).map_det _).symm
  unfold signedCircuit
  split
  · simpa only [Pi.neg_apply, abs_neg] using congrArg abs hmap
  · exact congrArg abs hmap

private theorem registeredCircuit_of_matching (A : Matrix (Fin r) (Fin n) ℚ)
    (keyLog : ℕ × Finset (Fin n) → ℚ) (ell : κ → ℝ) (f : κ → ℚ)
    (matching : ∀ {k : ℕ} (hk : k+1 ≤ r) (J : Fin k → Fin n) (j : Fin n),
      circuitMinor (A.submatrix (Fin.castLE hk) id) J j ≠ 0 →
      ∃ u, f u = keyLog (prefixMinorKey J j) ∧
        ell u = Real.logb 2 |((circuitMinor (A.submatrix (Fin.castLE hk) id) J j : ℚ) : ℝ)|)
    (t : Fin n → ℝ) {c : Fin n → ℝ} (hc : c ∈ minorCircuitFamily A keyLog) :
    RegisteredVector (span ℝ (Set.range (A.map (Rat.castHom ℝ)).row)) ell (fun u => (f u : ℝ))
      t (priceNormalize t c) := by
  cases r with
  | zero => simp [minorCircuitFamily, fullCircuitFamily] at hc
  | succ k =>
    let L (J : Fin k → Fin n) (j : Fin n) : ℝ := keyLog (prefixMinorKey J j)
    change c ∈ compressedCircuitFamily (A.map (Rat.castHom ℝ)) L at hc
    obtain ⟨code, _, rfl⟩ := (mem_compressedCircuitFamily (D := A.map (Rat.castHom ℝ)) (f := L)).mp hc
    let raw := signedCircuit (A.map (Rat.castHom ℝ)) code
    refine ⟨raw, (fun j => (keyLog (prefixMinorKey code.1 j) : ℝ)), 1, ?_, by norm_num, ?_, ?_⟩
    · unfold raw signedCircuit
      split
      · exact Submodule.neg_mem _ (circuitMinor_mem_rowSpan _ _)
      · exact circuitMinor_mem_rowSpan _ _
    · intro j hj
      have ha := abs_signedCircuit_real A code j
      have hnz : circuitMinor A code.1 j ≠ 0 := by
        intro h0
        exact hj (abs_eq_zero.mp (ha.trans (by simp [h0])))
      have hid : A.submatrix (Fin.castLE (show k+1 ≤ k+1 from le_rfl)) id = A := rfl
      obtain ⟨u, hfu, heu⟩ := matching (show k+1 ≤ k+1 from le_rfl) code.1 j (by simpa only [hid] using hnz)
      refine ⟨u, congrArg (fun z : ℚ => (z : ℝ)) hfu, ?_⟩
      rw [hid] at heu
      exact heu.trans (congrArg (Real.logb 2) ha.symm)
    · simpa only [one_mul] using priceNormalize_normalizedMinorRow raw _ t

/-- Primal circuit registration uses the nonzero-minor subtype of the original matrix pair. -/
theorem registered_primal_circuit (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (f : NonzeroPairMinor D E → ℚ) (t : Fin n → ℝ) {c : Fin n → ℝ}
    (hc : c ∈ minorCircuitFamily D (prefixAssignment D E f)) :
    RegisteredVector (span ℝ (Set.range (D.map (Rat.castHom ℝ)).row))
      (pairMinorLog D E) (fun u => (f u : ℝ)) t (priceNormalize t c) :=
  registeredCircuit_of_matching D _ _ f (fun hk J j => prefixAssignment_matches D E f hk J j) t hc

/-- Dual circuits use the other summand of the very same minor index type. -/
theorem registered_dual_circuit (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (f : NonzeroPairMinor D E → ℚ) (t : Fin n → ℝ) {c : Fin n → ℝ}
    (hc : c ∈ minorCircuitFamily E (dualPrefixAssignment D E f)) :
    RegisteredVector (span ℝ (Set.range (E.map (Rat.castHom ℝ)).row))
      (pairMinorLog D E) (fun u => (f u : ℝ)) t (priceNormalize t c) :=
  registeredCircuit_of_matching E _ _ f (fun hk J j => dualPrefixAssignment_matches D E f hk J j) t hc

/-- The primal and dual circuit families lie in the nonnegative unit cube. -/
theorem minorCircuitFamily_unitCube (A : Matrix (Fin r) (Fin n) ℚ)
    (keyLog : ℕ × Finset (Fin n) → ℚ) {c : Fin n → ℝ} (hc : c ∈ minorCircuitFamily A keyLog)
    (i : Fin n) : 0 ≤ c i ∧ c i ≤ 1 := by
  cases r with
  | zero => simp [minorCircuitFamily, fullCircuitFamily] at hc
  | succ k =>
    let L (J : Fin k → Fin n) (j : Fin n) : ℝ := keyLog (prefixMinorKey J j)
    change c ∈ compressedCircuitFamily (A.map (Rat.castHom ℝ)) L at hc
    exact compressedCircuitFamily_unitCube (D := A.map (Rat.castHom ℝ)) (f := L) hc i

end Geometry
end LinearProgramming
end Optimization
end OAI
