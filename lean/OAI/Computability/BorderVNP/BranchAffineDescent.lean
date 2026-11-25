import OAI.Computability.BorderVNP.BranchAffineRows

/-! # The equations over the finite advice field

The construction of the cleared rows commutes with scalar extension, so the curve
equations over the constant closure descend to the common finite advice field. The
equations in the affine variables and deformation parameter have total degree at most
the table degree plus two.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {I σ K T : Type*} [Field K] [Field T] {m d : ℕ}

/-- Clearing chart numerators is compatible with every field embedding, at the same
prescribed denominator exponent. -/
theorem map_clearedSubstitution (f : K →+* T) (den : MvPolynomial σ K) (num : I → MvPolynomial σ K)
    (e : ℕ) (p : MvPolynomial I K) :
    map f (clearedSubstitution den num e p) =
      clearedSubstitution (map f den) (fun i => map f (num i)) e (map f p) := by
  classical
  simp only [clearedSubstitution, map_sum, map_mul, map_pow, Finsupp.prod, map_prod, map_C,
    support_map_of_injective p f.injective, coeff_map]

/-- Every advice-field affine row numerator maps to the identical numerator over the
ambient constants. -/
theorem map_affineSlice (f : K →+* T) (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (row : MvPolynomial (Option (Fin m) ⊕ I) K) :
    map f (affineSlice Y k row) = affineSlice (fun i => map f (Y i)) k (map f row) := by
  have hd (j : Option (Fin m)) : map f (affineChartDen j) = affineChartDen j := by
    cases j <;> simp [affineChartDen]
  have hn (j) : map f (affineGraphNums Y k j) = affineGraphNums (fun i => map f (Y i)) k j := by
    cases j <;> simp [affineGraphNums, hd]
  rw [affineSlice, map_clearedSubstitution, hd, funext hn]
  rfl

/-- The actual polynomial equation in the affine parameters and the extra variable `t`. -/
noncomputable def affineEquation (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (D : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K) (v : Fin m → K) (i : Fin m) :
    MvPolynomial (Option (Fin m)) K :=
  rename some (affineSlice Y k (D i)) + X none * rename some (affineChartNum k i - C (v i) * affineChartDen k)

/-- The bivariate parameter system has total degree at most `d + 2` in the original
affine parameters and `t`, including on the chart boundary. -/
theorem affineEquation_degree (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (hY : ∀ i, (Y i).totalDegree ≤ d) (D : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K)
    (hD : ∀ i, (D i).totalDegree ≤ 1) (v : Fin m → K) (i : Fin m) :
    (affineEquation Y k D v i).totalDegree ≤ d+2 := by
  obtain ⟨hd, hn⟩ := affineChart_degrees (K := K) k
  have hrow := affineSlice_degree Y k (D i) hY (hD i)
  have hlin : (affineChartNum k i - C (v i) * affineChartDen k).totalDegree ≤ 1 := by
    apply (totalDegree_sub ..).trans (max_le (hn i) _)
    exact (totalDegree_mul ..).trans (by simpa using hd)
  apply (totalDegree_add ..).trans
  apply max_le
  · exact (totalDegree_rename_le ..).trans (hrow.trans (by omega))
  · exact (totalDegree_mul ..).trans (Nat.add_le_add (totalDegree_X none).le
      ((totalDegree_rename_le ..).trans hlin) |>.trans (by omega))

/-- Mapping the coefficient field of the full equation gives the equation built after
extending every table entry, slice and target. -/
theorem map_affineEquation (f : K →+* T) (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (D : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K) (v : Fin m → K) (i : Fin m) :
    map f (affineEquation Y k D v i) = affineEquation (fun i => map f (Y i)) k
      (fun j => map f (D j)) (f ∘ v) i := by
  have hd (j : Option (Fin m)) : map f (affineChartDen j) = affineChartDen j := by
    cases j <;> simp [affineChartDen]
  have hn (j) : map f (affineChartNum k j) = affineChartNum k j := hd (chartIndex k j)
  simp only [affineEquation, map_add, map_mul, map_X, map_rename, map_sub, map_C, map_affineSlice,
    Function.comp_apply, hd, hn]

/-- Replacing the distinguished polynomial variable by the generic field parameter
recovers the cleared row used to prove nonsingularity. -/
theorem specialize_affineEquation (f : K →+* T) (Y : I → MvPolynomial (Fin m) K) (k : Option (Fin m))
    (D : Fin m → MvPolynomial (Option (Fin m) ⊕ I) K) (v : Fin m → K) (i : Fin m) (t : T) :
    eval₂Hom (C.comp f) (fun o : Option (Fin m) => o.elim (C t) X) (affineEquation Y k D v i) =
      affineRow k t (fun j => map f (affineSlice Y k (D j))) (f ∘ v) i := by
  have ev (p : MvPolynomial (Fin m) K) :
      eval₂Hom (C.comp f) (fun o : Option (Fin m) => o.elim (C t) X) (rename some p) = map f p := by
    rw [coe_eval₂Hom, eval₂_rename]
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  have hd (j : Option (Fin m)) : map f (affineChartDen j) = affineChartDen j := by
    cases j <;> simp [affineChartDen]
  have hn (j) : map f (affineChartNum k j) = affineChartNum k j := hd (chartIndex k j)
  simp only [affineEquation, map_add, map_mul, ev, eval₂Hom_X', Option.elim_none, map_sub,
    map_C, affineRow, Function.comp_apply, hd, hn]
  ring

end Branch

end BorderVNP
end Computability
end OAI
