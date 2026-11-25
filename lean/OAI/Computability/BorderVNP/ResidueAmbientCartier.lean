import OAI.Computability.BorderVNP.ResidueBox
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.Ring

/-!
# Cartier on the Laurent polynomial parameter space

The ambient coefficient extractor of §10.1 is additive and moves a Frobenius power out
of a product. Composing extractions adds their iteration counts. These identities apply
before restriction to the curve and retain the signed exponent of the parameter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open ResidueBox
open scoped Classical

variable {K σ : Type*} [Field K] (p u : ℕ) [ExpChar K p] [PerfectRing K p]

/-- The ambient `Λ_q` of (10.2) for `q = p^u`. -/
noncomputable def ambientCartier (f : Laurent σ K) : Laurent σ K :=
  extract (p ^ u) (expChar_pow_pos K p u) (iterateFrobeniusEquiv K p u).symm.toRingHom f

/-- The output coefficient is the inverse Frobenius of the coefficient at the shifted index. -/
theorem ambientCartier_coeff (f : Laurent σ K) (d : Exponent σ) :
    (ambientCartier p u f).coeff d =
    (iterateFrobeniusEquiv K p u).symm (f.coeff (sourceIndex (p ^ u) d)) := rfl

/-- Extraction respects addition, including cancellation of Laurent monomials. -/
theorem ambientCartier_add (f g : Laurent σ K) :
    ambientCartier p u (f + g) = ambientCartier p u f + ambientCartier p u g := by
  ext d
  simp only [ambientCartier_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]

/-- Extracting from zero returns zero. -/
theorem ambientCartier_zero : ambientCartier p u (0 : Laurent σ K) = 0 := by
  ext d
  simp only [ambientCartier_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]

/-- Two successive ambient extractions give the extraction at the product of their powers. -/
theorem ambientCartier_comp (v : ℕ) (f : Laurent σ K) :
    ambientCartier p u (ambientCartier p v f) = ambientCartier p (u + v) f := by
  ext d
  simp only [ambientCartier_coeff, iterateFrobeniusEquiv_symm_add_apply]
  congr 3
  funext i
  simp only [sourceIndex, pow_add, Nat.cast_mul]
  ring

private theorem sourceIndex_sub (q : ℕ) (d e : Exponent σ) :
    sourceIndex q (-e + d) = -(q • e) + sourceIndex q d := by
  funext i
  change (q : ℤ) * (-e i + d i) + q - 1 = -(q • e i) + ((q : ℤ) * d i + q - 1)
  rw [nsmul_eq_mul]
  ring

/-- A `q`-th power can be pulled through the ambient Cartier operator. -/
theorem ambientCartier_pow_mul (D f : Laurent σ K) :
    ambientCartier p u (D ^ p ^ u * f) = D * ambientCartier p u f := by
  let : ExpChar (Laurent σ K) p := expChar_of_injective_ringHom
    (f := AddMonoidAlgebra.singleZeroRingHom) (RingHom.injective _) p
  induction D using AddMonoidAlgebra.induction_linear with
  | zero => simp [zero_pow (expChar_pow_pos K p u).ne', ambientCartier_zero]
  | add D G hD hG => rw [add_pow_expChar_pow, add_mul, ambientCartier_add, hD, hG, add_mul]
  | single e b =>
    ext d
    rw [ambientCartier_coeff, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.coeff_single_mul_apply,
      AddMonoidAlgebra.coeff_single_mul_apply, ambientCartier_coeff, sourceIndex_sub, map_mul]
    exact congrArg (· * _) ((iterateFrobeniusEquiv K p u).symm_apply_apply b)

/-- On a monomial with exponents between `0` and `q−1`, the extractor reads just the
top corner of the box. -/
theorem ambientCartier_reduced_single (r : Option σ → ℕ) (hr : ∀ i, r i < p ^ u) :
    ambientCartier p u (AddMonoidAlgebra.single (fun i => (r i : ℤ)) (1 : K)) =
      if r = (fun _ => p ^ u - 1) then 1 else 0 := by
  classical
  let q := p ^ u
  have hq := expChar_pow_pos K p u
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hit (d : Exponent σ) :
      (fun i => (r i : ℤ)) = sourceIndex q d ↔ r = (fun _ => q - 1) ∧ d = 0 := by
    constructor
    · intro h
      have hd (i : Option σ) : d i = 0 := by
        have h' := congrFun h i
        change (r i : ℤ) = (q : ℤ) * d i + q - 1 at h'
        have hupper : (r i : ℤ) < q := by exact_mod_cast hr i
        rcases lt_trichotomy (d i) 0 with hh | hh | hh
        · have := mul_le_mul_of_nonneg_left (show d i ≤ -1 by omega) hq'.le
          linarith [Int.natCast_nonneg (r i)]
        · exact hh
        · have := mul_le_mul_of_nonneg_left (show 1 ≤ d i by omega) hq'.le
          linarith
      refine ⟨?_, funext hd⟩
      funext i
      have h' := congrFun h i
      change (r i : ℤ) = (q : ℤ) * d i + q - 1 at h'
      rw [hd, mul_zero, zero_add] at h'
      omega
    · rintro ⟨rfl, rfl⟩
      funext i
      change ((q - 1 : ℕ) : ℤ) = (q : ℤ) * 0 + q - 1
      rw [Nat.cast_sub (by omega), Nat.cast_one, mul_zero, zero_add]
  ext d
  rw [ambientCartier_coeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  change (iterateFrobeniusEquiv K p u).symm (if _ = sourceIndex q d then 1 else 0) =
    (if r = (fun _ => q - 1) then (1 : Laurent σ K) else 0).coeff d
  rw [hit d]
  by_cases ht : r = (fun _ => q - 1)
  · by_cases hd : d = 0
    · simp [ht, hd]
    · simp [ht, hd, AddMonoidAlgebra.one_def]
  · simp [ht]

end Residue

end BorderVNP
end Computability
end OAI
