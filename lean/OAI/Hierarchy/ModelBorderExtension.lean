import OAI.Hierarchy.BorderExtension
import OAI.Hierarchy.ModelBorder
import OAI.Hierarchy.FormulaParameters
import OAI.Hierarchy.ABPParameters
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod

namespace OAI
/-! # Scalar extension preserves formula and branching-program border bounds -/

namespace Hierarchy

open MvPolynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {σ : Type} (d s : ℕ) (p : MvPolynomial σ F)

/-- The degree-component border formula bound is unchanged under a field extension. -/
theorem formulaDegreeBorder_map_iff :
    DegreeBorderAtMost HasFormula d s (map (algebraMap F E) p) ↔ DegreeBorderAtMost HasFormula d s p := by
  apply degreeBorderAtMost_map_iff_of_closure
  intro _ g
  exact degreeModelClosure_map_iff (fun _ h => hasFormula_map _ h)
    (fun _ h => formula_parameters h) g

/-- The degree-component border branching-program bound is unchanged under a field extension. -/
theorem abpDegreeBorder_map_iff [Fintype σ] :
    DegreeBorderAtMost HasABP d s (map (algebraMap F E) p) ↔ DegreeBorderAtMost HasABP d s p := by
  apply degreeBorderAtMost_map_iff_of_closure
  intro _ g
  exact degreeModelClosure_map_iff (fun _ h => hasABP_map _ h)
    (fun _ h => abp_parameters h) g

section Characteristic

variable {K L : Type*} [Field K] [Field L] (q : ℕ) [CharP K q] [CharP L q] (f : MvPolynomial σ ℤ)

include q in
private theorem viaPrimeField {P : Prop}
    (h : ∀ (k : Type) [Field k] [Algebra k K] [Algebra k L], P) : P := by
  rcases CharP.char_is_prime_or_zero K q with hp | rfl
  · let : Fact q.Prime := ⟨hp⟩
    let := ZMod.algebra K q
    let := ZMod.algebra L q
    exact h (ZMod q)
  · let := CharP.charP_to_charZero K
    let := CharP.charP_to_charZero L
    exact h ℚ

include q in
/-- An integer polynomial has the same degree-component border formula bound over
all fields of a fixed characteristic. -/
theorem formulaDegreeBorder_intCast_iff :
    DegreeBorderAtMost HasFormula d s (map (Int.castRingHom K) f) ↔
      DegreeBorderAtMost HasFormula d s (map (Int.castRingHom L) f) := by
  apply viaPrimeField (K := K) (L := L) q
  intro k _ _ _
  have hK : (algebraMap k K).comp (Int.castRingHom k) = Int.castRingHom K := Subsingleton.elim ..
  have hL : (algebraMap k L).comp (Int.castRingHom k) = Int.castRingHom L := Subsingleton.elim ..
  simpa only [map_map, hK, hL] using
    (formulaDegreeBorder_map_iff (E := K) d s (map (Int.castRingHom k) f)).trans
      (formulaDegreeBorder_map_iff (E := L) d s (map (Int.castRingHom k) f)).symm

include q in
/-- An integer polynomial has the same degree-component border branching-program bound
over all fields of a fixed characteristic. -/
theorem abpDegreeBorder_intCast_iff [Fintype σ] :
    DegreeBorderAtMost HasABP d s (map (Int.castRingHom K) f) ↔
      DegreeBorderAtMost HasABP d s (map (Int.castRingHom L) f) := by
  apply viaPrimeField (K := K) (L := L) q
  intro k _ _ _
  have hK : (algebraMap k K).comp (Int.castRingHom k) = Int.castRingHom K := Subsingleton.elim ..
  have hL : (algebraMap k L).comp (Int.castRingHom k) = Int.castRingHom L := Subsingleton.elim ..
  simpa only [map_map, hK, hL] using
    (abpDegreeBorder_map_iff (E := K) d s (map (Int.castRingHom k) f)).trans
      (abpDegreeBorder_map_iff (E := L) d s (map (Int.castRingHom k) f)).symm

end Characteristic

end Hierarchy

end OAI
