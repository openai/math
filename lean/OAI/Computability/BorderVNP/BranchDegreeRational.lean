import OAI.Computability.BorderVNP.BranchDegreeGraph
import OAI.Computability.VPVNP.PerronRelation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.FieldSimp

/-! # Bounded relations for rational parameter functions

In §9.2 the coordinates of the deformed map and its exceptional locus are rational
in the affine parameters with a common denominator. Adjoining one independent scale
makes their numerators and denominator a polynomial cone. Perron's degree bound for
this cone descends to the rational functions by choosing a nonzero scalar slice on
which the relation is still a nonzero polynomial.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP.RadicalCertificate

variable {K L : Type*} [Field K] [Infinite K] [Field L] [Algebra K L] {m d : ℕ}

/-- A rational parametrization in `m` variables with `m+1` output coordinates satisfies
a nonzero relation of singly exponential degree. The parameters may be evaluated in any
extension field where the common denominator is nonzero. -/
theorem rational_perron_relation (x : Fin m → L) (g : Fin (m+1) → L)
    (den : MvPolynomial (Fin m) K) (num : Fin (m+1) → MvPolynomial (Fin m) K)
    (hden : aeval x den ≠ 0) (hd : den.totalDegree ≤ d) (hn : ∀ i, (num i).totalDegree ≤ d)
    (hfrac : ∀ i, g i * aeval x den = aeval x (num i)) :
    ∃ P : MvPolynomial (Fin (m+1)) K, P ≠ 0 ∧
      P.totalDegree ≤ perronSimplexBound (m+1) (d+1) ∧ aeval g P = 0 := by
  classical
  let scale (p : MvPolynomial (Fin m) K) : MvPolynomial (Fin (m+1)) K :=
    X 0 * rename Fin.succ p
  let cone : Fin ((m+1)+1) → MvPolynomial (Fin (m+1)) K := Fin.cons (scale den) (scale ∘ num)
  have hdeg (p : MvPolynomial (Fin m) K) (hp : p.totalDegree ≤ d) : (scale p).totalDegree ≤ d+1 := by
    apply (totalDegree_mul ..).trans
    rw [totalDegree_X, Nat.add_comm]
    exact Nat.add_le_add_right ((totalDegree_rename_le Fin.succ p).trans hp) 1
  obtain ⟨W, hW, hWd, hWzero⟩ := perron_relation cone
    (fun i => Fin.cases (hdeg den hd) (fun j => hdeg (num j) (hn j)) i)
  have hpoint : ∃ y : Fin ((m+1)+1) → K, eval y (W * X 0) ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hW (X_ne_zero 0) (MvPolynomial.funext fun y => by simpa using h y)
  obtain ⟨y, hy⟩ := hpoint
  rw [map_mul, eval_X, mul_ne_zero_iff] at hy
  let k := y 0
  let slice : Fin ((m+1)+1) → MvPolynomial (Fin (m+1)) K :=
    Fin.cons (C k) (fun i => C k * X i)
  let P := aeval slice W
  have hval : aeval (fun i : Fin (m+1) => y i.succ / k) P = eval y W := by
    let ev := aeval (R := K) (fun i : Fin (m+1) => y i.succ / k)
    have he : (fun i => ev (slice i)) = y := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [ev, slice, k]
      · simp [ev, slice, k, mul_comm (y 0), hy.2]
    change ev (aeval slice W) = _
    rw [← AlgHom.comp_apply, comp_aeval, he, aeval_eq_eval]
  have hP : P ≠ 0 := by
    intro h
    exact hy.1 (by rwa [h, map_zero, eq_comm] at hval)
  have hPd : P.totalDegree ≤ W.totalDegree := by
    have hs (i) : (slice i).totalDegree ≤ 1 := by
      refine Fin.cases (by simp [slice]) (fun j => ?_) i
      exact (totalDegree_mul ..).trans (by simp)
    simpa using substitute_degree slice hs W
  let k' := algebraMap K L k
  let arg : Fin (m+1) → L := Fin.cons (k' / aeval x den) x
  have hscale (p : MvPolynomial (Fin m) K) :
      aeval arg (scale p) = k' / aeval x den * aeval x p := by
    simp only [scale, map_mul, aeval_X, aeval_rename]
    rfl
  have hs (i : Fin ((m+1)+1)) : aeval g (slice i) = aeval arg (cone i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [slice, cone, hscale, k', hden]
    · simp only [slice, cone, Fin.cons_succ, map_mul, aeval_C, aeval_X, Function.comp_apply,
        hscale, ← hfrac]
      field_simp [hden]
      exact mul_comm _ _
  refine ⟨P, hP, hPd.trans hWd, ?_⟩
  change aeval g (aeval slice W) = 0
  rw [← AlgHom.comp_apply, comp_aeval, funext hs, ← comp_aeval, AlgHom.comp_apply, hWzero, map_zero]

end Branch

end BorderVNP
end Computability
end OAI
