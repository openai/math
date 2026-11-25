import OAI.Computability.BorderVNP.ModelSubstitute
import OAI.Computability.BorderVNP.HittingSetHybrid
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Lagrange

/-! # Hasse coefficient extraction on circuits

Interpolation in one scalar variable bounds the circuit size of a Hasse
derivative without dividing by a factorial. This works in every characteristic
over the infinite ambient field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace HittingSet

open MvPolynomial VPVNP
open scoped Classical

variable {K σ : Type*} [Field K]

/-- Summing finitely many circuit outputs costs at most one addition per summand. -/
theorem circuitSize_finsetSum_le {ι : Type*} (S : Finset ι) (f : ι → MvPolynomial σ K)
    (T : ℕ) (h : ∀ i ∈ S, circuitSize (f i) ≤ T) :
    circuitSize (∑ i ∈ S, f i) ≤ S.card * (T+1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (circuitSize_C (σ := σ) (0 : K)).le
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul]
    exact (circuitSize_binOp_le .add (f i) _).trans (by
      have h1 := h i (Finset.mem_insert_self ..)
      have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      omega)

/-- The designated free variable `none` is shifted by a field scalar. -/
noncomputable def shiftZ (a : K) (p : MvPolynomial (Option σ) K) : MvPolynomial (Option σ) K :=
  aeval (fun j => j.elim (X none + C a) (fun i => X (some i))) p

/-- A single additional shared gate implements the scalar shift in the distinguished variable. -/
theorem circuitSize_shiftZ (a : K) (p : MvPolynomial (Option σ) K) :
    circuitSize (shiftZ a p) ≤ 1 + circuitSize p := by
  let P : Program K (Option σ) 1 := Program.snoc .nil .add (.var none) (.const a)
  let r : Option σ → Ref K (Option σ) 1 := fun j => j.elim (.gate 0) (fun i => .var (some i))
  have hr : (fun j => (⟨P, r j⟩ : Circuit K (Option σ) 1).polynomial) =
      fun j => j.elim (X none + C a) (fun i => X (some i)) := by
    funext j
    cases j <;> rfl
  simpa only [shiftZ, hr] using circuitSize_aeval_shared P r p

private theorem eval_shiftZ (a z : K) (y : σ → K) (p : MvPolynomial (Option σ) K) :
    eval (fun j => j.elim z y) (shiftZ a p) = eval (fun j => j.elim (z+a) y) p := by
  rw [shiftZ, eval_substitute]
  congr 2
  funext j
  cases j <;> simp

/-- A Hasse derivative of a polynomial of individual degree below the number of nodes is
a fixed scalar linear combination of translates, including in positive characteristic. -/
theorem hasse_eq_sum_shiftZ [Infinite K] (S : Finset K) (k : ℕ)
    (B : Polynomial (MvPolynomial σ K)) (hdeg : B.natDegree < S.card) :
    (optionEquivLeft K σ).symm (B.hasseDeriv k) =
      ∑ a ∈ S, shiftZ a ((optionEquivLeft K σ).symm B) *
        C ((Lagrange.basis S id a).coeff k) := by
  classical
  apply MvPolynomial.funext
  intro x
  let y : σ → K := x ∘ some
  let z := x none
  have hx : x = fun j => j.elim z y := by funext j; cases j <;> rfl
  rw [hx, optionEquivLeft_elim_eval, AlgEquiv.apply_symm_apply, ← Polynomial.hasseDeriv_map,
    ← Polynomial.taylor_coeff]
  let T := Polynomial.taylor z (B.map (eval y))
  have hd : T.degree < S.card := by
    refine T.degree_le_natDegree.trans_lt ?_
    exact_mod_cast ((Polynomial.natDegree_taylor ..).trans_le (Polynomial.natDegree_map_le ..)).trans_lt hdeg
  have hI := Lagrange.eq_interpolate (v := id) (s := S) Function.injective_id.injOn hd
  change T.coeff k = _
  conv_lhs => rw [hI, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  simp only [map_sum, map_mul, eval_C, Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [eval_shiftZ, optionEquivLeft_elim_eval, AlgEquiv.apply_symm_apply]
  simp [T, Polynomial.taylor_apply, Polynomial.eval_comp, add_comm]

/-- With `D+1` scalar nodes and a size-`m` input, extraction costs at most
`(D+1)*(m+3)` binary gates, independently of the characteristic or derivative order. -/
theorem circuitSize_hasse_le [Infinite K] (D k : ℕ) (B : Polynomial (MvPolynomial σ K))
    (hD : B.natDegree ≤ D) :
    circuitSize ((optionEquivLeft K σ).symm (B.hasseDeriv k)) ≤
      (D+1) * (circuitSize ((optionEquivLeft K σ).symm B) + 3) := by
  classical
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq K (D+1)
  rw [hasse_eq_sum_shiftZ S k B (by omega)]
  let m := circuitSize ((optionEquivLeft K σ).symm B)
  refine (circuitSize_finsetSum_le S _ (m+2) ?_).trans_eq ?_
  · intro a _
    apply (circuitSize_binOp_le .mul ..).trans
    simp only [circuitSize_C, add_zero]
    have h := circuitSize_shiftZ a ((optionEquivLeft K σ).symm B)
    omega
  · rw [hS]

end HittingSet

end BorderVNP
end Computability
end OAI
