import OAI.Computability.VPVNP.ComplexityLib.Bounds
import OAI.Computability.VPVNP.ComplexityLib.Circuit
import OAI.Computability.VPVNP.ComplexityLib.Renaming
import OAI.Computability.VPVNP.ComplexityLib.Witness
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Finite variable families in the two models

Numbering the variables preserves the polynomial, its degree, and its minimum
project circuit size. For a VNP verifier, number the visible variables first,
then the witness variables, as required by complexitylib's Boolean sum.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

open Cslib.Circuits.Arithmetic

variable {K : Type*} [Field K] {X : ℕ → Type} [∀ n, Fintype (X n)] {a : ℕ → ℕ}

/-- The upstream polynomial family obtained by numbering the variables at each length. -/
noncomputable def numberedFamily (p : Family K X) (e : ∀ n, X n ≃ Fin (a n)) :
    PolynomialFamily K where
  vars := a
  poly n := MvPolynomial.rename (e n) (p n)

private theorem numbered_isPFamily_iff (p : Family K X) (e : ∀ n, X n ≃ Fin (a n)) :
    (numberedFamily p e).IsPFamily ↔ PFamily p := by
  have ha : a = fun n => Fintype.card (X n) := by
    funext n
    simpa using (Fintype.card_congr (e n)).symm
  have hd : (fun n => ((numberedFamily p e).poly n).totalDegree) =
      (fun n => (p n).totalDegree) := by
    funext n
    exact MvPolynomial.totalDegree_renameEquiv (e n) (p n)
  unfold PolynomialFamily.IsPFamily PFamily
  change (Cslib.PolynomiallyBounded a ∧ Cslib.PolynomiallyBounded _) ↔ _
  simp only [hd, ← polynomiallyBounded_iff, ha]

/-- A family has polynomial-size circuits in one model precisely when its
numbered family has polynomial-size circuits in the other. -/
theorem numbered_mem_VP_iff (p : Family K X) (e : ∀ n, X n ≃ Fin (a n)) :
    numberedFamily p e ∈ VP K ↔ IsVP p := by
  constructor
  · rintro ⟨hf, c, hc, hpoly⟩
    refine ⟨(numbered_isPFamily_iff p e).mp hf, (polynomiallyBounded_iff _).mpr ?_⟩
    refine hc.mono_of_le fun n => ?_
    rw [← circuitSize_renameEquiv (e n) (p n)]
    change circuitSize ((numberedFamily p e).poly n) ≤ _
    rw [← hpoly n]
    exact circuitSize_le_upstream (c n) 0
  · rintro ⟨hf, hsize⟩
    choose c hpoly hc using fun n => exists_upstream_circuit ((numberedFamily p e).poly n)
    refine ⟨(numbered_isPFamily_iff p e).mpr hf, c, ?_, hpoly⟩
    have hs := (polynomiallyBounded_iff _).mp hsize
    refine (((Cslib.PolynomiallyBounded.const 5).mul hs).add
      (Cslib.PolynomiallyBounded.const 1)).mono_of_le fun n => ?_
    simpa only [numberedFamily, circuitSize_renameEquiv] using hc n

/-- A project VNP verifier gives an upstream VNP verifier with the same Boolean
witness length and the same formal polynomial at each index. -/
theorem numbered_mem_VNP (p : Family K X) (e : ∀ n, X n ≃ Fin (a n)) (hp : IsVNP p) :
    numberedFamily p e ∈ VNP K := by
  classical
  obtain ⟨_, W, iW, g, _, hVP, hsum⟩ := hp
  let : ∀ n, Fintype (W n) := iW
  let m := fun n => Fintype.card (W n)
  let w : ∀ n, W n ≃ Fin (m n) := fun n => Fintype.equivFin _
  let combined := fun n => sumVariables (e n) (w n)
  refine ⟨m, fun n => MvPolynomial.rename (combined n) (g n),
    (numbered_mem_VP_iff g combined).mpr hVP, fun n => ?_⟩
  change MvPolynomial.rename (e n) (p n) = _
  rw [hsum n]
  exact (booleanSum_rename (e n) (w n) (g n)).symm

end ComplexityLib

end VPVNP
end Computability
end OAI
