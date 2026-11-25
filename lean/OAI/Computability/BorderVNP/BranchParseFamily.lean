import OAI.Computability.BorderVNP.BranchFiniteCuts
import OAI.Computability.BorderVNP.BranchSpecializationParse

/-!
# The actual degree-component coefficient table for the branch construction

The graph chart uses a finite numbering of the grammar labels. Its output coordinates
remain the entire degree component, including nonsquarefree monomials. The weighted
equations use the exponents in base `n+1` specified in Section 9.2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial VPVNP ParseTable BranchSpecialization

/-- Label dimension of the universal table on `v` variables and degree `k+1`. -/
abbrev parameterCount (v k s : ℕ) : ℕ :=
  Fintype.card (GrammarLabel (Fin v) (State (Fin v) s) (k+1))

/-- Actual coefficient map over any specified field, with the grammar labels numbered. -/
noncomputable def numberedTable (K : Type*) [Field K] (v k s : ℕ)
    (ν : DegreeMonomial (Fin v) (k+1)) : MvPolynomial (Fin (parameterCount v k s)) K :=
  rename (Fintype.equivFin _) (map (Int.castRingHom K) (table (Fin v) k s ν))

/-- Numbering the parameters and casting the coefficients preserves the parse-degree bound. -/
theorem numberedTable_degree (K : Type*) [Field K] (v k s : ℕ) (ν : DegreeMonomial (Fin v) (k+1)) :
    (numberedTable K v k s ν).totalDegree ≤ 2*k+1 :=
  (totalDegree_rename_le ..).trans ((Finset.sup_mono (support_map_subset _ _)).trans (table_degree_le _ _ _ _))

/-- A nonempty variable set supplies a terminal label and a nonempty parameter chart. -/
theorem parameterCount_pos {v : ℕ} (hv : 0 < v) (k s : ℕ) : 0 < parameterCount v k s := by
  let : Nonempty (GrammarLabel (Fin v) (State (Fin v) s) (k+1)) := ⟨Sum.inl (0,⟨0,hv⟩)⟩
  exact Fintype.card_pos

/-- The genuine digit exponents distinguish the entire degree component. -/
theorem degreeMonomial_digits (v k : ℕ) :
    Function.Injective (fun ν : DegreeMonomial (Fin v) (k+1) => digitExponent (k+2) ν.val) ∧
      ∀ ν : DegreeMonomial (Fin v) (k+1), digitExponent (k+2) ν.val < (k+2)^v := by
  have hd (ν : DegreeMonomial (Fin v) (k+1)) (j) : ν.val j < k+2 :=
    (Finsupp.le_degree j ν.val).trans_lt (by rw [ν.property]; omega)
  refine ⟨fun p q hp => Subtype.ext (DFunLike.ext' (digitExponent_inj (by omega) (hd p) (hd q) hp)),
    fun p => digitExponent_lt (by omega) (hd p)⟩

/-- Renaming the label parameters by their enumeration preserves the actual image set. -/
theorem numberedTable_image (K : Type*) [Field K] (v k s : ℕ) :
    polynomialImage (numberedTable K v k s) =
      polynomialImage (fun i => map (Int.castRingHom K) (table (Fin v) k s i)) :=
  polynomialImage_rename (Fintype.equivFin _) _

/-- The field change of the numbered table is the coefficientwise extension of the table. -/
theorem numberedTable_map {E K : Type*} [Field E] [Field K] (i : E →+* K) (v k s : ℕ)
    (ν : DegreeMonomial (Fin v) (k+1)) :
    map i (numberedTable E v k s ν) = numberedTable K v k s ν := by
  rw [numberedTable, numberedTable, map_rename, map_map]
  exact congrArg (rename _) (congrArg (fun f : ℤ →+* K => map f (table (Fin v) k s ν))
    (Subsingleton.elim ..))

/-- The §9 input for every integral polynomial supplied by a genuine degree-component
border approximation, over the algebraic closure of the original field. -/
theorem numbered_table_closure_of_borderApprox {F : Type*} [Field F] (v k s : ℕ)
    (p : MvPolynomial (Fin v) ℤ)
    (hp : BorderApprox (k+1) s (map (Int.castRingHom F) p)) :
    Int.castRingHom (AlgebraicClosure F) ∘ coeffVector (k+1) p ∈ imageClosure
      (polynomialImage (numberedTable (AlgebraicClosure F) v k s)) := by
  rw [numberedTable_image]
  exact tableClosure_of_borderApprox_int p k s hp

end Branch

end BorderVNP
end Computability
end OAI
