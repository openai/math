import OAI.Computability.BorderVNP.BranchParseFamily
import OAI.Computability.BorderVNP.ResidueDiagonalRow
import OAI.Computability.BorderVNP.ResidueOutputAtPlace

/-!
# The signed row on the numbered coefficient table

The geometric branch is constructed for a table on `2n` variables, with
every grammar label numbered. Reindexing the paired signed polynomial and
the requested monomials gives the signed live contraction over precisely
that table. The row degree is bounded before evaluation at any branch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Residue ResiduePins Module Matrix MvPolynomial
open scoped BigOperators Matrix Classical

variable {Pin Wire Proc : Type*} [Fintype Wire] [Fintype Proc]

/-- The full degree monomial obtained by numbering the paired input variables. -/
noncomputable def numberedMonomial {n : ℕ} (e : Fin n × Bool ≃ Fin (2*n))
    (d : DegreeMonomial (Fin n × Bool) n) : DegreeMonomial (Fin (2*n)) n :=
  ⟨d.val.mapDomain e, (Finsupp.degree_mapDomain _ _).trans d.property⟩

/-- Numbering both the queried degree monomial and the signed polynomial preserves
the coefficient value at every physical query. -/
theorem numbered_live_eq_eval {n : ℕ} {K : Type*} [CommRing K] (e : Fin n × Bool ≃ Fin (2*n))
    (layout : Proc → Fin n → InputSlot Pin Wire) (pins : Pin → Bool) :
    (signedContraction layout pins : K) =
      eval (coeffVector n (map (Int.castRingHom K) (rename e (Pstar n))))
        (queryPolynomial K (fun l r => numberedMonomial e (pairedQuery layout pins l r))) := by
  rw [live_eq_eval, eval_queryPolynomial, eval_queryPolynomial, map_rename]
  congr 1
  funext l
  apply Finset.prod_congr rfl
  intro r _
  exact (coeff_rename_mapDomain e e.injective _ _).symm

/-- The polynomial in the numbered parameters used by a substituted row. -/
noncomputable def numberedSubstituted (E : Type*) [Field E] (k s : ℕ)
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (layout : Proc → Fin (k+1) → InputSlot Pin Wire)
    (pins : Pin → Bool) : MvPolynomial (Fin (parameterCount (2*(k+1)) k s)) E :=
  ∑ links, ∏ proc, numberedTable E _ k s (numberedMonomial e (pairedQuery layout pins links proc))

/-- The degree budget of the substituted row comes from one bounded-degree table
coordinate per live processor, independently of the number of shared wire assignments. -/
theorem numberedSubstituted_degree (E : Type*) [Field E] (k s : ℕ)
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (layout : Proc → Fin (k+1) → InputSlot Pin Wire)
    (pins : Pin → Bool) : (numberedSubstituted E k s e layout pins).totalDegree ≤
      Fintype.card Proc * (2*k+1) := by
  apply totalDegree_finsetSum_le
  intro links _
  refine (totalDegree_finsetProd _ _).trans ?_
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun proc _ => numberedTable_degree E _ k s (numberedMonomial e (pairedQuery layout pins links proc)))

variable {β ι E κ : Type*} [Field E] [Field κ] [Fintype β] [Fintype ι]

/-- The exact pin row evaluated on the numbered system whose closure is used in §9. -/
theorem numbered_signed_pinRow (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) E]
    [Algebra (ZMod p) κ] (k s : ℕ) (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (φ : E →+* LaurentSeries κ) (v : Fin (parameterCount (2*(k+1)) k s) → LaurentSeries κ)
    (B : Basis β (ZMod p) E) (H L q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option (Fin (parameterCount (2*(k+1)) k s))) E)
    (Ω : Index β (Fin (parameterCount (2*(k+1)) k s)) H → ZMod p)
    (hpin : ∀ A : MvPolynomial (Fin (parameterCount (2*(k+1)) k s)) E, A.totalDegree ≤ L →
      ∀ z : ZMod p, 0 ≤ (eval₂ φ v A).order →
      (eval₂ φ v A).coeff 0 = algebraMap (ZMod p) κ z →
      (∑ μ ∈ A.support, weights B H q hq g (.id E) (Residue.mixedIndex (polynomialIndex μ))
        (A.coeff μ)) *ᵥ Ω = z • Ω)
    (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool)
    (hL : Fintype.card Proc * (2*k+1) ≤ L)
    (hy : ∀ a, 0 ≤ (eval₂Hom φ v (numberedTable E _ k s a)).order)
    (hc : ∀ a, (eval₂Hom φ v (numberedTable E _ k s a)).coeff 0 =
      algebraMap (ZMod p) κ (coeffVector (k+1)
        (map (Int.castRingHom (ZMod p)) (rename e (Pstar (k+1)))) a))
    (i : Index β (Fin (parameterCount (2*(k+1)) k s)) H) :
    ∑ h, pinEntry (entryWeight p B H q hq g) i h (numberedSubstituted E k s e layout pins) * Ω h =
      (signedContraction layout pins : ZMod p) * Ω i := by
  let c := coeffVector (k+1) (map (Int.castRingHom (ZMod p)) (rename e (Pstar (k+1))))
  let Q := queryPolynomial (ZMod p) (fun l r => numberedMonomial e (pairedQuery layout pins l r))
  have hA := substituted_output_specializes p (algebraMap (ZMod p) κ) φ (algebraMap (ZMod p) E)
    v (numberedTable E _ k s) c hy hc Q
  have hs : eval₂Hom (C.comp (algebraMap (ZMod p) E)) (numberedTable E _ k s) Q =
      numberedSubstituted E k s e layout pins := substitute_queryPolynomial _ _ _
  dsimp only at hA
  rw [hs, show eval c Q = (signedContraction layout pins : ZMod p) from
    (numbered_live_eq_eval ..).symm] at hA
  exact pinRow_of_action p B H q hq g Ω _ _ i (hpin _
    ((numberedSubstituted_degree E k s e layout pins).trans hL) _ hA.1 hA.2)

end Diagonal

end BorderVNP
end Computability
end OAI
