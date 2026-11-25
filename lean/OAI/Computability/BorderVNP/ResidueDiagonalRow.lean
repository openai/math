import OAI.Computability.BorderVNP.ResidueOutputSpecialization
import OAI.Computability.BorderVNP.ResiduePinsPolynomial
import OAI.Computability.BorderVNP.DiagonalEntry
import OAI.Computability.BorderVNP.DiagonalSubstitution

/-!
# The row equation of the boundary diagonal

Each substituted signed contraction is a polynomial in the *regular outputs*
of the chart. Applying the branch pin to its monomials produces the row
equation with the actual signed live value. The residue is taken only after
the complete contraction has been formed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Residue ResiduePins Module Matrix MvPolynomial
open scoped BigOperators Matrix

variable {σ ι β E κ : Type*} [Field E] [Field κ] [Fintype σ] [Fintype β] [Fintype ι]
  (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) κ]

/-- A matrix equality from the residue construction gives the scalar equation
on any substituted row, in terms of the entry evaluator on that row. -/
theorem pinRow_of_action (B : Basis β (ZMod p) E) (H q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (Ω : Index β σ H → ZMod p)
    (A : MvPolynomial σ E) (z : ZMod p) (i : Index β σ H)
    (ha : (∑ μ ∈ A.support, weights B H q hq g (.id E)
      (Residue.mixedIndex (polynomialIndex μ)) (A.coeff μ)) *ᵥ Ω = z • Ω) :
    ∑ h, pinEntry (entryWeight p B H q hq g) i h A * Ω h = z * Ω i := by
  have he := congrFun ha i
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Pi.smul_apply,
    smul_eq_mul] at he
  have hμ : parameterShift = (fun μ : σ →₀ ℕ => Residue.mixedIndex (polynomialIndex μ)) := by
    funext μ i
    cases i <;> rfl
  simpa only [pinEntry_eq_support_sum, entryWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    hμ] using he

/-- Parameters of the full parse table for the paired signed family. -/
abbrev PairedParameters (k s : ℕ) :=
  VPVNP.GrammarLabel (Fin (k+1) × Bool) (ParseTable.State (Fin (k+1) × Bool) s) (k+1)

/-- Applying Lemma 10.1 to the actual polynomial of (11.1) gives the row tested
against the signed live contraction. The same chart and pin may be used for every
choice of layout and literal/pin bits. -/
theorem signed_pinRow {Pin Wire Proc : Type*} [Fintype Wire] [Fintype Proc] (k s : ℕ)
    (φ : E →+* LaurentSeries κ) (v : PairedParameters k s → LaurentSeries κ)
    (B : Basis β (ZMod p) E) (H L q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option (PairedParameters k s)) E)
    (Ω : Index β (PairedParameters k s) H → ZMod p)
    (hpin : ∀ A : MvPolynomial (PairedParameters k s) E, A.totalDegree ≤ L →
      ∀ z : ZMod p, 0 ≤ (eval₂ φ v A).order →
      (eval₂ φ v A).coeff 0 = algebraMap (ZMod p) κ z →
      (∑ μ ∈ A.support, weights B H q hq g (.id E) (Residue.mixedIndex (polynomialIndex μ))
        (A.coeff μ)) *ᵥ Ω = z • Ω)
    (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool)
    (hL : (substituted E k s layout pins).totalDegree ≤ L)
    (hy : ∀ e, 0 ≤ (eval₂ (Int.castRingHom (LaurentSeries κ)) v (ParseTable.table _ k s e)).order)
    (hc : ∀ e, (eval₂ (Int.castRingHom (LaurentSeries κ)) v (ParseTable.table _ k s e)).coeff 0 =
      algebraMap (ZMod p) κ (coeffVector (k+1) (map (Int.castRingHom (ZMod p)) (Pstar (k+1))) e))
    (i : Index β (PairedParameters k s) H) :
    ∑ h, pinEntry (entryWeight p B H q hq g) i h (substituted E k s layout pins) * Ω h =
      (signedContraction layout pins : ZMod p) * Ω i := by
  let Y (e : DegreeMonomial (Fin (k+1) × Bool) (k+1)) :=
    map (Int.castRingHom E) (ParseTable.table _ k s e)
  let c := coeffVector (k+1) (map (Int.castRingHom (ZMod p)) (Pstar (k+1)))
  let Q := queryPolynomial (ZMod p) (pairedQuery layout pins)
  have hY (e) : eval₂Hom φ v (Y e) = eval₂ (Int.castRingHom (LaurentSeries κ)) v
      (ParseTable.table _ k s e) := by
    change eval₂ φ v (map _ _) = _
    rw [eval₂_map, Subsingleton.elim (φ.comp (Int.castRingHom E)) (Int.castRingHom (LaurentSeries κ))]
  have hA := substituted_output_specializes p (algebraMap (ZMod p) κ) φ (algebraMap (ZMod p) E)
    v Y c (fun e => (hY e).symm ▸ hy e) (fun e => (hY e).symm ▸ hc e) Q
  have hs : eval₂Hom (C.comp (algebraMap (ZMod p) E)) Y Q = substituted E k s layout pins :=
    substitute_queryPolynomial _ _ _
  dsimp only at hA
  rw [hs, show eval c Q = (signedContraction layout pins : ZMod p) from (live_eq_eval ..).symm] at hA
  exact pinRow_of_action p B H q hq g Ω _ _ i (hpin _ hL _ hA.1 hA.2)

end Diagonal

end BorderVNP
end Computability
end OAI
