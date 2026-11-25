import OAI.Computability.BorderVNP.ResidueBranchDiagonal
import OAI.Computability.BorderVNP.BranchCurveEvaluation
import OAI.Computability.BorderVNP.BranchParseFamily

/-!
# Applying the residue diagonal to the geometric branch of Proposition 9.2

The affine time coordinate and Jacobian are recovered from the generic
equations over `E(t)`. The discrete place provides its own uniformizer
and preserves the original prime-field boundary values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Residue ResidueBox ResiduePins Residue.JetRing Module Matrix MvPolynomial IsLocalRing
open scoped BigOperators Matrix Classical

universe u

variable {Pin Wire Proc β E : Type*} [Fintype Wire] [Fintype Proc] [Fintype β]
  [Field E] [Fintype E] (p : ℕ) [Fact p.Prime] [CharP E p] [Algebra (ZMod p) E]

/-- The genuine arithmetic branch constructed for the entire signed table yields
a uniformly bounded Frobenius power and a nonzero pin acting on every signed row. These are
chosen before every subsequent layout, input encoding, and term expansion. -/
theorem geometric_branch_rows (k s : ℕ)
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (g : Fin (parameterCount (2*(k+1)) k s) →
      MvPolynomial (Option (Fin (parameterCount (2*(k+1)) k s))) E)
    (branch : GeometricBranch (numberedTable E (2*(k+1)) k s)
      (Int.castRingHom E ∘ coeffVector (k+1) (rename e (Pstar (k+1))))
      (fun i => genericRow (g i)))
    [Finite (ResidueField branch.place)]
    (B : Basis β (ZMod p) E) (L : ℕ) (hL : Fintype.card Proc * (2*k+1) ≤ L) :
    let h := parameterCount (2*(k+1)) k s
    let S := ∑ j, (g j).totalDegree
    let H := radius L S
    let I := Index β (Fin h) H
    ∃ r > 0, p^r ≤ Fintype.card E * max (chartBoxPoleBudget h H S) 1 ∧ (∀ a : E, a ^ (p^r) = a) ∧
      ∃ Ω : I → ZMod p, (∃ j, Ω j ≠ 0) ∧
        ∀ (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool) (i : I),
        ∑ j, pinEntry (entryWeight p B H (p^r) (pow_pos (Fact.out : p.Prime).pos r) g)
          i j (numberedSubstituted E k s e layout pins) * Ω j =
          (signedContraction layout pins : ZMod p) * Ω i := by
  let F := DeformationField E
  let K := branch.L
  let V := branch.place
  let ψ := (algebraMap F K).comp (algebraMap (Polynomial E) F)
  let : Algebra (Polynomial E) K := ψ.toAlgebra
  let : IsScalarTower (Polynomial E) F K := .of_algebraMap_eq fun _ => rfl
  have he : ψ.comp Polynomial.C = algebraMap E K := by
    apply RingHom.ext
    intro a
    change algebraMap F K (algebraMap (Polynomial E) F (algebraMap E (Polynomial E) a)) = _
    rw [← IsScalarTower.algebraMap_apply E (Polynomial E) F, ← IsScalarTower.algebraMap_apply E F K]
  let : IsScalarTower E (Polynomial E) K := .of_algebraMap_eq fun a => (RingHom.congr_fun he a).symm
  let : CharP K p := charP_of_injective_ringHom (algebraMap E K).injective p
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  let : IsDiscreteValuationRing V := branch.discrete
  let coeff : E →+* V := (algebraMap E K).codRestrict V.toSubring
    (finite_constants_regular (algebraMap E K) V)
  let : CharP V p := charP_of_injective_ringHom coeff.injective p
  let : CharP (ResidueField V) p := charP_of_injective_ringHom ((residue V).comp coeff).injective p
  let : Finite (ResidueField V) := inferInstanceAs (Finite (ResidueField branch.place))
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hψ : Function.Injective ψ := (algebraMap F K).injective.comp (IsFractionRing.injective _ _)
  let t : Kˣ := Units.mk0 (ψ Polynomial.X) ((map_ne_zero_iff ψ hψ).mpr Polynomial.X_ne_zero)
  obtain ⟨hg,hJ⟩ := branch_affine_equations branch
  change ∀ i, eval₂Hom (ψ.comp Polynomial.C) (fun j => j.elim (t : K) branch.x) (g i) = 0 at hg
  change eval₂Hom (ψ.comp Polynomial.C) (fun j => j.elim (t : K) branch.x) (boxJacobian g) ≠ 0 at hJ
  rw [he] at hg hJ
  rw [eval_boxJacobian] at hJ
  apply signed_branch_rows V p π hπ t rfl branch.parameter_zero k s e
    branch.x branch.generates g hg hJ B L hL
  · exact fun i => (branch.outputs i).1
  · intro i
    have hc := (branch.outputs i).2
    change eval₂ (algebraMap E K) branch.x (numberedTable E _ k s i) -
      algebraMap E K ((Int.castRingHom E) ((rename e (Pstar (k+1))).coeff i.val)) ∈ V.nonunits at hc
    have hh (z : ℤ) : algebraMap E K (Int.castRingHom E z) =
        algebraMap (ZMod p) K (Int.castRingHom (ZMod p) z) := RingHom.congr_fun
      (Subsingleton.elim ((algebraMap E K).comp (Int.castRingHom E))
        ((algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)))) z
    simpa only [coeffVector, coeff_map, hh] using hc

/-- The genuine arithmetic branch constructed for the entire signed table yields
a uniformly bounded Frobenius power and a distinguished nonzero pin. These are
chosen before every subsequent layout, input encoding, and term expansion. -/
theorem geometric_branch_excludes_unit_evaluator (k s : ℕ)
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (g : Fin (parameterCount (2*(k+1)) k s) →
      MvPolynomial (Option (Fin (parameterCount (2*(k+1)) k s))) E)
    (branch : GeometricBranch (numberedTable E (2*(k+1)) k s)
      (Int.castRingHom E ∘ coeffVector (k+1) (rename e (Pstar (k+1))))
      (fun i => genericRow (g i)))
    [Finite (ResidueField branch.place)]
    (B : Basis β (ZMod p) E) (L : ℕ) (hL : Fintype.card Proc * (2*k+1) ≤ L) :
    let h := parameterCount (2*(k+1)) k s
    let S := ∑ j, (g j).totalDegree
    let H := radius L S
    let I := Index β (Fin h) H
    ∃ r > 0, p^r ≤ Fintype.card E * max (chartBoxPoleBudget h H S) 1 ∧ (∀ a : E, a ^ (p^r) = a) ∧
      ∃ (Ω : I → ZMod p) (star : I), Ω star ≠ 0 ∧
      ∀ (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (encode : I → Pin → Bool)
        (Path : I → Type u) [∀ i, Fintype (Path i)]
        (μ : ∀ i, Path i → Fin h →₀ ℕ) (a : ∀ i, Path i → E),
        (∀ i, numberedSubstituted E k s e layout (encode i) =
          ∑ j, monomial (μ i j) (a i j)) →
        ∃ j, (signedContraction layout (encode j) : ZMod p) ≠
          (if j = star then 1 else 0) + ∑ i, ∑ l,
            entryWeight p B H (p^r) (pow_pos (Fact.out : p.Prime).pos r) g (μ i l) i j (a i l) := by
  intro h S H I
  obtain ⟨r, hr, hbound, hfix, Ω, ⟨star, hstar⟩, hrow⟩ :=
    geometric_branch_rows (Pin := Pin) (Wire := Wire) p k s e g branch B L hL
  refine ⟨r, hr, hbound, hfix, Ω, star, hstar, ?_⟩
  intro layout encode Path _ μ a hex
  by_contra! hcol
  exact incompatible_assignment_evaluator
    (entryWeight p B H (p^r) (pow_pos (Fact.out : p.Prime).pos r) g)
    star Ω (fun j => (signedContraction layout (encode j) : ZMod p)) hstar
    (fun i => numberedSubstituted E k s e layout (encode i)) μ a hex
    (fun i => hrow layout (encode i) i) hcol

end Diagonal

end BorderVNP
end Computability
end OAI
