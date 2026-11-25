import OAI.Computability.BorderVNP.ResidueAdviceCircuit
import OAI.Computability.BorderVNP.ResidueGeometricBranch
import OAI.Computability.BorderVNP.ResidueEntryScalarReader

/-!
# The branch pin and entry reader for the signed universal table

The selected Frobenius power, common vector, distinguished index and both
shared readers precede the choice of the diagonal layout. The row circuit
bound is obtained directly from the chart advice that produced the place.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch ResidueBox ResiduePins ResidueEntryVerifier Module IsLocalRing MvPolynomial
open scoped BigOperators Classical

universe u

variable {Pin Wire Proc E : Type*} [Fintype Wire] [Fintype Proc]
  [Field E] [Fintype E] (p : ℕ) [Fact p.Prime] [CharP E p] [Algebra (ZMod p) E]

/-- The literal equations used for the arithmetic branch of the signed paired family. -/
noncomputable abbrev signedAdviceEquations (k s : ℕ)
    [Fintype (DegreeMonomial (Fin (2*(k+1))) (k+1))]
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (advice : CurveAdvice E (parameterCount (2*(k+1)) k s)) :=
  advice.equations (numberedTable E (2*(k+1)) k s)
    (Int.castRingHom E ∘ coeffVector (k+1) (rename e (Pstar (k+1))))
    (pairedDegreeExponent (k+1)) ((k+2)^(2*(k+1)))

/-- On the concrete branch of Proposition 9.2, one common matrix reader serves every
layout and input. For its distinguished index the claimed unit-plus-column identity
fails on at least one input of each expansion of the true signed row. -/
theorem geometric_signed_reader_fixed (k s : ℕ)
    [Fintype (DegreeMonomial (Fin (2*(k+1))) (k+1))]
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (advice : CurveAdvice E (parameterCount (2*(k+1)) k s))
    (branch : GeometricBranch (numberedTable E (2*(k+1)) k s)
      (Int.castRingHom E ∘ coeffVector (k+1) (rename e (Pstar (k+1))))
      (fun i => genericRow (signedAdviceEquations k s e advice i)))
    [Finite (ResidueField branch.place)]
    {D : ℕ} (B : Basis (Fin D) (ZMod p) E) (L : ℕ) (hL : Fintype.card Proc * (2*k+1) ≤ L) :
    let g := signedAdviceEquations k s e advice
    let h := parameterCount (2*(k+1)) k s
    let S := ∑ j, (g j).totalDegree
    let H := radius L S
    let I := Index (Fin D) (Fin h) H
    let size := adviceGateBudget (2*(k+1)) k s
    ∃ r > 0, p^r ≤ Fintype.card E * max (chartBoxPoleBudget h H S) 1 ∧ (∀ a : E, a ^ (p^r) = a) ∧
      ∃ (Ω : I → ZMod p) (star : I), Ω star ≠ 0 ∧
      ScalarEntryReader B (p^r) (pow_pos (Fact.out : p.Prime).pos r) H size g ∧
      (∀ (J : Type*) [Fintype J] (m : ℕ) (gadgets : J → E),
        GadgetEntryReader B (p^r) (pow_pos (Fact.out : p.Prime).pos r) H size g m gadgets) ∧
      ∀ (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (encode : I → Pin → Bool)
        (Path : I → Type u) [∀ i, Fintype (Path i)]
        (μ : ∀ i, Path i → Fin h →₀ ℕ) (a : ∀ i, Path i → E),
        (∀ i, numberedSubstituted E k s e layout (encode i) =
          ∑ j, monomial (μ i j) (a i j)) →
        ∃ j, (signedContraction layout (encode j) : ZMod p) ≠
          (if j = star then 1 else 0) + ∑ i, ∑ l,
            entryWeight p B H (p^r) (pow_pos (Fact.out : p.Prime).pos r) g (μ i l) i j (a i l) := by
  intro g h S H I size
  obtain ⟨r,hr,hbound,hfix,Ω,star,hstar,hcol⟩ :=
    geometric_branch_excludes_unit_evaluator (Pin := Pin) (Wire := Wire) p k s e g branch B L hL
  have hg (i : Fin h) : VPVNP.circuitSize (g i) ≤ size := advice.equations_circuitSize ..
  refine ⟨r,hr,hbound,hfix,Ω,star,hstar,?_,?_,?_⟩
  · exact exists_scalar_reader p B (p^r) H size (pow_pos (Fact.out : p.Prime).pos r) g hg
  · intro J _ m gadgets
    exact exists_reader_over_base p B (p^r) H size m (pow_pos (Fact.out : p.Prime).pos r) g hg gadgets

  · intro layout encode Path _ μ a hex
    obtain ⟨j,hj⟩ := hcol layout encode Path μ a hex
    refine ⟨j, ?_⟩
    by_cases he : j = star
    · simpa only [ite_eq_left he] using hj
    · simpa only [ite_eq_right he] using hj

/-- On the concrete branch of Proposition 9.2, one common matrix reader serves every
layout and input. For its distinguished index the claimed unit-plus-column identity
fails on at least one input of each expansion of the true signed row. -/
theorem geometric_signed_reader (k s : ℕ)
    [Fintype (DegreeMonomial (Fin (2*(k+1))) (k+1))]
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (advice : CurveAdvice E (parameterCount (2*(k+1)) k s))
    (branch : GeometricBranch (numberedTable E (2*(k+1)) k s)
      (Int.castRingHom E ∘ coeffVector (k+1) (rename e (Pstar (k+1))))
      (fun i => genericRow (signedAdviceEquations k s e advice i)))
    [Finite (ResidueField branch.place)]
    {D : ℕ} (B : Basis (Fin D) (ZMod p) E) (L : ℕ) (hL : Fintype.card Proc * (2*k+1) ≤ L) :
    let g := signedAdviceEquations k s e advice
    let h := parameterCount (2*(k+1)) k s
    let S := ∑ j, (g j).totalDegree
    let H := radius L S
    let I := Index (Fin D) (Fin h) H
    let size := adviceGateBudget (2*(k+1)) k s
    ∃ r > 0, p^r ≤ Fintype.card E * max (chartBoxPoleBudget h H S) 1 ∧
      ∃ (Ω : I → ZMod p) (star : I), Ω star ≠ 0 ∧
      ScalarEntryReader B (p^r) (pow_pos (Fact.out : p.Prime).pos r) H size g ∧
      (∀ (J : Type*) [Fintype J] (m : ℕ) (gadgets : J → E),
        GadgetEntryReader B (p^r) (pow_pos (Fact.out : p.Prime).pos r) H size g m gadgets) ∧
      ∀ (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (encode : I → Pin → Bool)
        (Path : I → Type u) [∀ i, Fintype (Path i)]
        (μ : ∀ i, Path i → Fin h →₀ ℕ) (a : ∀ i, Path i → E),
        (∀ i, numberedSubstituted E k s e layout (encode i) =
          ∑ j, monomial (μ i j) (a i j)) →
        ∃ j, (signedContraction layout (encode j) : ZMod p) ≠
          (if j = star then 1 else 0) + ∑ i, ∑ l,
            entryWeight p B H (p^r) (pow_pos (Fact.out : p.Prime).pos r) g (μ i l) i j (a i l) := by
  obtain ⟨r,hr,hb,_,Ω,star,hstar,reader,gadget,hex⟩ :=
    geometric_signed_reader_fixed (Pin := Pin) (Wire := Wire) p k s e advice branch B L hL
  exact ⟨r,hr,hb,Ω,star,hstar,reader,gadget,hex⟩

end Diagonal

end BorderVNP
end Computability
end OAI
