import OAI.Computability.BorderVNP.ResidueSignedBranch

/-!
# Contradiction at the completed arithmetic branch

The fixed Frobenius power and distinguished nonzero pin are selected before
the choice of any processor program or input layout. At least one live column
then differs from the assignment evaluator with its extra unit branch. This
is the algebraic contradiction at the end of §11.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Residue ResiduePins ResidueBox Residue.JetRing Branch Module Matrix MvPolynomial IsLocalRing
open scoped BigOperators Matrix Classical

universe u

variable {Pin Wire Proc β E K : Type*} [Fintype Wire] [Fintype Proc] [Fintype β]
  [Field E] [Fintype E] [Field K] [Algebra E K] [Algebra (Polynomial E) K]
  [IsScalarTower E (Polynomial E) K] [Algebra (FractionRing (Polynomial E)) K]
  [IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) K]
  (V : ValuationSubring K) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime]
  [CharP V p] [CharP (ResidueField V) p] [Finite (ResidueField V)]
  [CharP E p] [Algebra (ZMod p) E] [Algebra (ZMod p) K]

/-- Every layout and term expansion, chosen after the distinguished pin, is
incompatible with the proposed column identity (11.3) for all live pins. -/
theorem branch_excludes_unit_evaluator (π : V) (hπ : Irreducible π) (t : Kˣ)
    (ht : (t : K) = algebraMap (Polynomial E) K Polynomial.X) (h0 : (t : K) ∈ V.nonunits)
    (k s : ℕ) (e : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (x : Fin (parameterCount (2*(k+1)) k s) → K)
    (hgen : IntermediateField.adjoin (FractionRing (Polynomial E)) (Set.range x) = ⊤)
    (g : Fin (parameterCount (2*(k+1)) k s) →
      MvPolynomial (Option (Fin (parameterCount (2*(k+1)) k s))) E)
    (hg : ∀ i, eval₂Hom (algebraMap E K) (fun j => j.elim (t : K) x) (g i) = 0)
    (hJ : (chartJacobian (algebraMap E K) (fun j => j.elim (t : K) x) g).det ≠ 0)
    (B : Basis β (ZMod p) E) (L : ℕ) (hL : Fintype.card Proc * (2*k+1) ≤ L)
    (hy : ∀ a, eval₂ (algebraMap E K) x (numberedTable E _ k s a) ∈ V)
    (hc : ∀ a, eval₂ (algebraMap E K) x (numberedTable E _ k s a) -
      algebraMap (ZMod p) K (coeffVector (k+1)
        (map (Int.castRingHom (ZMod p)) (rename e (Pstar (k+1)))) a) ∈ V.nonunits) :
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
    signed_branch_rows (Pin := Pin) (Wire := Wire) V p π hπ t ht h0 k s e x hgen g hg hJ B L hL hy hc
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
