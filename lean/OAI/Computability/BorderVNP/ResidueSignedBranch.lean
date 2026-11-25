import OAI.Computability.BorderVNP.ResiduePinsQuantitative
import OAI.Computability.BorderVNP.ResidueNumberedExpansion

/-!
# The boundary row for the signed family at a nonsingular arithmetic place

The power and nonzero pin are chosen at the branch before the physical
layouts, literals, and input pins. A place above the prescribed full table
coefficients supplies the Laurent specialization of every row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Residue ResidueBox ResiduePins Residue.JetRing Branch Module MvPolynomial IsLocalRing
open scoped Classical BigOperators

variable {Pin Wire Proc β E K : Type*} [Fintype Wire] [Fintype Proc] [Fintype β]
  [Field E] [Fintype E] [Field K] [Algebra E K] [Algebra (Polynomial E) K]
  [IsScalarTower E (Polynomial E) K] [Algebra (FractionRing (Polynomial E)) K]
  [IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) K]
  (V : ValuationSubring K) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime]
  [CharP V p] [CharP (ResidueField V) p] [Finite (ResidueField V)]
  [CharP E p] [Algebra (ZMod p) E] [Algebra (ZMod p) K]

/-- Prime-field scalar action used to read the finite residue field. -/
noncomputable local instance residueScalars : Algebra (ZMod p) (ResidueField V) := ZMod.algebra _ _

/-- Quantitative residue action on the signed physical contraction, using the actual
finite-field chart equations and the original regularity/nonunit conditions at the place. -/
theorem signed_branch_rows (π : V) (hπ : Irreducible π) (t : Kˣ)
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
    ∃ u > 0, p^u ≤ Fintype.card E * max (chartBoxPoleBudget h H S) 1 ∧ (∀ a : E, a ^ (p^u) = a) ∧
      ∃ Ω : Index β (Fin h) H → ZMod p, (∃ j, Ω j ≠ 0) ∧
        ∀ (layout : Proc → Fin (k+1) → InputSlot Pin Wire) (pins : Pin → Bool) (i : Index β (Fin h) H),
        ∑ j, pinEntry (entryWeight p B H (p^u) (pow_pos (Fact.out : p.Prime).pos u) g)
          i j (numberedSubstituted E k s e layout pins) * Ω j =
          (signedContraction layout pins : ZMod p) * Ω i := by
  intro h S H
  let ρ := branchLaurentExpansion p π hπ K
  let φ := ρ.comp (algebraMap E K)
  let v := ρ ∘ x
  let c := coeffVector (k+1) (map (Int.castRingHom (ZMod p)) (rename e (Pstar (k+1))))
  have hout (a) : 0 ≤ (eval₂Hom φ v (numberedTable E _ k s a)).order ∧
      (eval₂Hom φ v (numberedTable E _ k s a)).coeff 0 = algebraMap (ZMod p) (ResidueField V) (c a) := by
    have ha := completed_prime_output V p π hπ (c a) (hy a) (hc a)
    have hm := map_eval₂Hom (algebraMap E K) x ρ (numberedTable E _ k s a)
    change 0 ≤ (ρ (eval₂Hom (algebraMap E K) x _)).order ∧
      (ρ (eval₂Hom (algebraMap E K) x _)).coeff 0 = _ at ha
    rw [hm] at ha
    exact ha
  obtain ⟨_, u, hu, _, hbound, hfix, hΩ, ha⟩ := quantitative_residue_pins V p π hπ t ht h0 x hgen g hg hJ B L
  refine ⟨u, hu, hbound, hfix, _, hΩ, ?_⟩
  intro layout pins i
  exact numbered_signed_pinRow p k s e φ v B H L (p^u) (pow_pos (Fact.out : p.Prime).pos u)
    g _ ha layout pins hL (fun a => (hout a).1) (fun a => (hout a).2) i

end Diagonal

end BorderVNP
end Computability
end OAI
