import OAI.Computability.BorderVNP.BranchCurveBoxPole
import OAI.Computability.BorderVNP.BranchCurveBoxEliminants

/-!
# The pole cutoff for the completed arithmetic branch

Every concrete finite test of Lemma 10.1 satisfies one pole bound, computed
from the equation degrees and the box radius. The cutoff applies to a simple
root on a possibly reducible fiber. Its binary length grows polynomially in
the coordinate count and the binary lengths of the input degree bounds.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open Residue ResidueBox ResiduePins Residue.JetRing Module

/-- Uniform pole cutoff in terms of the number of coordinates, the radius,
and the sum of the equation degrees. -/
def chartBoxPoleBudget (h H S : ℕ) : ℕ :=
  let d := boxEliminantInputDegree h H S
  let C := eliminantWidth (h+1) (d+1)
  C * d * C ^ h

/-- At a nonsingular root of the given chart system, all box tests times `dt/J`
have order bounded below by the explicit budget. The estimate applies in the
DVR completion used for the residue and permits poles of the individual coordinates. -/
theorem nonsingular_box_test_order {E L β : Type*} [Field E] [Finite E] [Field L]
    [Algebra E L] [Algebra (Polynomial E) L] [IsScalarTower E (Polynomial E) L]
    [Algebra (FractionRing (Polynomial E)) L] [IsScalarTower (Polynomial E) (FractionRing (Polynomial E)) L]
    (V : ValuationSubring L) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] [CharP V p]
    [CharP (IsLocalRing.ResidueField V) p] [Finite (IsLocalRing.ResidueField V)] [Algebra (ZMod p) E]
    (s : V) (hs : Irreducible s) (t : Lˣ) (ht : (t : L) = algebraMap (Polynomial E) L Polynomial.X)
    (h0 : (t : L) ∈ V.nonunits) {h : ℕ} (x : Fin h → L)
    (hgen : IntermediateField.adjoin (FractionRing (Polynomial E)) (Set.range x) = ⊤)
    (g : Fin h → MvPolynomial (Option (Fin h)) E) (H : ℕ) (B : Basis β (ZMod p) E)
    (hx : ∀ i, MvPolynomial.eval₂Hom (algebraMap E L) (fun j => j.elim (t : L) x) (g i) = 0)
    (hJ : (chartJacobian (algebraMap E L) (fun j => j.elim (t : L) x) g).det ≠ 0) :
    let ρ := branchLaurentExpansion p s hs L
    let φ := ρ.comp (algebraMap E L)
    let τ := Units.map ρ.toMonoidHom t
    let J := (chartJacobian φ (fun j => j.elim (τ : LaurentSeries _) (ρ ∘ x)) g).det
    ∀ i : Index β (Fin h) H, -((chartBoxPoleBudget h H (∑ j, (g j).totalDegree) : ℕ) : ℤ) ≤
      (evaluate φ (ρ ∘ x) τ (test B i) *
        (LaurentSeries.derivative (IsLocalRing.ResidueField V) (τ : LaurentSeries _) / J)).order := by
  let φ₀ := algebraMap (Polynomial E) L
  let d := boxEliminantInputDegree h H (∑ j, (g j).totalDegree)
  let C := eliminantWidth (h+1) (d+1)
  have hφ : φ₀.comp Polynomial.C = algebraMap E L := (IsScalarTower.algebraMap_eq E (Polynomial E) L).symm
  obtain ⟨hRs, hQ⟩ := chart_box_eliminants φ₀ t ht.symm x g H (hφ ▸ hx) (hφ ▸ hJ)
  choose R hne hC hr using hRs
  have root (i) : Polynomial.aeval (x i)
      ((R i).map (algebraMap (Polynomial E) (FractionRing (Polynomial E)))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      ← IsScalarTower.algebraMap_eq (Polynomial E) (FractionRing (Polynomial E)) L]
    exact hr i
  have hp := box_test_pole_bound V p s hs t ht h0 x R hgen hne root C hC g H (C*d) B (hφ ▸ hQ)
  simpa only [Fintype.card_fin, chartBoxPoleBudget, d, C] using hp

/-- The first admissible cardinality power has a polynomial binary-length bound
in the field-cardinality bits, input-degree bits, and number of coordinates. -/
theorem chart_box_pin_power_bits {q k h H S a b : ℕ} (hk : k ≤ 2 ^ a)
    (hd : boxEliminantInputDegree h H S ≤ 2 ^ b)
    (hq : q ≤ k * max (chartBoxPoleBudget h H S) 1) :
    let c := ((b+2) * (4*(h+3)) + 2) * (h+1)
    Nat.clog 2 q ≤ a + (c+b) + c*h := by
  let d := boxEliminantInputDegree h H S
  exact pin_power_bit_bound hk (ratioEliminant_parameterDegree_le (h := h) (d := d) hd hd)
    (ratioEliminant_width_le (h := h) hd) hq

end Branch

end BorderVNP
end Computability
end OAI
