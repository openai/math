import OAI.Computability.BorderVNP.BranchCurveGraphCoordinates
import OAI.Computability.BorderVNP.BranchCurveRealization

/-!
# The residue point on the sliced graph

A point of the graph fiber defines a character on the chart's coordinate
ring, even at a parameter at infinity. It gives a point over zero on every
component through it. A generic finite-parameter solution of a nonsingular
square system on this component then realizes the simultaneous residues of
the prescribed outputs in one discrete valuation ring.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

variable {σ ι K : Type*} [Field K]
variable (Y : ι → MvPolynomial σ K) (k : Option σ)

/-- A point of the graph zero locus gives a character of the actual chart algebra. -/
theorem graph_point_character (z : Option σ → K) (c : ι → K)
    (h : Sum.elim z c ∈ zeroLocus K (RingHom.ker (graphChartMap Y k))) :
    ∃ point : ChartRing Y k →ₐ[K] K,
      (∀ j, point (chartRatio Y k j) = z j) ∧ (∀ i, point (chartOutput Y k i) = c i) := by
  let f := graphChartAlgHom Y k
  let e := Ideal.quotientKerEquivRange f
  let a := aeval (R := K) (Sum.elim z c)
  have vanishes : ∀ p ∈ RingHom.ker f, a p = 0 := by
    intro p hp
    apply h p
    rwa [← graphChartAlgHom_toRingHom]
  let v := (Ideal.Quotient.liftₐ (RingHom.ker f) a vanishes).comp e.symm.toAlgHom
  have ev (p : MvPolynomial (Option σ ⊕ ι) K) : v (f.rangeRestrict p) = a p := by
    have eq : e (Ideal.Quotient.mk _ p) = f.rangeRestrict p := rfl
    rw [← eq]
    change (Ideal.Quotient.liftₐ _ a vanishes) (e.symm (e _)) = _
    rw [AlgEquiv.symm_apply_apply]
    rfl
  exact ⟨v, fun j => (ev (X (.inl j))).trans (aeval_X _ _),
    fun i => (ev (X (.inr i))).trans (aeval_X _ _)⟩

/-- A component through the retained special-fiber point has the induced
character, with its parameter specializing to zero. -/
theorem special_point_on_component {S : Type*} [CommRing S] [Algebra K S]
    (v : S →ₐ[K] K) (P : Ideal (Polynomial S))
    (hP : P ≤ RingHom.ker (Polynomial.aevalTower v 0)) :
    ∃ point : ComponentRing (A := Polynomial S) P →ₐ[K] K,
      point (Ideal.Quotient.mk P Polynomial.X) = 0 ∧
        ∀ r : S, point (Ideal.Quotient.mk P (Polynomial.C r)) = v r := by
  let p := Polynomial.aevalTower v 0
  refine ⟨Ideal.Quotient.liftₐ P p (fun _ h => hP h), ?_, fun r => ?_⟩
  · exact Polynomial.aevalTower_X v 0
  · exact Polynomial.aevalTower_C v 0 r

/-- The generic parameters of a component of the deformed graph realize the
boundary values of the original output table. This conclusion allows arbitrary
poles in the individual parameters. -/
theorem chart_place_realizes_outputs {A L : Type*} [CommRing A]
    [Field L] [Algebra K A] [Algebra K L] [Algebra A L] [IsScalarTower K A L]
    [IsFractionRing A L] [Algebra (Polynomial K) A] [Algebra (Polynomial K) L]
    [IsScalarTower (Polynomial K) A L] [Algebra (FractionRing (Polynomial K)) L]
    [IsScalarTower K (FractionRing (Polynomial K)) L]
    [IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) L]
    [Fintype σ] [DecidableEq σ] (hk : homogeneousParameters σ K k ≠ 0)
    (π : Polynomial (ChartRing Y k) →ₐ[K] A) (hπ : Function.Surjective π)
    (ht : π Polynomial.X = algebraMap (Polynomial K) A Polynomial.X)
    (φ : ChartRing Y k →ₐ[K] L) (hφ : ∀ r, φ r = algebraMap A L (π (Polynomial.C r)))
    (hd : φ (chartRatio Y k none) ≠ 0) (point : A →ₐ[K] K) (c : ι → K)
    (h0 : point (π Polynomial.X) = 0)
    (houtput : ∀ i, point (π (Polynomial.C (chartOutput Y k i))) = c i)
    (g : σ → MvPolynomial σ (FractionRing (Polynomial K)))
    (hroot : ∀ i, aeval (chartParameters Y k φ) (g i) = 0)
    (hjac : (Matrix.of fun i j => aeval (chartParameters Y k φ) (pderiv j (g i))).det ≠ 0) :
    ∃ (V : ValuationSubring L), IsDiscreteValuationRing V ∧
      (∀ p : Polynomial K, algebraMap (Polynomial K) L p ∈ V) ∧
      algebraMap (Polynomial K) L Polynomial.X ∈ V.nonunits ∧
      ∀ i, aeval (chartParameters Y k φ) (Y i) ∈ V ∧
        aeval (chartParameters Y k φ) (Y i) - algebraMap K L (c i) ∈ V.nonunits := by
  have hgen := chart_generates_component Y k hk π hπ φ hφ hd
    (E := FractionRing (Polynomial K))
    ⟨algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X, by
      rw [ht, ← IsScalarTower.algebraMap_apply (Polynomial K) A L,
        ← IsScalarTower.algebraMap_apply (Polynomial K) (FractionRing (Polynomial K)) L]⟩
  obtain ⟨V, reg, hdis, hz, hres⟩ := place_at_special_point point (ht ▸ h0)
    g _ hgen hroot hjac
  have hregular (p : Polynomial K) : algebraMap (Polynomial K) L p ∈ V := by
    rw [IsScalarTower.algebraMap_apply (Polynomial K) A L]
    exact reg _
  refine ⟨V, hdis, hregular, hz, fun i => ?_⟩
  let a := π (Polynomial.C (chartOutput Y k i))
  have ey : aeval (chartParameters Y k φ) (Y i) = algebraMap A L a :=
    (chartOutput_specializes Y k φ hd i).symm.trans (hφ _)
  rw [ey]
  refine ⟨reg a, ?_⟩
  rw [← houtput i, IsScalarTower.algebraMap_apply K A L]
  have e := hres a
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at e
  exact V.coe_mem_nonunits_iff.mpr e

end Branch

end BorderVNP
end Computability
end OAI
