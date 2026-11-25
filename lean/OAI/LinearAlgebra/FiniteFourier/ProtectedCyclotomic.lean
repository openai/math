import OAI.LinearAlgebra.FiniteFourier.ProtectedRationals
import OAI.LinearAlgebra.FiniteFourier.ProtectedShears

/-! # The cyclotomic coefficient ring with protected odd primes -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- After adjoining a primitive root of admissible order, the protected ring is
semilocal, every scalar splits into two units, and the root has full order in
every residue field. -/
theorem protectedCyclotomic_properties {L : Finset ℕ}
    (hL : ∀ p ∈ L, Nat.Prime p) (hodd : ∀ p ∈ L, Odd p)
    {E : Type*} [CommRing E] [IsDomain E] [Algebra (protectedRationals L) E]
    {ζ : E} {M : ℕ} (hM : 0 < M) (hζ : IsPrimitiveRoot ζ M) (hc : ∀ p ∈ L, p.Coprime M) :
    let O := Algebra.adjoin (protectedRationals L) ({ζ} : Set E)
    let w : O := ⟨ζ, Algebra.subset_adjoin (Set.mem_singleton ζ)⟩
    Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧
      (∀ μ : O, ∃ t : O, IsUnit t ∧ IsUnit (μ - t)) ∧
      ∀ m : MaximalSpectrum O, IsPrimitiveRoot (Ideal.Quotient.mk m.asIdeal w) M := by
  intro O w
  let : Finite (MaximalSpectrum (protectedRationals L)) := finite_maximalSpectrum_protectedRationals hL
  let : Finite (MaximalSpectrum O) := finite_maximalSpectrum_adjoin_root _ hM hζ.pow_eq_one
  have h₂ : IsUnit (2 : O) := by
    simpa only [map_natCast, Nat.cast_ofNat, map_ofNat] using (isUnit_natCast_protectedRationals (d := 2) (by decide)
      (fun p hp => Nat.coprime_two_right.mpr (hodd p hp))).map (algebraMap (protectedRationals L) O)
  have hunit : IsUnit (M : O) := by
    simpa using (isUnit_natCast_protectedRationals hM.ne' hc).map (algebraMap (protectedRationals L) O)
  have hw : IsPrimitiveRoot w M := by
    apply IsPrimitiveRoot.of_map_of_injective (f := O.val) (ζ := w) hζ
    exact Subtype.coe_injective
  exact ⟨inferInstance, h₂, exists_unit_split h₂,
    fun m => primitiveRoot_map_of_unit_order (R := O) (S := O ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal) hw hunit⟩

end FiniteFourier
end LinearAlgebra
end OAI
