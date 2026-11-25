import OAI.LinearAlgebra.SpectralBooks.BorderCircuitTransport

/-!
# Characteristic invariance of degree-component border circuit size

For a polynomial with integer coefficients, the border complexity of its image in a field
depends only on the characteristic. The common comparison field is the algebraic closure of
the prime field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MvPolynomial

/-- Extending the coefficient field preserves degree-component border size. -/
theorem degreeBorderSizeAtMost_map_iff {P F σ : Type*} [Field P] [Field F]
    [Algebra P F] (d s : ℕ) (f : MvPolynomial σ P) :
    DegreeBorderSizeAtMost d s (MvPolynomial.map (algebraMap P F) f) ↔
      DegreeBorderSizeAtMost d s f := by
  let : Algebra P (AlgebraicClosure F) :=
    ((algebraMap F (AlgebraicClosure F)).comp (algebraMap P F)).toAlgebra
  let e : AlgebraicClosure P →ₐ[P] AlgebraicClosure F := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure P) (AlgebraicClosure F) := e.toRingHom.toAlgebra
  have h := circuitClosure_map_iff (K := AlgebraicClosure P) (L := AlgebraicClosure F) d s
    (MvPolynomial.map (algebraMap P (AlgebraicClosure P)) f)
  unfold DegreeBorderSizeAtMost
  simp only [MvPolynomial.map_map] at h ⊢
  convert h using 3
  congr 2
  ext a
  exact (e.commutes a).symm

private theorem map_intCast_atMost_iff {σ : Type*} (d s : ℕ) (f : MvPolynomial σ ℤ)
    (P E : Type*) [Field P] [Field E] [Algebra P E] :
    DegreeBorderSizeAtMost d s (MvPolynomial.map (Int.castRingHom E) f) ↔
    DegreeBorderSizeAtMost d s (MvPolynomial.map (Int.castRingHom P) f) := by
  have h := degreeBorderSizeAtMost_map_iff (F := E) d s (MvPolynomial.map (Int.castRingHom P) f)
  rwa [MvPolynomial.map_map, show (algebraMap P E).comp (Int.castRingHom P) =
    Int.castRingHom E from Subsingleton.elim _ _] at h

/-- The border complexity of an integer polynomial agrees over all fields of a fixed
characteristic, including characteristic zero. -/
theorem degreeBorderSize_eq_of_charP (F G : Type*) [Field F] [Field G] (p : ℕ)
    [CharP F p] [CharP G p] {σ : Type*} (d : ℕ) (f : MvPolynomial σ ℤ) :
    degreeBorderSize d (MvPolynomial.map (Int.castRingHom F) f) =
      degreeBorderSize d (MvPolynomial.map (Int.castRingHom G) f) := by
  have equiv (s : ℕ) :
      DegreeBorderSizeAtMost d s (MvPolynomial.map (Int.castRingHom F) f) ↔
      DegreeBorderSizeAtMost d s (MvPolynomial.map (Int.castRingHom G) f) := by
    have compare (P : Type) [Field P] [Algebra P F] [Algebra P G] :=
      (map_intCast_atMost_iff d s f P F).trans (map_intCast_atMost_iff d s f P G).symm
    rcases CharP.char_is_prime_or_zero F p with hp | rfl
    · let : Fact p.Prime := ⟨hp⟩
      let := ZMod.algebra F p
      let := ZMod.algebra G p
      exact compare (ZMod p)
    · let : CharZero F := (CharP.charP_zero_iff_charZero F).mp inferInstance
      let : CharZero G := (CharP.charP_zero_iff_charZero G).mp inferInstance
      exact compare ℚ
  apply le_antisymm <;> apply (degreeBorderSize_le_iff ..).mpr
  · exact (equiv _).mpr ((degreeBorderSize_le_iff ..).mp le_rfl)
  · exact (equiv _).mp ((degreeBorderSize_le_iff ..).mp le_rfl)

end SpectralBooks
end LinearAlgebra
end OAI
