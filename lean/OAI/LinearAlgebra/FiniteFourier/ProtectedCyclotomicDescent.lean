import OAI.LinearAlgebra.FiniteFourier.ExtensionCircuit
import OAI.LinearAlgebra.FiniteFourier.ProtectedCircuit
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # Descent from the cyclotomic orders of the integral tensor compiler

The cyclotomic power basis gives the exact simulation cost over the protected
rationals, independently of the set of protected primes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial

variable {I O : Type*} [Fintype I] [Fintype O] {k s : ℕ}

/-- Simulate a circuit over a monic cyclotomic quotient in the power basis
of dimension `φ(k)`, restricting inputs and outputs to one component. -/
theorem circuit_of_cyclotomicOrder {R : Type*} [CommRing R] [Nontrivial R]
    (hk : 0 < k) (M : Matrix O I R) (p : Circuit (AdjoinRoot (cyclotomic k R)) I O s)
    (hp : p.matrix = M.map (algebraMap R _)) :
    ∃ n ≤ 2 * k.totient^2 * s + k.totient * Fintype.card O,
      ∃ q : Circuit R I O n, q.matrix = M := by
  let b := (AdjoinRoot.powerBasis' (cyclotomic.monic k R)).basis.reindex
    (finCongr (natDegree_cyclotomic k R))
  simpa only [Fintype.card_fin] using
    circuit_of_extensionBasis b (⟨0, Nat.totient_pos.mpr hk⟩ : Fin k.totient) M p hp

/-- For an integral matrix, descend all gate and readout coefficients to the
protected subring while keeping the matrix equal to its integer specialization. -/
theorem circuit_of_protectedCyclotomic (L : Finset ℕ) (hk : 0 < k)
    (M : Matrix O I ℤ) (p : Circuit (AdjoinRoot (cyclotomic k (protectedRationals L))) I O s)
    (hp : p.matrix = M.map (Int.castRingHom _)) :
    ∃ n ≤ 2 * k.totient^2 * s + k.totient * Fintype.card O,
      ∃ q : Circuit (protectedRationals L) I O n,
        q.matrix = M.map (Int.castRingHom _) := by
  let R := protectedRationals L
  apply circuit_of_cyclotomicOrder hk _ p
  rw [hp]
  ext o i
  exact (map_intCast (algebraMap R (AdjoinRoot (cyclotomic k R))) (M o i)).symm

/-- Descend an integral matrix to a rational circuit in which all gate and
readout denominators avoid the prescribed primes. -/
theorem protectedCyclotomic_circuit_denominators (L : Finset ℕ) (hk : 0 < k)
    (M : Matrix O I ℤ) (p : Circuit (AdjoinRoot (cyclotomic k (protectedRationals L))) I O s)
    (hp : p.matrix = M.map (Int.castRingHom _)) :
    ∃ n ≤ 2 * k.totient^2 * s + k.totient * Fintype.card O,
      ∃ q : Circuit ℚ I O n, q.matrix = M.map (Int.castRingHom ℚ) ∧
        q.DenominatorsIn (denominatorsAvoiding L) := by
  let R := protectedRationals L
  obtain ⟨n, hn, q, hq⟩ := circuit_of_protectedCyclotomic L hk M p hp
  refine ⟨n, hn, q.mapCoeff R.subtype, ?_, q.denominatorsIn_protectedRationals⟩
  rw [Circuit.matrix_mapCoeff, hq]
  ext o i
  simp

end FiniteFourier
end LinearAlgebra
end OAI
