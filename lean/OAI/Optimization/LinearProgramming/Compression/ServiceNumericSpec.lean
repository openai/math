import OAI.Optimization.LinearProgramming.Compression.NativeCache
import OAI.Optimization.LinearProgramming.Compression.ProxyFuel
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! Interface of the closed numerical subroutine. It is given only a list of the
positive generator/request magnitudes, the ambient dimension, and a membership/rank
pair. It has no access to a matrix or to the identities of the minors. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog

def numericalValue {g : ℕ} (n : ℕ) (position : Option (Fin g)) (mag : Fin (g+1) → ℚ) : Option ℚ :=
  sharedMinorStep n g position (requestMagnitudeNegative (manuscriptProxyFuel n) (paperRadius n+7) mag)

/-- The input address words are ordinary natural registers. A missing minor still has
a sorted insertion rank, which is retained only by the enclosing table manager.
The input scalar tape contains the `g` generator magnitudes followed by the requested
magnitude. The clock depends on dimension alone and every temporary scalar is charged. -/
def NumericSolverSpec (p : Program) (time height : Polynomial ℕ) : Prop :=
  ∀ {n g : ℕ}, g ≤ paperWidth n → ∀ (position : Option (Fin g)) (rank : ℕ), rank ≤ g →
    (∀ i,position=some i → i.val=rank) → ∀ (mag : Fin (g+1) → ℚ), (∀ i,0 < mag i) →
    ∃ t, call p (time.eval n) (height.eval (n+totalBits (List.ofFn mag)))
      (start [n,g,position.isSome.toNat,rank] (List.ofFn mag)) t ∧ emits t (numericalValue n position mag)

theorem numericalValue_of_minor {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ)
    (E : Matrix (Fin e) (Fin n) ℚ) (J : Finset (NonzeroPairMinor D E))
    (u : NonzeroPairMinor D E) :
    numericalValue n (matrixMinorPosition J u) (matrixMinorCache D E J u) =
      matrixMinorRequest D E (manuscriptProxyFuel n) J u :=
  (matrixMinorRequest_eq_sharedStep D E (manuscriptProxyFuel n) J u).symm

end Compression
end LinearProgramming
end Optimization
end OAI
