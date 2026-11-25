import OAI.Optimization.LinearProgramming.Compression.Online
import OAI.Optimization.LinearProgramming.Compression.MinorIndex

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The determinant counting argument bounds the number of restarts of the actual online
transition, for every request prefix, regardless of how requests were selected. -/
theorem minor_request_restarts_le {rD rE N : ℕ}
    (D : Matrix (Fin rD) (Fin N) ℚ) (E : Matrix (Fin rE) (Fin N) ℚ)
    (hN : 1 ≤ N) (hrows : rD + rE = N)
    (l : NonzeroPairMinor D E → ℝ)
    (herr : ∀ i, |l i - Real.logb 2 (|((pairMinorValue D E i.val : ℚ) : ℝ)|)| ≤
      1 / 2 ^ (100 * (N + 1)^3 + 7 : ℕ))
    [DecidableEq (NonzeroPairMinor D E)]
    (request : MinorRequest (NonzeroPairMinor D E)) (htest : RestartTest l request)
    (indices : List (NonzeroPairMinor D E)) :
    ((RequestTrace.replay request indices).restarts : ℝ) ≤
      (7 * (N : ℝ)^2 + 8) * Real.logb 2 (N + 1) := by
  apply RequestTrace.restarts_le l request htest
  intro J hd
  exact dissociated_nonzeroPairMinor_card_le D E hN hrows (Rat.castHom ℝ)
    (Rat.cast_injective) J l (fun i _ => herr i) hd

end Compression
end LinearProgramming
end Optimization
end OAI
