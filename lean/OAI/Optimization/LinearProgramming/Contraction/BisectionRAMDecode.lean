import OAI.Optimization.LinearProgramming.PriceGame.Model
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Contraction
namespace BisectionRAM

open PriceGame OracleSpec

/-- Used to interpret the source bit machine's finite transcripts. The deployed
scalar RAM separately parses its actual packet with the checked native parser. -/
noncomputable def readQuery (n : ℕ) (w : Word) : Option (Query n) := by
  classical
  exact if h : ∃ q : Query n, priceQuery q.index q.prices = w then some h.choose else none

theorem readQuery_price {n : ℕ} (q : Query n) :
    readQuery n (priceQuery q.index q.prices) = some q := by
  classical
  have h : ∃ t : Query n, priceQuery t.index t.prices = priceQuery q.index q.prices := ⟨q,rfl⟩
  rw [readQuery,dite_eq_left h]
  have inj : Function.Injective (fun t : Query n => priceQuery t.index t.prices) := by
    intro x y eq
    obtain ⟨hi,hp⟩ := priceQuery_injective.mp eq
    cases x; cases y; congr
  exact congrArg some (inj h.choose_spec)

end BisectionRAM
end Contraction
end LinearProgramming
end Optimization
end OAI
