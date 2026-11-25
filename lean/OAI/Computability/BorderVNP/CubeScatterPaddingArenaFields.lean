import OAI.Computability.BorderVNP.CubeScatterPaddingArenaRoom
import OAI.Computability.BorderVNP.CubeScatterPaddingPublishedStages
import OAI.Computability.BorderVNP.RoutingISACubeArenaFields

/-! # Reading the actual joint cube arena's eight padding literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA RoutingISA.CubeArena VPVNP.BurstRAM Tally
open private public_bounds from OAI.Computability.BorderVNP.CubeScatterPaddingArenaRoom

/-- The padding verifier is a projection of the full native arena's literal field encoder. -/
theorem arena_operand (L : CubeArena.Layout) {j v : ℕ}
    (field : (arenaPointers L).operand L.n L.header.d L.b L.h L.K L.s j = some v) : L.operand j = some v := by
  unfold Pointers.operand at field
  split at field <;> simp_all [CubeArena.Layout.operand,arenaPointers,CubeArena.Layout.alphabet]

/-- The actual length-only 81-word cube extension spells every padding operand exactly,
using one whole-arena room bound and the fixed packet stride bound. -/
theorem arena_literal {w : ℕ} (L : CubeArena.Layout) (old : Fin 81 → Word w)
    (fit : L.stop < 2^w) (bankFit : bankWidth L.n L.b L.h L.K L.s < 2^w)
    (j : Fin 81) (v : ℕ) (field : (arenaPointers L).operand L.n L.header.d L.b L.h L.K L.s (31+j.val) = some v) :
    (L.extension old j).val = v := by
  obtain ⟨widths,powers,owners,triples,vertices⟩ := public_bounds L
  have singles := L.separated.2.1.trans vertices
  have Z : L.alphabet ≤ L.alphabet^2 := by
    by_cases zero : L.alphabet=0
    · simp [zero]
    · rw [pow_two]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero zero)
  have range : v < 2^w := by
    unfold Pointers.operand at field
    split at field <;> simp only [Option.some.injEq,reduceCtorEq] at field <;> try contradiction
    all_goals subst v
    all_goals first
      | exact bankFit
      | exact (show selectorWidth L.n L.K L.h ≤ bankWidth L.n L.b L.h L.K L.s from by unfold bankWidth supplyBase; omega).trans_lt bankFit
      | change L.alphabet < _; omega
      | dsimp only [arenaPointers]; omega
  simp [CubeArena.Layout.extension,arena_operand L field,TeamTapeInputEmit.word,Nat.mod_eq_of_lt range]

end Cube.Padding

end BorderVNP
end Computability
end OAI
