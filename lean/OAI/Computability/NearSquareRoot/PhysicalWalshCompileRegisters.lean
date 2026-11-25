import OAI.Computability.NearSquareRoot.PhysicalWalshCompile
import OAI.Computability.NearSquareRoot.ScheduleRegisterWitness
import OAI.Computability.NearSquareRoot.KernelPassComputableRelation

/-! # The template compiler preserves fixed data-register bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code CommonRegisters KernelPass.ComputableSyntax

private theorem left_within {N : ℕ} (hN : 0 < N) {c : Cmd} (h : Within N c) :
    Within N (left c) := RegisterWitness.splitRoot_within.mpr ⟨hN,trivial,trivial,h,hN⟩

/-- The register count does not increase with plan size, bank width, or arity. -/
theorem command_within {N : ℕ} (hN : 0 < N) (b : BankCode) (zero : Cmd) (leaf : ℕ → Op → Cmd)
    (hs : ∀ i, Within N (b.split i)) (hw : Within N b.swap) (hf : Within N b.finish)
    (hz : Within N zero) (hl : ∀ A op, Within N (leaf A op)) (A : ℕ) (ops : List Op) :
    Within N (command b zero leaf A ops) := by
  let P (_ : Shape) (v : Shape × Cmd) := Within N v.2
  apply Algebra.parse_rel (a := Shape.algebra A) (b := algebra A zero (leaf A) Prog.join b.parallel) P
    hz (hl A) ?_ ?_ ops
  · intro _ _ p q hp hq
    change Within N (if _ then q.2.join p.2 else zero)
    split
    · exact ⟨hq,hp⟩
    · exact hz
  · intro _ _ p q hp hq
    exact ⟨⟨⟨hs _,left_within hN hp⟩,hw⟩,left_within hN hq,hf⟩

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
