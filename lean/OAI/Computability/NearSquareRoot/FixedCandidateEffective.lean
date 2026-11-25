import OAI.Computability.NearSquareRoot.FixedCandidateArena

/-! # Effective assembly when every candidate uses linear space -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code EffectiveBoundedTask

variable {P : Type} [Primcodable P] (K : P → ℕ)
variable (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
variable (plans : ∀ p i, Plan (hv p i)) (c : P → Clocks)

/-- Effective assembly on the large-width domain. All commands use linear space, including the two parallel operand packets. -/
theorem effective_largeTask (hK : ∀ p, 2 ≤ K p) (ops : EffectiveTransports K hv plans c) :
    Family (fun p (i : LargeInput (K p)) => (c p).total i.val.width) (fun _ i => i.val.width)
      (fun _ i => send i.val.operands) (fun _ i => send (Lea.answer i.val.operands)) :=
  effective_largeTask_atArena K hv plans c (fun _ n => n) (fun p => (c p).total) hK
    (fun _ _ => le_rfl) (fun p n => by unfold Clocks.total; omega) (fun _ _ => le_rfl)
    ⟨ops.crt,ops.undoCRT,ops.fourier,ops.adjoint⟩

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
