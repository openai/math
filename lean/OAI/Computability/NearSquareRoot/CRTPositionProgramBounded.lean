import OAI.Computability.NearSquareRoot.CRTPositionProgram
import OAI.Computability.NearSquareRoot.CRTControlledBoundedSchedule

/-! # Space-bounded physical execution of the assembled position stream -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Space Reflections

/-- A dispatcher for the four physical stages suffices for the execution of
an arbitrary serialized position permutation. The time pays for every
issued stage; the space reuses the same bound between successive stages. -/
theorem bounded_assemble {X : Type*} {Y : X → Type*} (k G : X → ℕ) (hG : ∀ x, 0 < G x)
    (p : (x : X) → Equiv.Perm (Fin (k x))) (key : X → Op → Tree)
    (box : (x : X) → ((Fin (k x) → Bool) → Y x) → Tree)
    (charge : X → Op → ℕ) (allowance volume : X → ℕ)
    (step : BoundedTask (fun i : (x : X) × {q // q ∈ assemble (tally (G x),table (p x))} ×
        ((Fin (k x) → Bool) → Y x) => charge i.1 i.2.1)
      (fun i => volume i.1)
      (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
      (fun i => box i.1 (i.2.2 ∘ fun w => act (G i.1) w i.2.1)))
    (forestCap : ∀ x, (Task.forest (key x) (assemble (tally (G x),table (p x)))).count ≤ volume x)
    (dataCap : ∀ x f, (box x f).count ≤ volume x)
    (callCap : ∀ x, ∀ a ∈ assemble (tally (G x),table (p x)), charge x a + (key x a).count + 1 ≤ allowance x) :
    BoundedTask (fun i : (x : X) × ((Fin (k x) → Bool) → Y x) =>
      (72*(4+3*G i.1)+4)*allowance i.1 + 1) (fun i => volume i.1)
      (fun i => .fork (Task.forest (key i.1) (assemble (tally (G i.1),table (p i.1)))) (box i.1 i.2))
      (fun i => box i.1 (fun w => i.2 (w ∘ (p i.1).symm))) := by
  have h := boundedSchedule (fun x => assemble (tally (G x),table (p x))) key box
    (fun x b q => b ∘ fun w => act (G x) w q) charge allowance volume step forestCap dataCap callCap
  have m := h.mono (fun i => Nat.add_le_add_right
    (Nat.mul_le_mul_right (allowance i.1) (assemble_length (G i.1) (p i.1))) 1) (fun _ => le_rfl)
  exact m.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun i => congrArg (box i.1) (assemble_rows (hG i.1) (p i.1) i.2))

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
