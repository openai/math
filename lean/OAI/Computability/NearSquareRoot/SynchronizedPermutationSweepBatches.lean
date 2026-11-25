import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweep
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchSemantics
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

/-! # A physical half-stage over the coefficient records in their original order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PermutationSweep
open IntegerMultiplication IntegerMultiplication.Code
open Space Benes

variable {X : Type*} {E B V : X → Type*}
variable (w : (x : X) → B x → ℕ) (tables : (x : X) → E x → B x → RawTable)
variable (which : (x : X) → B x → ℕ) (half : X → Bool × ℕ)

local notation "Address" => fun x => PackedAddress (E x) (w x)

/-- Each target group occurs in one batch. Running all the batch kernels gives
the full half-stage on the array, including groups narrower than the current depth. -/
theorem halfStage (batches : X → ℕ) (belongs : ∀ x b, which x b < batches x)
    (key : X → ℕ → Tree) (array : (x : X) → (Address x → V x) → Tree)
    (v : (x : X) → Address x → V x) (tick volume work : X → ℕ)
    (kernel : BoundedTask
      (fun z : (x : X) × Fin (batches x) × Equiv.Perm (Address x) => tick z.1)
      (fun z => work z.1)
      (fun z => .fork (key z.1 z.2.1.val) (array z.1 (scatter z.2.2 (v z.1))))
      (fun z => array z.1 (scatter (batchStage (which z.1) (w z.1) (tables z.1) (half z.1) z.2.1.val)
        (scatter z.2.2 (v z.1)))))
    (directoryFits : ∀ x, (Task.forest (key x) (List.range (batches x))).count ≤ volume x)
    (arrayFits : ∀ x ψ, (array x (scatter ψ (v x))).count ≤ volume x) :
    BoundedTask (fun x => batches x*tick x+volume x) (fun x => volume x+work x)
      (fun x => .fork (Task.forest (key x) (List.range (batches x))) (array x (v x)))
      (fun x => array x (scatter (packedStage (w x) (tables x) (half x)) (v x))) := by
  let inj (z : (x : X) × {b // b ∈ List.range (batches x)} × Equiv.Perm (Address x)) :
      (x : X) × Fin (batches x) × Equiv.Perm (Address x) :=
    ⟨z.1, ⟨z.2.1.val,List.mem_range.mp z.2.1.property⟩,z.2.2⟩
  have execute := run (fun x => List.range (batches x))
    (fun x => batchStage (which x) (w x) (tables x) (half x)) key array v tick volume work
    (kernel.on inj) directoryFits arrayFits
  exact execute.conform (fun _ => by simp) (fun _ => rfl) (fun _ => rfl)
    (fun x => congrArg (array x) (batchStage_run (which x) (w x) (tables x) (half x)
      (batches x) (belongs x) (v x)))

/-- Build the directory from the short header while the coefficient array remains
parked. The generator's polynomial cost is independent of the parked array's size. -/
theorem withPolyDirectory {H R : Type*} [Codec H] [Codec R] (header : X → H)
    (generate : H → List R) (effective : Poly generate) (scale : X → ℕ)
    (short : Dom scale (fun x => size (header x)))
    (directory data output : X → Tree) (render : ∀ x, send (generate (header x)) = directory x)
    (time space : X → ℕ) (sweep : BoundedTask time space (fun x => .fork (directory x) (data x)) output) :
    ∃ overhead : X → ℕ, Dom scale overhead ∧
      BoundedTask (fun x => overhead x+time x)
        (fun x => max (size (header x)+overhead x+(data x).count) (space x))
        (fun x => .fork (send (header x)) (data x)) output := by
  obtain ⟨overhead,cost,gen⟩ := effective.on short
  refine ⟨overhead,cost,?_⟩
  have prepare := (BoundedTask.of_time gen).left data
  exact (prepare.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (output' := fun x => .fork (directory x) (data x)) (fun x => by rw [render])).compose sweep

end PermutationSweep

end NearSquareRoot
end Computability
end OAI
