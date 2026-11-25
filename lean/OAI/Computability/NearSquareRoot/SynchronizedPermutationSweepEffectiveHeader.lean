import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.BoundedProduct
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

/-! # Effective directory generation with the array parked on the data stack -/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication Code CommonRegisters GeneratorSyntax Space

namespace EffectiveBoundedTask

variable {P : Type} [Primcodable P] {I : P → Type}
  {t s t' s' : ∀ p, I p → ℕ} {u v w : ∀ p, I p → Tree}

/-- Run a generated command on the first field without reading the second.
The wrapper uses register zero, which already lies in the family's bound. -/
theorem Family.left (f : Family t s u v) (spectator : ∀ p, I p → Tree) :
    Family t (fun p i => s p i + (spectator p i).count)
      (fun p i => .fork (u p i) (spectator p i)) (fun p i => .fork (v p i) (spectator p i)) := by
  obtain ⟨c,R,he,hR,hc⟩ := f
  refine ⟨_,R,KernelEffectiveFamily.effective_left he,hR,fun p => ⟨?_,?_⟩⟩
  · exact KernelEffectiveFamily.within_left hR (hc p).1
  · exact command_contract (KernelEffectiveFamily.leftCmd (c p))
      from (hc p).2.task.left (spectator p)

/-- Execute the two generated files in sequence, reusing their registers and workspace. -/
theorem Family.compose (f : Family t s u v) (g : Family t' s' v w) :
    Family (fun p i => t p i+t' p i) (fun p i => max (s p i) (s' p i)) u w :=
  (f.mono (fun _ _ => Nat.le_add_right ..) (fun _ _ => le_max_left ..)).sequence
    (g.mono (fun _ _ => Nat.le_add_left ..) (fun _ _ => le_max_right ..))

end EffectiveBoundedTask

namespace PermutationSweep.Effective

open EffectiveBoundedTask

/-- One polynomial directory generator suffices for every candidate. It reads
only the short header. During its run the coefficient array contributes its
size to space, with no term involving the array in the preparation time. -/
theorem withPolyDirectory {P : Type} [Primcodable P] {I : P → Type}
    {H R : Type} [Codec H] [Codec R] (header : ∀ p, I p → H)
    (generate : H → List R) (effective : Poly generate) (scale : ∀ p, I p → ℕ)
    (short : ∀ p, Dom (scale p) (fun i => size (header p i)))
    (directory data output : ∀ p, I p → Tree) (render : ∀ p i, send (generate (header p i)) = directory p i)
    (time space : ∀ p, I p → ℕ)
    (sweep : Family time space (fun p i => .fork (directory p i) (data p i)) output) :
    ∃ overhead : ∀ p, I p → ℕ, (∀ p, Dom (scale p) (overhead p)) ∧
      Family (fun p i => overhead p i + time p i)
        (fun p i => max (size (header p i) + overhead p i + (data p i).count) (space p i))
        (fun p i => .fork (send (header p i)) (data p i)) output := by
  obtain ⟨cost,hcost,cmd,C,hc⟩ := effective
  let overhead p (i : I p) := cost (header p i)
  refine ⟨overhead,fun p => (hcost.map (header p)).sub (short p),?_⟩
  have gen : Family overhead (fun p i => size (header p i) + overhead p i)
      (fun p i => send (header p i)) directory := by
    apply Family.fixed_run cmd
    intro p
    have base := Runs.of_time (c := cmd) (t := cost) (u := send)
      (v := fun h => send (generate h)) ⟨C,hc⟩
    rw [← funext (render p)]
    obtain ⟨K,hK⟩ := base
    exact ⟨K,fun i => hK (header p i)⟩
  exact (gen.left data).compose sweep

end PermutationSweep.Effective

end NearSquareRoot
end Computability
end OAI
