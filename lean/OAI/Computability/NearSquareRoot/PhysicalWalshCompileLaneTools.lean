import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyFold
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyMapping
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyTally
import OAI.Computability.NearSquareRoot.PhysicalWalshChildLanes

/-! # Compiling lists of a varying finite number of lane queries -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Lanes

open IntegerMultiplication Code KernelEffectiveFamily

variable {P X Y : Type} [Primcodable P] [Codec X] [Codec Y] {R : ℕ}

/-- The number of emitted operations can vary with the template while all
instructions use the same register pool. -/
theorem listOfFn (hR : 4 ≤ R) (n : P → ℕ) (hn : Computable n)
    {v : P × ℕ → X → Y} (hv : Family R v) :
    Family R (fun p x => List.ofFn (fun j : Fin (n p) => v (p,j.val) x)) := by
  apply (Family.foldList hR n hn hv (fun z : Y × List Y => z.1 :: z.2) RegisterWitness.Easy.cons []).congr
  intro p x
  simp

/-- A compiled duplicate of each block ruler for every lane in the template. -/
theorem repeat_family (hR : 4 ≤ R) : Family R (fun n : ℕ => List.replicate (α := X) n) := by
  simpa only [List.ofFn_const, id_eq] using listOfFn hR id Computable.id
    (Family.identity (P := ℕ × ℕ) (X := X) (R := R))

end PhysicalWalshCompile.Lanes

end NearSquareRoot
end Computability
end OAI
