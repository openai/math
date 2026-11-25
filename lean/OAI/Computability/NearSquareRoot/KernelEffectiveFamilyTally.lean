import OAI.Computability.NearSquareRoot.KernelEffectiveFamily
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoom

/-! # Emitting a parameter-dependent unary literal -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveFamily.Family

open IntegerMultiplication Code CommonRegisters GeneratorSyntax

theorem tally {P X : Type} [Primcodable P] [Codec X] {R : ℕ} (hR : 1 ≤ R)
    (n : P → ℕ) (hn : Computable n) :
    Family R (fun p => fun _ : X => Code.tally (n p)) := by
  let ruler (p : P) := send (Code.tally (n p))
  refine ⟨fun p => (discard 0).join (Task.prepare 0 (ruler p)),
    (effective_const ltr _).join (PhysicalWalshCompile.effective_tally_prepare.comp hn),?_⟩
  intro p
  refine ⟨⟨LoomRegisters.discard_within hR, (RegisterWitness.prepare_within _).mpr hR⟩,
    20+5*(ruler p).count,fun x env r => ?_⟩
  change Fits env _ (pile 0 (send x) r) (pile 0 (ruler p) r) (_*((send x).count+1))
  apply ((fits_discard _ _ _ _).join (Task.fits_prepare 0 (ruler p) env r)).mono
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
  omega

end KernelEffectiveFamily.Family

end NearSquareRoot
end Computability
end OAI
