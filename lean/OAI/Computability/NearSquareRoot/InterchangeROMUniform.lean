import OAI.Computability.NearSquareRoot.InterchangeROMOuterComponents
import OAI.Computability.NearSquareRoot.InterchangeROMBinarySelected

/-!
# The uniform physical interchange codes

One finite-register compiler accepts the exponent index and a lower bound
on the radix. It emits the complete recursive program, including the
selected finite-field tables and both physical changes of row layout.
The binary specialization acts on ordinary records at every width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFamily

open InterchangeROMOuter

theorem exists_native_family : Nonempty NativeFamily := by
  obtain ⟨F⟩ := InterchangeROMFront.exists_core
  obtain ⟨kb,kc,ku,components⟩ := native_components F
  obtain ⟨R,regs⟩ := template_registers
  exact NativeFamily.ofComponents F templateEnter templateLeave effective_templateEnter
    effective_templateLeave R R (fun x => (regs x).1) (fun x => (regs x).2) kb kc ku components

theorem binary_rectangles :
    ∃ (D R : ℕ) (command : ℕ → IntegerMultiplication.Code.Cmd),
    GeneratorSyntax.Effective GeneratorSyntax.ltr command ∧ ∀ j,
      CommonRegisters.Within R (command j) ∧
      InterchangeROMBinary.RectPhysical (command j) (Generator.targetExponent j) D := by
  obtain ⟨F⟩ := exists_native_family
  exact InterchangeROMBinary.Selected.ofNative F

end InterchangeROMFamily

end NearSquareRoot
end Computability
end OAI
