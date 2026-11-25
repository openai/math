import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorNativeTotal
import OAI.Computability.NearSquareRoot.CRTPositionNamedOpcode

/-! # Specializing the native Walsh address stage to a rectangular interchange -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code PhysicalWalsh Controlled.PositionProgram
open PhysicalWalshCompileInteriorHeader (nativeRegime nativeP)
open CommonRegisters GeneratorSyntax

/-- The same rectangle program appears in every opcode of the native
three-slot stage. Its input and return wrappers depend only on the fixed
two-width header convention. -/
noncomputable def rectangleStage (rect : Cmd) : Cmd :=
  XorWindow.stageCmd nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow (opcodeCmd rect)

theorem rectangleStage_effective {Z : Type} [Primcodable Z] {rect : Z → Cmd}
    (h : Effective ltr rect) : Effective ltr (rectangleStage ∘ rect) :=
  XorWindow.stageCmd_effective nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow (opcodeCmd_effective h)

theorem rectangleStage_within (R : ℕ) : ∃ N, 0 < N ∧ ∀ c : Cmd, Within R c → Within N (rectangleStage c) := by
  obtain ⟨K,_,hk⟩ := opcodeCmd_within R
  obtain ⟨N,hN,hn⟩ := XorWindow.stageCmd_within nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow K
  exact ⟨N,hN,fun c hc => hn _ (hk c hc)⟩

/-- A physical rectangle certificate yields both unconditional functional
termination and the given exponent's stage bounds. The clock-sensitive proof
uses the rectangle's charged time and live stack space separately. -/
theorem rectangleStage_runs {rect : Cmd} {ρ : ℝ} (hρ : 0 ≤ ρ) (run : Controlled.Effective.rectContract rect ρ) :
    XorWindow.StagesTotal nativeRegime worldPrefix worldBits worldRow (rectangleStage rect) ∧
      ∃ D, XorWindow.StagesAt nativeRegime worldPrefix worldBits worldRow ρ D (rectangleStage rect) := by
  have op := opcodeCmd_runs hρ run
  refine ⟨?_,XorWindow.stagesFromCanonical nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow op⟩
  obtain ⟨_,_,c⟩ := op
  obtain ⟨t,h,_⟩ := c.work
  exact XorWindow.stagesTotalFromCanonical nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow ⟨t,h⟩

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
