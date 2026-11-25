import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareStageJoint
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareNative

/-! # Compiling the complete front XOR from the native address-stage file -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh CommonRegisters GeneratorSyntax
open KernelPass KernelPass.ComputableSyntax PhysicalWalshCompileInterior

/-- The program generator only reads the finite template and stage files. A
candidate's exponential rate and its reserve degree need to be justified
only when asking for that candidate's physical running-time certificate. -/
theorem compileSquareFromStage {Z : Type} [Primcodable Z] (raw : Z → Raw) (hraw : Computable raw)
    (stage : Z → Cmd) (hs : Effective ltr stage) (R : ℕ) (reg : ∀ z, Within R (stage z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0 < N ∧ 1 ≤ e ∧ (∀ z, Within N (emit z)) ∧
      ∀ (z : Z) (ρ : ℝ) (a W : ℕ) (ops : List Op) (arity : 4 ≤ a),
        raw z = (a+1,ops) → (Packed.decode (a+1) ops).i = W → ρ ≤ 1 →
        (∃ D, XorWindow.StagesAt PhysicalWalshCompileInteriorHeader.nativeRegime
          worldPrefix worldBits worldRow ρ D (stage z)) →
        ∀ d, e ≤ d → PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan a W d (squareExtra a W ρ)) (nodeArena a W d) (Interior.axes a arity) (emit z) := by
  obtain ⟨emit,N,e,eff,hn,he,within,sharp,_⟩ := compileSquareFromStageJoint raw hraw stage hs R reg
  exact ⟨emit,N,e,eff,hn,he,within,sharp⟩

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
