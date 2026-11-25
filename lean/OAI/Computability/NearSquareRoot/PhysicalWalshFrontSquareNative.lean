import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareElementary
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareNativeJoint

/-! # Complete canonical XOR command from a native three-slot program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh GeneratorSyntax CommonRegisters
open KernelPass KernelPass.ComputableSyntax

/-- The selected raw descriptor determines arity and width. The single
generated command includes compact header expansion, native padding and
cropping, the square-log test and the full signed-record elementary branch.
Only a bound for the supplied native kernel on the reached physical inputs
is required. -/
theorem compileSquareFromNative {Z : Type} [Primcodable Z] (raw : Z → Raw) (hraw : Computable raw)
    (core : Z → Cmd) (hc : Effective ltr core) (R : ℕ) (reg : ∀ z, Within R (core z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0<N ∧ 1≤e ∧ (∀ z, Within N (emit z)) ∧
      ∀ (z : Z) (ρ : ℝ) (a W : ℕ) (ops : List Op) (arity : 4 ≤ a),
        raw z = (a+1,ops) → (Packed.decode (a+1) ops).i = W →
        PhysicalWalshCompileInterior.NativeOn a W ρ (squareFits a) (core z) →
        ∀ d, e ≤ d → PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan a W d (squareExtra a W ρ)) (nodeArena a W d) (Interior.axes a arity) (emit z) := by
  obtain ⟨emit,N,e,eff,hn,he,regs,sharp,_⟩ :=
    compileSquareFromNativeJoint raw hraw core hc R reg
  exact ⟨emit,N,e,eff,hn,he,regs,sharp⟩

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
