import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareElementaryJoint

/-! # Emitting the complete square-log front gate with its elementary sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code PhysicalWalsh Space CommonRegisters GeneratorSyntax

/-- Emit a single program for the two canonical adjacent slots. The short
branch is the full-width directed elementary sweep on that pair, while the
native branch is required only on headers that pass the live reserve test. -/
theorem compileSquareWithNative {Z : Type} [Primcodable Z] (a W : Z → ℕ)
    (ha : Computable a) (hw : Computable W) (large : Z → Cmd)
    (el : Effective ltr large) (R : ℕ) (regL : ∀ z, Within R (large z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0 < N ∧ (∀ z, Within N (emit z)) ∧
      ∀ (z : Z) (ρ : ℝ) (arity : 4 ≤ a z) (d : ℕ), e ≤ d →
        let A := a z+1
        let g := Interior.axes (a z) arity
        branchRuns (W:=W z) g (squareFits (a z))
          (fun s => allowance A d s + Interior.extra (a z) (W z) ρ s) (allowance A d) (large z) →
        PhysicalWalshCompileXorPacket.FlatRuns (W:=W z)
          (nodeScan (a z) (W z) d (squareExtra (a z) (W z) ρ)) (nodeArena (a z) (W z) d) g (emit z) := by
  obtain ⟨emit,N,e,eff,hn,regs,sharp,_⟩ :=
    compileSquareWithNativeJoint a W ha hw large el R regL
  exact ⟨emit,N,e,eff,hn,regs,sharp⟩

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
