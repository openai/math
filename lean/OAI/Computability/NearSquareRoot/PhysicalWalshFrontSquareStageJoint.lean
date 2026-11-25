import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareNativeJoint
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorNativeTotal
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorNativeSquare

/-! # Sharp and total execution of the same compiled front XOR -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh CommonRegisters GeneratorSyntax
open KernelPass KernelPass.ComputableSyntax PhysicalWalshCompileInterior

/-- Every total address stage gives a terminating front XOR on the real row.
For the same command, a stage with a certified exponent and reserve degree
also gives the sharp scan and arena bounds. -/
theorem compileSquareFromStageJoint {Z : Type} [Primcodable Z] (raw : Z → Raw) (hraw : Computable raw)
    (stage : Z → Cmd) (hs : Effective ltr stage) (R : ℕ) (reg : ∀ z, Within R (stage z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0 < N ∧ 1 ≤ e ∧ (∀ z, Within N (emit z)) ∧
      (∀ (z : Z) (ρ : ℝ) (a W : ℕ) (ops : List Op) (arity : 4 ≤ a),
        raw z = (a+1,ops) → (Packed.decode (a+1) ops).i = W → ρ ≤ 1 →
        (∃ D, XorWindow.StagesAt PhysicalWalshCompileInteriorHeader.nativeRegime
          worldPrefix worldBits worldRow ρ D (stage z)) →
        ∀ d, e ≤ d → PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan a W d (squareExtra a W ρ)) (nodeArena a W d) (Interior.axes a arity) (emit z)) ∧
      ∀ (z : Z) (a W : ℕ) (ops : List Op) (arity : 4 ≤ a),
        raw z = (a+1,ops) → (Packed.decode (a+1) ops).i = W →
        XorWindow.StagesTotal PhysicalWalshCompileInteriorHeader.nativeRegime
          worldPrefix worldBits worldRow (stage z) →
        flatTotal (W:=W) (Interior.axes a arity) (emit z) := by
  let r := PhysicalWalshCompileInteriorHeader.nativeRegime
  let gate z := XorWindow.gateCmd r worldBits nativeWidth (stage z)
  let core z := XorWindow.duskCmd (gate z)
  have eg : Effective ltr gate := XorWindow.gateCmd_effective r worldBits nativeWidth hs
  have ec : Effective ltr core := XorWindow.duskCmd_effective eg
  obtain ⟨G,_,hg⟩ := XorWindow.gateCmd_within r worldBits nativeWidth R
  obtain ⟨K,_,hk⟩ := XorWindow.duskCmd_within G
  obtain ⟨emit,N,e,ee,hn,he,within,run,total⟩ := compileSquareFromNativeJoint raw hraw core ec K
    (fun z => hk _ (hg _ (reg z)))
  refine ⟨emit,N,e,ee,hn,he,within,?_,?_⟩
  · intro z ρ a W ops arity key width upper certificate
    obtain ⟨D,hD⟩ := certificate
    have assembled : WorldGate ρ (max D forestReserve) (gate z) :=
      XorWindow.boundedGateOnNamed worldPrefix worldBits nativeWidth worldRow hD
    have native : SquareNative ρ (core z) := squareNativeOfGate upper assembled
    exact run z ρ a W ops arity key width (native a W arity)
  · intro z a W ops arity key width certified
    exact total z a W ops arity key width (nativeTotalOfStage certified a W arity (squareFits a))

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
