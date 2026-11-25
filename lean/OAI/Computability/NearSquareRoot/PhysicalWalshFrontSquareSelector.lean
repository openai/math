import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSelectorNamed

/-! # A Walsh front selector with a reserve computed from the current header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Staff Strip Carry PhysicalWalsh Space PhysicalWalshCompile
open PhysicalWalshCompileChild CommonRegisters GeneratorSyntax
open private level active width prefFigure suffix childBits from OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildHeader

/-- Reserve degree computed during the run from the serialized descriptor size. -/
def squareDegree (A : ℕ) (s : Shape) := Nat.clog 2 (Header.scale A s+1)

/-- One emitted program per arity inspects each incoming node's compact header,
computes the live reserve degree and emits the branch bit, preserving the
descriptor and lane. The register and polynomial bounds apply across arities. -/
theorem compileSquareSelector : ∃ (emit : ℕ → Cmd) (R e : ℕ),
    Effective ltr emit ∧ (∀ a, Within R (emit a)) ∧
    ∀ (a W d : ℕ), e ≤ d →
      let v := fun t : XorInput W => allowance (a+1) d t.shape
      let packet := fun t : XorInput W =>
        Tree.fork (send (Header.wire (a+1) t.shape)) (send (laneFlat (a+1) W t.shape t.row))
      ClosedRuns (emit a) v v packet (fun t => .fork (.atom (decide
        (XorThreshold.cutoff (squareDegree (a+1) t.shape) (Header.scale (a+1) t.shape) ≤
          Interior.L (a+1) t.shape))) (packet t)) := by
  let test (t : World) := decide (XorThreshold.cutoff (squareDegree (t.a+1) t.shape)
    (Header.scale (t.a+1) t.shape) ≤ Interior.L (t.a+1) t.shape)
  have q := scaleFigureOf (fun t : World => t.a+1) World.shape level active width prefFigure suffix
  have hd := (q.added (Figure.natural 1)).short_log
  obtain ⟨emit,R,e,eff,reg,run⟩ := compileTag test (hasComparison hd q childBits)
  exact ⟨fun a => emit (a,0),R,e,eff.comp (Computable.id.pair (Computable.const 0)),
    fun _ => reg _,fun a W d he => run a W 0 d he⟩

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
