import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquareJoint
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryFull

/-! # The same front-gate command realizes slow and sharp executions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code PhysicalWalsh Space CommonRegisters GeneratorSyntax

/-- Emit a single program for the two canonical adjacent slots. Every reached
short branch terminates on the complete elementary sweep. The native branch
can supply data-dependent budgets even for a candidate lacking the sharp rate. -/
theorem compileSquareWithNativeJoint {Z : Type} [Primcodable Z] (a W : Z → ℕ)
    (ha : Computable a) (hw : Computable W) (large : Z → Cmd)
    (el : Effective ltr large) (R : ℕ) (regL : ∀ z, Within R (large z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0 < N ∧ (∀ z, Within N (emit z)) ∧
      (∀ (z : Z) (ρ : ℝ) (arity : 4 ≤ a z) (d : ℕ), e ≤ d →
        let A := a z+1
        let g := Interior.axes (a z) arity
        branchRuns (W:=W z) g (squareFits (a z))
          (fun s => allowance A d s + Interior.extra (a z) (W z) ρ s) (allowance A d) (large z) →
        PhysicalWalshCompileXorPacket.FlatRuns (W:=W z)
          (nodeScan (a z) (W z) d (squareExtra (a z) (W z) ρ)) (nodeArena (a z) (W z) d) g (emit z)) ∧
      ∀ (z : Z) (arity : 4 ≤ a z),
        let g := Interior.axes (a z) arity
        branchTotal (W:=W z) g (squareFits (a z)) (large z) →
        flatTotal (W:=W z) g (emit z) := by
  obtain ⟨Rs,es,walk,eff,reg,hwalk⟩ := PhysicalWalshCompileElementaryRelease.compiled false
  let key (z : Z) : PhysicalWalshCompileSwapRulers.Control := (a z+1,W z,1,2,0)
  have keyComp : Computable key :=
    (Computable.succ.comp ha).pair (hw.pair (Computable.const (1,2,0)))
  obtain ⟨emit,N,e,hgen,pos,hreg,branch,total⟩ :=
    compileSquareGateJoint a ha (walk ∘ key) large (eff.comp keyComp) el (max Rs R)
      (fun z => RegisterSelect.within_mono (le_max_left ..) _ (reg (key z)))
      (fun z => RegisterSelect.within_mono (le_max_right ..) _ (regL z))
  have short (z : Z) (arity : 4 ≤ a z) (d : ℕ) (de : es ≤ d) :
      PhysicalWalshCompileXorPacket.FlatRuns (W:=W z)
        (nodeScan (a z) (W z) d (ElementarySweep.extra (a z+1))) (nodeArena (a z) (W z) d)
        (Interior.axes (a z) arity) (walk (key z)) := by
    let g := Interior.axes (a z) arity
    have ne : g.2 ≠ g.1 := by intro h; have h' := congrArg Fin.val h; change 1=2 at h'; omega
    have elementary := hwalk (a z) (W z) g.2 g.1 ne 0 d de
    rw [PhysicalWalshCompileElementaryRelease.full_slice g.2 g.1 ne] at elementary
    exact elementary
  refine ⟨emit,N,max e es,hgen,pos,hreg,?_,?_⟩
  · intro z ρ arity d hd
    dsimp only
    intro native
    exact branch z (W z) ρ arity d ((le_max_left ..).trans hd)
      (PhysicalWalsh.ClosedRuns.on (short z arity d ((le_max_right ..).trans hd)) Subtype.val) native
  · intro z arity
    dsimp only
    intro largeTotal
    apply total z (W z) arity _ largeTotal
    exact ⟨_,_,PhysicalWalsh.ClosedRuns.on (short z arity es le_rfl) Subtype.val⟩

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
