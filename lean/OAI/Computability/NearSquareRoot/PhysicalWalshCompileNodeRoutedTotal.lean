import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeRoutedFor

/-! # Totality and the sharp clock for the same selected physical program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node
open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass ComputableSyntax
open GeneratorSyntax CommonRegisters PhysicalWalshContext

/-- Every successful flat routing implementation yields a terminating raw
piece on all admitted inputs, with no cost requirement on the routing clocks.
The efficient routing estimates give the separate sharp bounds on exactly the
same emitted command. -/
theorem compileRoutedTotalWith {Z : Type} [Primcodable Z] (flat : Z × Raw → Op → Cmd) (eff : Effective ltr (Function.uncurry flat))
    (M : ℕ) (bounded : ∀ r op, Within M (flat r op)) :
    ∃ (s : ℕ → Raw) (cmd : Z × ℕ → Cmd) (R D : ℕ), Computable s ∧
      Computable (Dispatch.dimensions ∘ s) ∧ Computable (rawPrecisionCutoff ∘ s) ∧
      Effective ltr cmd ∧ 0 < R ∧ 1 ≤ D ∧ (∀ j, Within R (cmd j)) ∧
      ∃ sel : (j : ℕ) → Dispatch.Selected (j+3) (2*(j+2)) (s j),
      (∀ (z : Z) (j : ℕ) (scan arena : PhysicalWalshNode.Shape → ℕ),
        let a := (Dispatch.dimensions (s j)).1
        let W := (Dispatch.dimensions (s j)).2
        let hw : 0 < W := by have := (sel j).wide; dsimp [W]; omega
        Dispatch.XorRuns (fun raw => flat (z,raw)) a W (s j).2 scan arena →
        ∃ t r, EffectiveBoundedTask.Runs (cmd (z,j)) t r
          (rawInput hw (sel j).plan) (rawOutput hw (sel j).plan)) ∧
      ∀ (j d : ℕ), D ≤ d →
        let a := (Dispatch.dimensions (s j)).1
        let W := (Dispatch.dimensions (s j)).2
        let p := (sel j).plan
        let hw : 0 < W := by have := (sel j).wide; dsimp [W]; omega
        let ρ := ((j+3 : ℕ) : ℝ)/(2*(j+2) : ℕ)
        ∃ K : ℕ, 1 ≤ K ∧ ∀ (z : Z) (extra : PhysicalWalshNode.Shape → ℕ),
          Dispatch.XorRuns (fun raw => flat (z,raw)) a W (s j).2 (nodeScan a W d extra) (nodeArena a W d) →
          ∀ (c : ℝ) (L P : ℕ → ℝ), 0 ≤ c → (∀ w, 1 ≤ L w) → (∀ w, 0 ≤ P w) →
          (∀ t, withinWidth (a+1) t → (extra t : ℝ) ≤ localTime (a+1) ρ c (L t.w) (P t.w) t.level
            (bitVolume (a+1) t)) →
          ∃ B : ℝ, 0 ≤ B ∧ EffectiveBoundedTask.Runs (cmd (z,j))
            (fun v : Admitted hw p => pieceTimeBound (a+1) p.calls ρ B L (envelopeSetup K d P) v.val.shape)
            (fun v => pieceSpaceBound (a+1) (4*K+c) (envelopeSetup K d P) v.val.shape)
            (rawInput hw p) (rawOutput hw p) := by
  obtain ⟨s,hs,good⟩ := computable_midpoint_templates
  obtain ⟨cmd,R,D,h⟩ := compileRoutedTotalFor s hs good flat eff M bounded
  exact ⟨s,cmd,R,D,hs,h⟩

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
