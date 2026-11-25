import OAI.Computability.NearSquareRoot.FixedLayerWalshCompiler
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeRoutedFor

/-! # Literal compiled pieces for a specified signed template selector -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1500000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code Space FixedPoint KernelPass KernelPass.ComputableSyntax
open PhysicalWalsh PhysicalWalshNode PhysicalWalshCompile PhysicalWalshCompile.Dispatch
open CommonRegisters GeneratorSyntax EffectiveBoundedTask

/-- The selector is an input to the compiler so every arithmetic component
can retain the same selected signed word and precision threshold. -/
theorem compiledPieceProfilesFor {Z : Type} [Primcodable Z] (r : ℕ → Raw) (hs : Computable r)
    (good : ∀ j, (interpreted (r j)).Good (j+3) (2*(j+2)))
    (flat : Z × Raw → Op → Cmd) (eff : Effective ltr (Function.uncurry flat))
    (M : ℕ) (bounded : ∀ q op, Within M (flat q op)) :
    ∃ (cmd : Z × ℕ → Cmd) (R D : ℕ), Effective ltr cmd ∧ 0 < R ∧ 1 ≤ D ∧
      (∀ p,Within R (cmd p)) ∧ ∃ sel : (j : ℕ) → Selected (j+3) (2*(j+2)) (r j), ∀ z j,
        (TotalXorCosts (fun a => flat (z,a)) (r j) → TotalPiece (sel j) (cmd (z,j))) ∧
        (SharpXorCosts (fun a => flat (z,a)) (r j) (Generator.midExponent j) D →
          PackedPieceRate (sel j) (cmd (z,j)) (Generator.midExponent j)) := by
  obtain ⟨cmd,R,D,_,_,hc,hR,hD,reg,sel,total,rate⟩ := Node.compileRoutedTotalFor r hs good flat eff M bounded
  refine ⟨cmd,R,D,hc,hR,hD,reg,sel,fun z j => ⟨?_,?_⟩⟩
  · rintro ⟨scan,arena,h⟩
    exact total z j scan arena h
  · rintro ⟨d,hd,extra,c,hc,run,bound⟩
    have eqn : (((j+3:ℕ):ℝ)/(2*(j+2):ℕ)) = Generator.midExponent j := by
      unfold Generator.midExponent
      push_cast
      have hj := Nat.cast_nonneg (α:=ℝ) j
      field_simp
      ring
    obtain ⟨K,_,ready⟩ := rate j d hd
    rw [eqn] at ready
    obtain ⟨B,hB,exec⟩ := ready z extra run c RouterClock.logWidth (fun _ => 0) hc
      RouterClock.one_le_logWidth (fun _ => le_rfl) bound
    exact ⟨B,4*K+c,K,d,hB,by positivity,exec⟩

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
