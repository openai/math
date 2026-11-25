import OAI.Computability.NearSquareRoot.PhysicalWalshEffectiveRoutesJoint
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorRectangleStage
import OAI.Computability.NearSquareRoot.InterchangeROMBinarySelected
import OAI.Computability.NearSquareRoot.FixedCandidateJointParameters
import OAI.Computability.NearSquareRoot.FixedLayerWalshCompilerFor

/-! # The routed XOR programs for the actual fixed-candidate parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshEffectiveRoutes

open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode PhysicalWalshCompile.Dispatch
open FixedCandidate.CandidateParameters FixedLayer KernelPass.ComputableSyntax
open GeneratorSyntax CommonRegisters
open PhysicalWalshCompileInterior (rectangleStage rectangleStage_effective rectangleStage_runs rectangleStage_within)

/-- The same rectangle is used by the wide field and the native front stage.
The other three tuple components do not enter the recursive piece's cost. -/
theorem profilesFromRectangle (rect : Guess → Cmd) (er : Effective ltr rect) (H : ℕ)
    (reg : ∀ p, Within H (rect p)) (works : ∀ p, Controlled.Effective.rectContract (rect p)
      (Generator.midExponent (exponent p))) :
    ∃ (flat : Guess × Raw → Op → Cmd) (R : ℕ), Effective ltr (Function.uncurry flat) ∧
      (∀ k op, Within R (flat k op)) ∧ ∀ p,
        TotalXorCosts (fun r => flat (p,r)) (signedTemplate p) ∧
        SharpXorCosts (fun r => flat (p,r)) (signedTemplate p) (Generator.midExponent (exponent p)) 0 := by
  obtain ⟨S,_,stageReg⟩ := rectangleStage_within H
  obtain ⟨flat,R,d,eff,within,run⟩ := compileJoint rect (rectangleStage ∘ rect) er
    (rectangleStage_effective er) H S reg (fun p => stageReg _ (reg p))
  refine ⟨flat,R,eff,within,?_⟩
  intro p
  let a := (dimensions (signedTemplate p)).1
  let W := (dimensions (signedTemplate p)).2
  let ρ := Generator.midExponent (exponent p)
  let sel := Classical.choice (selected_of_good (signedTemplate p) (signedTemplate_good p))
  have ha : 4 ≤ a := by have := sel.large; dsimp [a]; omega
  have width : (Packed.decode (a+1) (signedTemplate p).2).i = W := congrArg Packed.i sel.decode
  have range := midpoint_bounds (exponent p)
  have hρ : 0 ≤ ρ := (by norm_num : (0:ℝ) ≤ 1/2).trans range.1.le
  obtain ⟨ok,sharp⟩ := run p a W (signedTemplate p).2 d ha le_rfl width
  obtain ⟨st,stRate⟩ := rectangleStage_runs hρ (works p)
  obtain ⟨degree,native⟩ := works p
  obtain ⟨b,total⟩ := ok ⟨⟨ρ,degree,hρ,native⟩,st⟩
  refine ⟨⟨b,b,total⟩,d,Nat.zero_le d,extra a W ρ,74*(4+(2:ℝ)^ρ+5505),by positivity,
    sharp ρ hρ range.2 ⟨⟨degree,native⟩,stRate⟩,?_⟩
  exact fun t good => extra_bound (by omega) range.1.le range.2 t good

/-- Select exactly the physical interchange template at twice the Fourier
exponent index plus two. Both time and totality hold on all candidate tuples. -/
theorem selectedProfiles (F : InterchangeROMFamily.NativeFamily) :
    ∃ (flat : Guess × Raw → Op → Cmd) (R : ℕ), Effective ltr (Function.uncurry flat) ∧
      (∀ k op, Within R (flat k op)) ∧ ∀ p,
        TotalXorCosts (fun r => flat (p,r)) (signedTemplate p) ∧
        SharpXorCosts (fun r => flat (p,r)) (signedTemplate p) (Generator.midExponent (exponent p)) 0 := by
  obtain ⟨D,H,c,eff,run⟩ := InterchangeROMBinary.Selected.ofNative F
  apply profilesFromRectangle (c ∘ nativeIndex) (eff.comp nativeIndex_pr.to_comp) H (fun p => (run _).1)
  intro p
  exact ⟨D,native_exponent p ▸ (run (nativeIndex p)).2⟩

/-- The signed template is exactly the one already used for the precision
guard. Both guarantees concern the same code emitted for every tuple. -/
theorem selectedPieces (F : InterchangeROMFamily.NativeFamily) :
    ∃ (piece : Guess → Cmd) (R : ℕ), Effective ltr piece ∧ 0 < R ∧ (∀ p, Within R (piece p)) ∧
      ∃ sel : ∀ p, Selected (exponent p+3) (2*(exponent p+2)) (signedTemplate p),
        ∀ p, TotalPiece (sel p) (piece p) ∧ PackedPieceRate (sel p) (piece p) (Generator.midExponent (exponent p)) := by
  obtain ⟨flat,M,ef,wr,physical⟩ := selectedProfiles F
  obtain ⟨cmd,R,D,ec,hR,_,wc,sel,body⟩ := compiledPieceProfilesFor computable_midpoint_templates.choose
    computable_midpoint_templates.choose_spec.1 computable_midpoint_templates.choose_spec.2 flat ef M wr
  refine ⟨fun p => cmd (p,exponent p),R,ec.comp (Computable.id.pair exponent_pr.to_comp),hR,
    fun p => wc (p,exponent p),fun p => sel (exponent p),?_⟩
  intro p
  obtain ⟨total,sharp⟩ := body p (exponent p)
  obtain ⟨allRows,fast⟩ := physical p
  exact ⟨total allRows,sharp (fast.atDegree D)⟩

end PhysicalWalshEffectiveRoutes

end NearSquareRoot
end Computability
end OAI
