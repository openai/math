import OAI.Computability.NearSquareRoot.PrecisionEffectiveTemplate
import OAI.Computability.NearSquareRoot.PhysicalWalshPackedRelease
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStage

/-! # Physical recursive Walsh execution for the selected literal templates

The arity, bank width, rounded update and recursive-call saving in the tape
bound all refer to the same parsed template. The arithmetic correctness
cutoff is computed from the actual code file.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

open PhysicalWalshNode PhysicalWalsh.Pieces

/-- The packed tape recursion and rounding estimates of the decoded file
at a scheduler comparison index. -/
def PhysicalAt (j : ℕ) (r : Raw) : Prop :=
  ∃ (a W : ℕ) (ha : 1 < a+1) (hw : 0 < W) (p : Plan (a+1) W W),
    4 ≤ a ∧ 2 ≤ W ∧ r.1 = a+1 ∧ Packed.decode (a+1) r.2 = ⟨W,W,p⟩ ∧
    interpreted r = ⟨a+1,W,p⟩ ∧ Correct p ∧
    (p.calls : ℝ)/W < ((a+1 : ℕ) : ℝ)^Generator.midExponent j ∧
    (∀ k ≥ rawPrecisionCutoff r, GroupedAccurateAt ha hw p k) ∧
    ∃ (c : ℝ) (K d : ℕ), 0 ≤ c ∧
      PieceRelease hw p (Generator.midExponent j) c RouterClock.logWidth (envelopeSetup K d (fun _ => 0))

theorem midpoint_bounds (j : ℕ) : 1/2 < Generator.midExponent j ∧ Generator.midExponent j ≤ 1 := by
  constructor
  ·
    unfold Generator.midExponent
    have h : 0 < 1/(2*((j:ℝ)+2)) := by positivity
    linarith
  ·
    unfold Generator.midExponent
    have h : 1/(2*((j:ℝ)+2)) ≤ 1/2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith [Nat.cast_nonneg (α:=ℝ) j]
    linarith

/-- Direct release from the same finite validation predicate used by the generator. -/
theorem physicalAt_of_good {r : Raw} {j : ℕ} (good : (interpreted r).Good (j+3) (2*(j+2))) :
    PhysicalAt j r := by
  obtain ⟨a,W,ha,hw,p,hA,hp,interp,correct,hs,hacc⟩ := accurateTemplate_of_good r good
  rw [interp] at good
  have arity : 4 ≤ a := by have h : 5 ≤ a+1 := good.1; omega
  have wide : 2 ≤ W := good.2.1
  have exp := midpoint_exponent j
  change _ = Generator.midExponent j at exp
  rw [exp] at hs
  obtain ⟨lower,upper⟩ := midpoint_bounds j
  exact ⟨a,W,ha,hw,p,arity,wide,hA,hp,interp,correct,hs,hacc,
    PackedRelease.pieceRelease p hw wide arity lower upper hs⟩

/-- One effective choice of literal templates gives a correct physical
recursive transform with a strict saving at each midpoint exponent. -/
theorem computable_physical_templates :
    ∃ select : ℕ → Raw, Computable select ∧ ∀ j, PhysicalAt j (select j) := by
  obtain ⟨s,eff,good⟩ := computable_midpoint_templates
  exact ⟨s,eff,fun j => physicalAt_of_good (good j)⟩

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
