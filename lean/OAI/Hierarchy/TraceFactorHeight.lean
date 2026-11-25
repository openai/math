import OAI.Hierarchy.TraceFactorStageBounds
import OAI.ThreeFlat.Diagonal.PhysicalShrinkWordDepth
import OAI.ThreeFlat.Diagonal.PhysicalProgramAssembly
import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordDepth

namespace OAI
/-! # Replay depth of the physical terminal factor

The two joins above a shrink party enumerate occupied parties and active
motifs. Every physical stage adds one more join around its root and children.
-/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open scoped Classical BigOperators

variable {F Pins : Type} [Field F]

open private allKernels all_recast all_step from OAI.Hierarchy.TraceFactorStageBounds
open private rootWithin from OAI.ThreeFlat.Diagonal.PhysicalShrinkWordDepth

private theorem root_output {d l D D' m : ℕ} {A : State d l} (e : D=D') (R : Move F A D m)
    (J : R.Assembler Pins) (h : rootWithin J) : rootWithin (Move.outputAssembler e R J) := by
  cases e
  exact h

attribute [local irreducible] CompressorPacking.shrinkSite RefreshTies.siteTree

private theorem program_kernels {s : ℕ} (P : Program F s) (rem : ℕ) (A : State (2^s) (P.charge+rem)) :
    allKernels (P.run rem A) (P.assembly rem A : (P.run rem A).Assembler Pins) := by
  induction P with
  | done s => intro L h; trivial
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let X : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let M := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) X
    apply all_recast e A (.step M (fun i => tail.run rem (M.next i)))
    apply all_step
    · exact shrinkBinary_root_within T s (2^t) _ _ _ X
    · intro i
      exact ih _
  | refresh s t hgt pad c γ scalar T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let X : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let M := refreshBinary T X hm hh sym rows zero conn
    let R := Program.recastMove degree M
    apply all_recast e A (.step R (fun i => tail.run rem (R.next i)))
    apply all_step
    · exact root_output degree M _ (refreshBinary_root_within T X hm hh sym rows zero conn)
    · intro i
      exact ih _

/-- A physically assembled terminal tree has replay depth bounded by four
plus the exact number of issued shrink and refresh passes. -/
theorem terminal_factor_within {s : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) (P.charge+rem)) (L : A.Words Pins)
    (h : (P.run rem A).plan.History) (N : Forest F L.ports.form) (seed : ∀ v, Tree.Within 4 (N v))
    (v : ((P.run rem A).plan.finish h).Site) :
    Tree.Within (4+P.length) (((P.run rem A).plan.assemble h ((P.assembly rem A : (P.run rem A).Assembler Pins) L) N).2 v) := by
  rw [← program_stage_count P rem A h]
  exact (P.run rem A).plan.within_finish h ((P.assembly rem A : (P.run rem A).Assembler Pins) L) N 4 4
    (program_kernels P rem A L h) le_rfl seed v

/-- An initial array of evaluated network atoms needs no separate seed-depth
assumption. This is the form used by the issued native trace seed. -/
theorem terminal_atomic_within {s : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) (P.charge+rem)) (L : A.Words Pins)
    (h : (P.run rem A).plan.History) (N : ∀ v, BitNetwork F (L.ports.form.width v))
    (v : ((P.run rem A).plan.finish h).Site) :
    Tree.Within (4+P.length)
      (((P.run rem A).plan.assemble h ((P.assembly rem A : (P.run rem A).Assembler Pins) L) (fun z => Tree.atom (N z))).2 v) :=
  terminal_factor_within P rem A L h _ (fun z => Tree.Within.atom 4 (N z)) v

end Hierarchy.TraceDistribution.Physical

end
end OAI
