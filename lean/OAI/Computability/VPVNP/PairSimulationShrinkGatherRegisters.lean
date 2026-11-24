import OAI.Computability.VPVNP.PairSimulationShrinkGatherImage

/-!
# Register separation in the hosted shrinking map segment

The combined register enumeration gives independent locations to the site
header, private matrix evaluator, each operand gather and the layout scratch.
Only the host's disjointness from DFS and saved registers is needed below.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open Compression.ShrinkMotif MotifGrid MotifBlocks MotifConversion

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {t shared r : ℕ} (F : MapHandlerImage.Family B t shared) (G : ShrinkGatherBank.Family F)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
  (locals : Fin (Nat.card (GatherRegister F G)) ↪ Fin r)
  (dfsApart : ∀ x j, locals x ≠ dfs j) (savedApart : ∀ x j, locals x ≠ saved j)

private theorem local_ne {x y : GatherRegister F G} (h : x ≠ y) :
    locals (gatherRegisters F G x) ≠ locals (gatherRegisters F G y) :=
  locals.injective.ne ((gatherRegisters F G).injective.ne h)

include dfsApart savedApart in
/-- Both native code families receive their true disjoint register bank. -/
theorem hosted_banks :
    F.Apart dfs saved ((gatherShared F G).trans locals) ((gatherMatrix F G).trans locals) ∧
    G.Apart dfs saved ((gatherShared F G).trans locals) ((gatherLocal F G).trans locals) ∧
    (∀ i, ((gatherShared F G).trans locals) i ≠ locals (layoutTemp F G)) := by
  refine ⟨⟨fun _ _ ↦ dfsApart _ _, fun _ _ ↦ savedApart _ _, ?_⟩,
    ⟨fun _ _ ↦ dfsApart _ _, fun _ _ ↦ savedApart _ _, ?_⟩, ?_⟩
  · intro x j
    exact local_ne F G locals (x := .inr (.inl x)) (y := .inl j) (by simp)
  · intro x j
    exact local_ne F G locals (x := .inr (.inr (.inl x))) (y := .inl j) (by simp)
  · intro j
    exact local_ne F G locals (x := .inl j) (y := .inr (.inr (.inr ()))) (by simp)

variable (S : Registers shared) (common : Fin shared ↪ Fin r) (tmp : Fin r)

/-- The item reader writes the motif, party, term pointer and grid, and the
layout and ordinal branches use two further scratch registers. -/
def Protected (q : Fin r) : Prop := q ≠ tmp ∧ q ≠ common S.zero ∧
  ∀ l : Fin 11, 6 ≤ l.val → l.val ≤ 9 → q ≠ (S.headerReg common) l

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
