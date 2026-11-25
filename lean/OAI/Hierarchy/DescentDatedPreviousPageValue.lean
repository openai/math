import OAI.Hierarchy.DescentOrdinaryRangeHostPadding
import OAI.Hierarchy.DescentDatedPreviousHeaderWords

namespace OAI
/-! A real word of the four operand headers or three retained spans at the reached host. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentDatedPriorOperand DescentOperandVectorArena DescentOperandStateBanks
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryRasterReturn
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (shape : v.VectorShape)
    {D k K cap nb mb H : ℕ}

variable (V : References.Rows v.vector D k K cap (v.resolver.size+2) nb mb)
    (fits : H ≤ v.vector.hosts)
    (small : Fin v.vector.lows → Values D k K cap H (v.vector.groups*v.vector.radix) (v.resolver.size+2) nb mb)

theorem previous_page_at (p : Pages v.resolver.operands) (x : Fin v.resolver.blocks)
    (h : Fin (H*v.vector.lows)) (g : Fin v.resolver.groups)
    (resident : ∀ l, Values.Prefix fits (small l) (V (p.cast (congrArg (7*·) shape.operands)) l)) :
    previousValues v.resolver v.vector shape.operands shape.blocks shape.hosts shape.groups
      (References.returnedValue v.vector V v.resolver.nodes) p x
      ((widen fits h).cast shape.hosts.symm) g =
      DescentScalarBookReshape.book (fun l h g => (small l).book v.resolver.nodes h g)
        (x.cast shape.blocks) h (g.cast shape.groups) := by
  exact Values.Prefix.returned resident v.resolver.nodes (x.cast shape.blocks) h (g.cast shape.groups)

theorem previous_header_at (j : Fin v.resolver.jobs) (f : Fin 4) (h : Fin (H*v.vector.lows)) (g : Fin v.resolver.groups)
    (resident : ∀ l, Values.Prefix fits (small l) (V
      ((page (f.castLE (by decide : 4≤7)) (v.resolver.index.symm j).2.2).cast (congrArg (7*·) shape.operands)) l)) :
    v.previousHeaderValue shape V j f ((widen fits h).cast shape.hosts.symm) g =
      DescentScalarBookReshape.book (fun l h g => (small l).book v.resolver.nodes h g)
        ((v.resolver.index.symm j).1.cast shape.blocks) h (g.cast shape.groups) := by
  exact v.previous_page_at shape V fits small _ _ h g resident

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
