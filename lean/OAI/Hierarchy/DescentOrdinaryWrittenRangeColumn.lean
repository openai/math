import OAI.Hierarchy.DescentOrdinaryTransposeValue
import OAI.Hierarchy.DescentDatedPreviousPageValue

namespace OAI
/-! # The integer in an ordinary operand column after its native host and group transpose -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup
noncomputable section
variable {D k K cap H G G' a a' nb mb : ℕ}

/-- Cast only the width and public group type of a numerical book. -/
def Values.reindex (groups : G=G') (width : a=a') (v : Values D k K cap H G a nb mb) :
    Values D k K cap H G' a' nb mb := by
  cases groups
  cases width
  exact v

theorem Values.Prefix.reindex {H' : ℕ} {fits : H≤H'} {v : Values D k K cap H G a nb mb}
    {v' : Values D k K cap H' G a nb mb} (r : Values.Prefix fits v v')
    (groups : G=G') (width : a=a') :
    Values.Prefix fits (v.reindex groups width) (v'.reindex groups width) :=by
  cases groups
  cases width
  exact r

theorem Values.reindex_book (groups : G=G') (width : a=a') (v : Values D k K cap H G a nb mb)
    (nodes : ℕ) (h : Fin H) (g : Fin G') :
    ((v.reindex groups width).book nodes h g).val=(v.book nodes h (g.cast groups.symm)).val :=by
  cases groups
  cases width
  rfl

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedPriorOperand DescentOperandVectorArena DescentOperandStateBanks DescentSIMDLookup DescentPackedZip
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryRasterReturn DescentScalarBookReshape
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (shape : v.VectorShape)
    {D k K cap nb mb H Q G R width : ℕ}
local notation "L₀" => v.resolver
local notation "A₀" => v.vector
variable (V : References.Rows v.vector D k K cap (v.resolver.size+2) nb mb)
    (fits : H≤v.vector.hosts)
    (small : Fin v.vector.lows→Values D k K cap H (v.vector.groups*v.vector.radix) (v.resolver.size+2) nb mb)

/-- On the actual previous-bank wire, the public transposition performs one direct lookup
in the unpadded gathered book. In particular the output integer is independent of any
data in the extra host rows of the physical rectangle. -/
theorem previous_range_column (pitch : (A₀).lows=Q) (groups : (A₀).groups=G) (radix : (A₀).radix=R)
    (rows : Fin Q→Fin H→Fin (G*R)→Cell width)
    (read : ∀l h g,((small l).book (L₀).nodes h g).val=
      (rows (l.cast pitch) h (g.cast (congrArg₂ (·*·) groups radix))).val)
    (p : Pages (L₀).operands) (block : Fin (L₀).blocks) (host : Fin (H*Q)) (group_ : Fin G)
    (resident : ∀l,Values.Prefix fits (small l) (V (p.cast (congrArg (7*·) shape.operands)) l)) :
    (previousValues L₀ A₀ shape.operands shape.blocks shape.hosts shape.groups
      (References.returnedValue A₀ V (L₀).nodes) p block
        ((widen fits (host.cast (congrArg (H*·) pitch.symm))).cast shape.hosts.symm)
        (group_.cast (shape.groups.trans groups).symm)).val=
      (DescentScalarBookReshape.book rows ((block.cast shape.blocks).cast radix) host group_).val :=by
  rw [v.previous_page_at shape V fits small p block _ _ resident]
  exact book_val_cast pitch groups radix _ rows read _ host group_

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
