import OAI.Hierarchy.DescentDatedRegisteredHeaders
import OAI.Hierarchy.DescentOrdinaryRangeHostPadding
import OAI.Hierarchy.DescentDatedTicketOriginRows

namespace OAI
/-! # The origin sampled at a genuine unpadded old host and returned W job -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentOrdinaryOriginMask DescentOrdinaryRasterReturn
noncomputable section
variable {D k K cap H H' G a nb mb Q r : ℕ} {wide : H≤H'}
theorem Values.Prefix.issued_selection
    {v : Fin Q→Values D k K cap H (G*r) a nb mb} {v' : Fin Q→Values D k K cap H' (G*r) a nb mb}
    (p : ∀q,Values.Prefix wide (v q) (v' q)) (nodes b : ℕ)
    (block : Fin r) (h : Fin (H*Q)) (g : Fin G) :
    DescentScalarBookReshape.book (fun l h g=>selection _ nodes b (marked (v' l) h g)) block (widen wide h) g =
      DescentScalarBookReshape.book (fun l h g=>selection _ nodes b (marked (v l) h g)) block h g :=by
  unfold DescentScalarBookReshape.book
  rw [endpoints wide h]
  simp only [marked,(p _).wanted,(p _).venues,(p _).counts]
end
end Hierarchy.DescentOrdinaryAtomFieldRAM.ScalarOperand

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentDatedOperandReadPipeline DescentOrdinaryOriginMask DescentOrdinaryOriginPorts
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryRasterReturn
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (shape : v.VectorShape)
variable {H d nb mb : ℕ} (large : v.OriginalDonors d nb mb) (wide : H≤v.vector.hosts)
variable (small : Fin v.vector.lows→Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
  H (v.vector.groups*v.vector.radix) d nb mb)
theorem registered_origin_at (resident : ∀l,Values.Prefix wide (small l) (large l))
    (j : Fin v.resolver.jobs) (h : Fin (H*v.vector.lows)) (g : Fin v.resolver.groups) (f : Fin 6) :
    v.originHeaderValue shape large j f ((widen wide h).cast shape.hosts.symm) g=
      readLaw v.originChart v.operandShortBits ((v.resolver.index.symm j).2.1) f
        (DescentScalarBookReshape.book (fun l h g=>selection v.originCandidates v.resolver.nodes v.originBits (marked (small l) h g))
          ((v.resolver.index.symm j).1.cast shape.blocks) h (g.cast shape.groups)) :=by
  change readLaw _ _ _ _ (DescentScalarBookReshape.book _ _ (((widen wide h).cast shape.hosts.symm).cast shape.hosts) _)=_
  simp only [Fin.cast_cast,Fin.cast_refl]
  exact congrArg (readLaw v.originChart v.operandShortBits _ f) (Values.Prefix.issued_selection resident _ _ _ _ _)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
