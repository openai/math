import OAI.Hierarchy.DescentRegisteredOperandReshape
import OAI.Hierarchy.DescentOrdinaryOriginMask
import OAI.Hierarchy.DescentOrdinaryFinalLaw
import OAI.Hierarchy.DescentRetainedRangeDigits

namespace OAI
/-! # Actual ordinary compaction keeps the original range on the same marked candidate -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentDatedPriorOperand DescentDatedPriorOperand.OrdinaryBooks DescentOperandStateBanks
open DescentPackedLocalAtoms DescentHaloWalkRAM DescentPackedActorMask
open scoped Classical Fin.CommRing
noncomputable section
variable {a b N K : ℕ}

/-- The one-based physical origin and every payload column use the identical stable mask. -/
theorem packed_at_stamp (mask : Cell (1*N)) (node : Fin K) (source : Fin N) (wide : N<2^b)
    (stamp : ((encode b K).symm (DescentOrdinaryOriginMask.selection N K b mask) node).val=source.val+1)
    (fields : Fin N→Cell a) :
    take node (pack a N K mask (encode a N fields))=fields source := by
  let flags:=(encode 1 N).symm mask
  by_cases found : ∃d,flags d≠0 ∧ earlier flags d=node.val
  · obtain ⟨d,marked,pos⟩:=found
    have same:=DescentOrdinaryOriginMask.stamp_at N K b mask node d marked pos wide
    have deq : d=source:=Fin.ext (by omega)
    subst d
    simpa only [take,pack,Equiv.symm_apply_apply] using field_at flags fields source marked node pos
  · have blank:=DescentOrdinaryOriginMask.selected_none N K b mask node found
    simp only [DescentOrdinaryOriginMask.selection,Equiv.symm_apply_apply,blank,Fin.val_zero] at stamp
    omega

variable {degree k K₀ cap H G J Q fields width nb mb : ℕ}
variable (old : Pages fields→Fin (2^k)→Fin H→Fin G→Cell (width*K₀))
    (born : Pages fields→Fin (2^k)→Fin cap→Fin 6→Fin H→Fin G→Cell width)
    (geom : Fin Q→Values degree k K₀ cap H G width nb mb)
    (name : Fin (J*2^k)→Fin G) (bl : Fin (2^k)) (h₁ : Fin (H*Q)) (g₁ : Fin J)

private abbrev originMask (v : Values degree k K₀ cap H G width nb mb) (h : Fin H) (g : Fin G) :=
  let donors := breadth degree * 2^k
  occupied donors K₀ cap mb
    (target nb (actors donors cap) (v.wanted h g) (encode nb (actors donors cap) (v.venues h g)))
    (encode mb donors (v.counts h g))

/-- The donor address, old physical block and local index are exactly those yielded by
`PaddedOrigin.origin_operands`. The unknown contents of any new node are irrelevant. -/
theorem raster_old (source : Fin (nodes (breadth degree * 2^k) K₀ cap)) (slot : Fin K) (saved : Fin H)
    (prior : Fin K₀) (wide : nodes (breadth degree * 2^k) K₀ cap < 2^b)
    (stamp : ((encode b K).symm (DescentOrdinaryOriginMask.selection _ K b
      (originMask (geom (finProdFinEquiv.symm h₁).2) (finProdFinEquiv.symm h₁).1
        (name (finProdFinEquiv (g₁,bl))))) slot).val=source.val+1)
    (route : DescentSortedRoster.indexed (geom (finProdFinEquiv.symm h₁).2).walks
      (finProdFinEquiv.symm h₁).1 (bookRoot degree k K₀ cap source)=some saved)
    (node : finSumFinEquiv.symm (bookItem degree k K₀ cap source)=Sum.inl prior) (p : Pages fields) :
    take slot (raster (K':=K) (inputs old born geom) name p bl h₁ g₁)=
      take prior (old p (bookBlock degree k K₀ cap source) saved (name (finProdFinEquiv (g₁,bl)))) := by
  simp only [raster, DescentScalarBookReshape.book, Values.book, inputs]
  apply Eq.trans (packed_at_stamp (a := width) _ slot source wide stamp _)
  simp only [route, Option.elim_some, item, node, Sum.elim_inl]

/-- The third actual input to the final registered scalar gate is the gathered span plane.
The two ballot inputs still determine activity on the occupied physical row. -/
theorem final_span (B : DescentOrdinaryFinal.Chart) (arg : Fin B.layout.operands)
    (node : Fin B.layout.nodes) (x : B.Input) (active : B.live x (B.slots (node,arg))) (f : Fin 3) :
    digit B.field node.val (B.law (B.pages (page f,arg)) x).val=
      digit B.field node.val (x (B.columns (.inl 2))).val :=
  B.span (page f) (by change 4≤4+f.val;omega) arg node x active

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
