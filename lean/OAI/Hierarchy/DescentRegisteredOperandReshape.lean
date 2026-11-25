import OAI.Hierarchy.DescentCompactedOperandHeaders
import OAI.Hierarchy.DescentGatheredVectorReshape

namespace OAI
/-! # The seven-field normal form at every padded numerical receiver address -/
namespace Hierarchy.DescentDatedPriorOperand.OrdinaryBooks
open DescentPackedColony DescentPackedZip DescentOperandStateBanks DescentSIMDLookup
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D k K cap H G J Q a nb mb count K' : ℕ}
local notation "P" => Pages count
local notation "FieldInputs" => Values D k K cap H G a nb mb
/-- Every field uses the same physical geometry. Thus a single selection
of an old node, a fresh birth or padding serves the complete seven-field row. -/
def inputs
    (old : P→Fin (2^k)→Fin H→Fin G→Cell (a*K))
    (born : P→Fin (2^k)→Fin cap→Fin 6→Fin H→Fin G→Cell a)
    (geom : Fin Q→FieldInputs) (p : P) (l : Fin Q) : FieldInputs :=
  {geom l with old:=old p,born:=born p}

def raster (V : P→Fin Q→FieldInputs) (name : Fin (J*2^k)→Fin G) (p : P) (b : Fin (2^k)) :=
  DescentScalarBookReshape.book (fun l h g=>(V p l).book K' h (name g)) b

private theorem item_typed
    (old : P→Fin (2^k)→Fin H→Fin G→Cell (a*K))
    (born : P→Fin (2^k)→Fin cap→Fin 6→Fin H→Fin G→Cell a)
    (hasOld : ∀b h g arg node,TypedHeader (fun f=>take node (old (DescentPriorOperandColumns.pageOf arg f) b h g)))
    (hasBirth : ∀b c s h g arg,TypedHeader (fun f=>born (DescentPriorOperandColumns.pageOf arg f) b c s h g))
    (arg : Fin count) (b : Fin (2^k)) (j : Fin (K+cap*6)) (h : Fin H) (g : Fin G) :
    TypedHeader (fun f=>item (old (DescentPriorOperandColumns.pageOf arg f))
      (born (DescentPriorOperandColumns.pageOf arg f)) b j h g) := by
  unfold item
  cases finSumFinEquiv.symm j with
  | inl node => exact hasOld b h g arg node
  | inr site => exact hasBirth b _ _ h g arg

set_option maxHeartbeats 1000000 in
theorem raster_typed
    (old : P→Fin (2^k)→Fin H→Fin G→Cell (a*K))
    (born : P→Fin (2^k)→Fin cap→Fin 6→Fin H→Fin G→Cell a)
    (geom : Fin Q→FieldInputs) (name : Fin (J*2^k)→Fin G)
    (hasOld : ∀b h g arg node,TypedHeader (fun f=>take node (old (DescentPriorOperandColumns.pageOf arg f) b h g)))
    (hasBirth : ∀b c s h g arg,TypedHeader (fun f=>born (DescentPriorOperandColumns.pageOf arg f) b c s h g))
    (b : Fin (2^k)) (h₁ : Fin (H*Q)) (g₁ : Fin J) (arg : Fin count) (node : Fin K') :
    TypedHeader (fun f=>take node (raster (inputs old born geom) name (DescentPriorOperandColumns.pageOf arg f) b h₁ g₁)) := by
  let donors := breadth D * 2^k
  let actors := DescentPackedActorMask.actors donors cap
  let entries := DescentPackedActorMask.nodes donors K cap
  let l : Fin Q := (finProdFinEquiv.symm h₁ : Fin H × Fin Q).2
  let h : Fin H := (finProdFinEquiv.symm h₁ : Fin H × Fin Q).1
  let g := name (finProdFinEquiv (g₁,b))
  let mask : Cell (1*entries) := DescentPackedActorMask.occupied donors K cap mb
    (DescentPackedActorMask.target nb actors ((geom l).wanted h g)
      (encode nb actors ((geom l).venues h g))) (encode mb donors ((geom l).counts h g))
  let records : Fin 4 → Fin entries → Cell a := fun f j =>
    (DescentSortedRoster.indexed (geom l).walks h (bookRoot D k K cap j)).elim 0
      (fun u => item (old (DescentPriorOperandColumns.pageOf arg f))
        (born (DescentPriorOperandColumns.pageOf arg f))
        (bookBlock D k K cap j) (bookItem D k K cap j) u g)
  have typed (j : Fin entries) : TypedHeader (fun f => records f j) := by
    cases e : DescentSortedRoster.indexed (geom l).walks h (bookRoot D k K cap j) with
    | none => simpa only [records,e,Option.elim_none] using (typed_zero (width:=a))
    | some u => simpa only [records,e,Option.elim_some] using
        item_typed old born hasOld hasBirth arg (bookBlock D k K cap j) (bookItem D k K cap j) u g
  exact typed_packed (width:=a) (count:=entries) (output:=K') mask records typed node

/-- These books occupy exactly the full rectangular destinations of
`DescentGatheredVectorReshape.run`. Their header invariant feeds the next
date's original `registered_books` with no conditions on holes or node count. -/
theorem registered_result
    (size lanes : ℕ)
    (old : P→Fin (2^k)→Fin H→Fin G→Cell ((size+2)*K))
    (born : P→Fin (2^k)→Fin cap→Fin 6→Fin H→Fin G→Cell (size+2))
    (geom : Fin Q→Values D k K cap H G (size+2) nb mb) (name : Fin (J*2^k)→Fin G)
    (hasOld : ∀b h g arg node,TypedHeader (fun f=>take node (old (DescentPriorOperandColumns.pageOf arg f) b h g)))
    (hasBirth : ∀b c s h g arg,TypedHeader (fun f=>born (DescentPriorOperandColumns.pageOf arg f) b c s h g)) :
    let l : Layout:=⟨2^k,K',count,H*Q,J,lanes,size⟩
    BookPointers (l:=l) (fun b p=>raster (K':=K') (inputs old born geom) name p b) := by
  intro l
  exact (books_typed_iff _).2 (fun b node arg h g => raster_typed old born geom name hasOld hasBirth b h g arg node)

end
end Hierarchy.DescentDatedPriorOperand.OrdinaryBooks

end OAI
