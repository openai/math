import OAI.Hierarchy.DescentOrdinaryMouthStamp

namespace OAI
/-! # Empty and missing rows of the physically returned newborn mouth fields -/
namespace Hierarchy.DescentOrdinaryMouthReturn
open DescentOrdinaryOriginMask DescentSIMDLookup DescentOrdinaryAtomFieldRAM
open DescentPackedColony DescentHaloWalkRAM DescentPackedActorMask
open scoped Classical Fin.CommRing
noncomputable section

/-- A zero donor stamp leaves no selected source ordinal at that output position.
The bound makes every real one-based ordinal strictly positive in the stored word. -/
theorem empty_of_stamp {N K b} (mask : Cell (1*N)) (n : Fin K) (room : N<2^b)
    (empty : ((encode b K).symm (selection N K b mask) n).val=0) :
    ¬∃j,(encode 1 N).symm mask j≠0 ∧ DescentPackedLocalAtoms.earlier ((encode 1 N).symm mask) j=n.val :=by
  rintro ⟨j,keep,rk⟩
  have seen:=stamp_at N K b mask n j keep rk room
  omega

namespace Layout
variable (L : Layout)
local notation "Nₒ" => nodes (breadth L.degree*2^L.depth) L.oldNodes L.B.cap

/-- Every role coordinate is zero at an unused chronological node, for all argument
ordinals. The physical condition is the value of the separately returned W stamp. -/
theorem received_empty {nb mb b} (V : Fin L.B.args→Fin L.lows→L.Val nb mb)
    (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits) (same : L.B.groups=L.groups*L.radix)
    (arg : Fin L.B.args) (f : Fin 3) (block : Fin L.radix) (h : Fin (L.B.hosts*L.lows))
    (g : Fin L.groups) (node : Fin L.newNodes) :
    let origin:=finProdFinEquiv.symm h
    let group:=(finProdFinEquiv (g,block)).cast same.symm
    let mask:=marked (V arg origin.2) origin.1 group
    Nₒ<2^b → ((encode b L.newNodes).symm (selection Nₒ L.newNodes b mask) node).val=0 →
    (encode L.B.bits L.newNodes).symm (DescentScalarBookReshape.book (fun l old group'=>
      (L.vals V chip (finProdFinEquiv (arg,f)) l).book L.newNodes old (group'.cast same.symm)) block h g) node=0 :=by
  intro origin group mask room absent
  have unused:=empty_of_stamp mask node room absent
  let val:=L.vals V chip (finProdFinEquiv (arg,f)) origin.2
  change (encode L.B.bits L.newNodes).symm (val.book L.newNodes origin.1 group) node=0
  unfold ScalarOperand.Values.book DescentPackedLocalAtoms.pack
  simp only [Equiv.symm_apply_apply]
  unfold DescentPackedLocalAtoms.field
  apply dite_eq_right
  simpa only [val,vals,Equiv.symm_apply_apply,mask,marked] using unused

/-- A selected ordinal with no earlier host has the zero scalar given by the
original kept-row gather, even when its lane's other ordinals have live hosts. -/
theorem received_missing {nb mb b} (V : Fin L.B.args→Fin L.lows→L.Val nb mb)
    (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits) (same : L.B.groups=L.groups*L.radix)
    (arg : Fin L.B.args) (f : Fin 3) (block : Fin L.radix) (h : Fin (L.B.hosts*L.lows))
    (g : Fin L.groups) (node : Fin L.newNodes) (j : Fin Nₒ) :
    let origin:=finProdFinEquiv.symm h
    let group:=(finProdFinEquiv (g,block)).cast same.symm
    let mask:=marked (V arg origin.2) origin.1 group
    Nₒ<2^b → ((encode b L.newNodes).symm (selection Nₒ L.newNodes b mask) node).val=j.val+1 →
    DescentSortedRoster.indexed (V arg origin.2).walks origin.1 (bookRoot L.degree L.depth L.oldNodes L.B.cap j)=none →
    (encode L.B.bits L.newNodes).symm (DescentScalarBookReshape.book (fun l old group'=>
      (L.vals V chip (finProdFinEquiv (arg,f)) l).book L.newNodes old (group'.cast same.symm)) block h g) node=0 :=by
  intro origin group mask room word missing
  have live:=live_of_stamp mask node j room word
  let val:=L.vals V chip (finProdFinEquiv (arg,f)) origin.2
  change (encode L.B.bits L.newNodes).symm (val.book L.newNodes origin.1 group) node=0
  unfold ScalarOperand.Values.book DescentPackedLocalAtoms.pack
  simp only [Equiv.symm_apply_apply]
  rw [DescentPackedLocalAtoms.field_at _ _ j (by simpa [val,vals,mask,marked] using live.1)
    node (by simpa [val,vals,mask,marked] using live.2)]
  simp [val,vals,missing]

end Layout
end
end Hierarchy.DescentOrdinaryMouthReturn

end OAI
