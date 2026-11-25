import OAI.Hierarchy.DescentOrdinaryMouthMeasured

namespace OAI
/-! Recover the exact mouth printed at an authentic one-based source ordinal, including
when adjacent lanes choose different old hosts and the group number changes. -/
namespace Hierarchy.DescentOrdinaryMouthReturn
open DescentOrdinaryOriginMask DescentOrdinaryBorn DescentSIMDLookup DescentOrdinaryAtomFieldRAM
open DescentPackedColony DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section

theorem live_of_stamp {N K b} (mask : Cell (1*N)) (n : Fin K) (j : Fin N) (room : N<2^b)
    (read : ((encode b K).symm (selection N K b mask) n).val=j.val+1) :
    (encode 1 N).symm mask j≠0 ∧ DescentPackedLocalAtoms.earlier ((encode 1 N).symm mask) j=n.val :=by
  rw [selection,Equiv.symm_apply_apply] at read
  by_cases seen : ∃i,(encode 1 N).symm mask i≠0 ∧ DescentPackedLocalAtoms.earlier ((encode 1 N).symm mask) i=n.val
  · have eqn:=stamp_at N K b mask n seen.choose seen.choose_spec.1 seen.choose_spec.2 room
    rw [selection,Equiv.symm_apply_apply] at eqn
    have same : seen.choose=j:=Fin.ext (by omega)
    exact same ▸ seen.choose_spec
  · rw [selected_none N K b mask n seen] at read
    change 0=j.val+1 at read
    omega

namespace Layout
variable (L : Layout)

/-- The semantic output word observed in the real returned memory by 'Layout.issued'.
Both the old group and the old host are recovered at the public receiving block coordinate. -/
theorem received_born {nb mb b} (V : Fin L.B.args→Fin L.lows→L.Val nb mb)
    (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits) (same : L.B.groups=L.groups*L.radix)
    (arg : Fin L.B.args) (f : Fin 3) (block : Fin L.radix) (h : Fin (L.B.hosts*L.lows)) (g : Fin L.groups)
    (donor : Fin L.B.hosts) (walk : Fin (breadth L.degree)) (x : Fin (2^L.depth)) (seat : Fin L.B.cap) (party : Fin 6)
    (node : Fin L.newNodes) :
    let origin:=finProdFinEquiv.symm h
    let group:=(finProdFinEquiv (g,block)).cast same.symm
    let n:=DescentPackedActorMask.nodes (breadth L.degree*2^L.depth) L.oldNodes L.B.cap
    let mask:=marked (V arg origin.2) origin.1 group
    let i : Fin n:=finProdFinEquiv (finProdFinEquiv (walk,x),finSumFinEquiv (.inr (finProdFinEquiv (seat,party))))
    n<2^b → DescentSortedRoster.indexed (V arg origin.2).walks origin.1 walk=some donor →
    ((encode b L.newNodes).symm (selection n L.newNodes b mask) node).val=i.val+1 →
    (encode L.B.bits L.newNodes).symm (DescentScalarBookReshape.book (fun l old group'=>
      (L.vals V chip (finProdFinEquiv (arg,f)) l).book L.newNodes old (group'.cast same.symm)) block h g) node=
      RolePorts.value L.B.bits (pointerAt L.B.demand L.B.grain L.B.scale
        (chipDonor L.B.format (chip donor group) (finProdFinEquiv (x.cast L.blocks_eq.symm,seat))) party arg.val) f :=by
  intro origin group n mask i room hit word
  have active:=live_of_stamp mask node i room word
  exact L.born_value V chip arg f origin.2 origin.1 donor group walk x seat party node hit active.1 active.2

end Layout
end
end Hierarchy.DescentOrdinaryMouthReturn

end OAI
