import OAI.Hierarchy.DescentOrdinaryMouthPadding
import OAI.Hierarchy.DescentOrdinaryOriginPorts

namespace OAI
/-! # Uniform bound for the active mouth role of every returned ordinary job -/
namespace Hierarchy.DescentOrdinaryOriginPorts
open DescentSIMDLookup DescentOrdinaryOriginMask DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- Tag two is issued only for an ordinal in the newborn part of the original W row. -/
theorem birth_index_from_tag (R : Return) (d : ℕ) (node : Fin R.newNodes) (word : Cell (R.ordinalBits*R.newNodes))
    (tag : (readLaw R d node 0 word).val=2) :
    ∃(p : Fin (breadth R.degree)) (x : Fin (2^R.depth)) (seat : Fin R.capacity) (party : Fin 6),
      ((encode R.ordinalBits R.newNodes).symm word node).val=(candidate R p x (.inr (seat,party))).val+1 := by
  let stamp:=((encode R.ordinalBits R.newNodes).symm word node).val
  by_cases within : 0<stamp ∧ stamp≤extent R
  · let i : Fin (extent R):=⟨stamp-1,by omega⟩
    have stampAt : stamp=i.val+1:=by change stamp=stamp-1+1; omega
    have flag : ((tuple R i 0:ℕ):Cell d).val=2 :=by
      rw [at_stamp R d node 0 word i stampAt] at tag
      exact tag
    obtain ⟨⟨region,item⟩,back⟩:=(finProdFinEquiv (m:=breadth R.degree*2^R.depth)
      (n:=R.oldNodes+R.capacity*6)).surjective i
    rw [←back] at flag stampAt
    obtain ⟨⟨p,x⟩,rfl⟩:=(finProdFinEquiv (m:=breadth R.degree) (n:=2^R.depth)).surjective region
    obtain ⟨item,rfl⟩:=(finSumFinEquiv (m:=R.oldNodes) (n:=R.capacity*6)).surjective item
    rcases item with old | fresh
    · change ((tuple R (candidate R p x (.inl old)) 0:ℕ):Cell d).val=2 at flag
      rw [tuple_old] at flag
      change 1%(2^d)=2 at flag
      have small:=Nat.mod_le 1 (2^d)
      omega
    · obtain ⟨⟨seat,party⟩,rfl⟩:=(finProdFinEquiv (m:=R.capacity) (n:=6)).surjective fresh
      exact ⟨p,x,seat,party,stampAt⟩
  · have empty : readLaw R d node 0 word=0:=by
      change (if yes : 0<stamp ∧ stamp≤extent R then _ else _)=_
      exact dite_eq_right within
    rw [empty] at tag
    change 0=2 at tag
    omega

end
end Hierarchy.DescentOrdinaryOriginPorts

namespace Hierarchy.DescentOrdinaryMouthReturn.Layout
open DescentOrdinaryOriginMask DescentOrdinaryBorn DescentSIMDLookup DescentOrdinaryAtomFieldRAM
open DescentPackedColony DescentHaloWalkRAM DescentOrdinaryOriginPorts DescentPackedActorMask
open scoped Classical Fin.CommRing
noncomputable section

def stampLayout (L : Layout) (b : ℕ) : Return :=
  ⟨L.degree,L.depth,L.oldNodes,L.B.cap,L.newNodes,b,L.B.hosts,L.lows,L.groups,L.radix,L.lanes⟩

/-- This bound includes the absent primitive mouth and requires no payload width. -/
theorem role_value_bounded (bits : ℕ) (mouth : Option Mouth) : (RolePorts.value bits mouth 1).val≤10 := by
  cases mouth with
  | none=>change 0≤10; decide
  | some m=>
    change m.rawRole%(2^bits)≤10
    exact (Nat.mod_le ..).trans (Nat.le_of_lt_succ (RolePorts.raw_bounded m))

/-- Every active W birth reads its role from the actual selected donor, or reads
the physical zero row when no donor is present. Retained jobs use the other ticket branch. -/
theorem guarded_role_bound (L : Layout) {nb mb b : ℕ} (V : Fin L.B.args→Fin L.lows→L.Val nb mb)
    (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits) (same : L.B.groups=L.groups*L.radix)
    (arg : Fin L.B.args) (block : Fin L.radix) (h : Fin (L.B.hosts*L.lows)) (g : Fin L.groups)
    (node : Fin L.newNodes) (width : ℕ) :
    let R:=stampLayout L b
    let home:=finProdFinEquiv.symm h
    let group:=(finProdFinEquiv (g,block)).cast same.symm
    let mask:=marked (V arg home.2) home.1 group
    let stamp:=selection (extent R) L.newNodes b mask
    extent R<2^b → (readLaw R width node 0 stamp).val=2 →
      ((encode L.B.bits L.newNodes).symm (DescentScalarBookReshape.book (fun l old group'=>
        (L.vals V chip (finProdFinEquiv (arg,(1:Fin 3))) l).book L.newNodes old (group'.cast same.symm)) block h g) node).val≤10 := by
  intro R home group mask stamp room tag
  obtain ⟨walk,x,seat,party,word⟩:=birth_index_from_tag R width node stamp tag
  cases distant : DescentSortedRoster.indexed (V arg home.2).walks home.1 walk with
  | none=>
    have missing : DescentSortedRoster.indexed (V arg home.2).walks home.1
        (bookRoot L.degree L.depth L.oldNodes L.B.cap (candidate R walk x (.inr (seat,party))))=none :=by
      let pair : Fin (breadth L.degree * 2^L.depth) := finProdFinEquiv (walk,x)
      let slot : Fin (L.oldNodes+L.B.cap*6) := finSumFinEquiv (Sum.inr (finProdFinEquiv (seat,party)))
      have split := finProdFinEquiv.symm_apply_apply (pair,slot)
      have start := finProdFinEquiv.symm_apply_apply (walk,x)
      change DescentSortedRoster.indexed (V arg home.2).walks home.1
        (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv (pair,slot))).1).1 = none
      rw [split]
      change DescentSortedRoster.indexed (V arg home.2).walks home.1 (finProdFinEquiv.symm (finProdFinEquiv (walk,x))).1 = none
      rw [start]
      exact distant
    rw [L.received_missing V chip same arg 1 block h g node (candidate R walk x (.inr (seat,party))) room word missing]
    exact Nat.zero_le _
  | some donor=>
    rw [L.received_born V chip same arg 1 block h g donor walk x seat party node room distant word]
    exact role_value_bounded _ _

end
end Hierarchy.DescentOrdinaryMouthReturn.Layout

end OAI
