import OAI.Hierarchy.DescentOrdinaryRoleControlPrice
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Address size of the original ordinary population and request arrays -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout
open DescentDatedAddressBook DescentSIMDLookup Filter
variable {ι : ℕ→Type*}
structure ScalarRoom (L : ∀h,ι h→RoleControl.Layout) where
  hosts : Bounded (fun h i=>(L h i).hosts)
  groups : Bounded (fun h i=>(L h i).groups)
  lanes : Bounded (fun h i=>(L h i).lanes)
  donors : Bounded (fun h i=>(L h i).donors)
  sites : Bounded (fun h i=>(L h i).sites)
  keys : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let l:=L h i
    (l.roleBits*l.nodes)*l.lanes≤K*h ∧ (l.countBits*l.donors+l.countBits)*l.lanes≤K*h

theorem bounded_extent (L : ∀h,ι h→RoleControl.Layout) (room : ScalarRoom L) :
    Bounded (fun h i=>(L h i).volume+2^(L h i).outBits) := by
  obtain ⟨K,fit⟩:=room.keys
  have one : Bounded (ι:=ι) (fun _ _=>1):=Bounded.const 1
  have two : Bounded (ι:=ι) (fun _ _=>2):=Bounded.const 2
  have batch : Bounded (fun h i=>chunks (L h i).groups (L h i).lanes):=
    (room.groups.add room.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have out_ : Bounded (fun h i=>2^(L h i).outBits) := ((room.hosts.mul batch).add one).padded
  have chunk_ : Bounded (fun h i=>2^(L h i).chunkBits) := (batch.add one).padded
  have raw:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).1)
  have set_:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2)
  have width_ : Bounded (fun h i=>2^(L h i).width):=by
    apply ((raw.add set_).add chunk_).of_le
    intro h i
    dsimp only [width]
    set a:=(L h i).roleBits*(L h i).nodes*(L h i).lanes
    set b:=((L h i).countBits*(L h i).donors+(L h i).countBits)*(L h i).lanes
    set c:=(L h i).chunkBits
    have a_le : 2^a ≤ (2^a + 2^b) + 2^c := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
    have b_le : 2^b ≤ (2^a + 2^b) + 2^c := (Nat.le_add_left ..).trans (Nat.le_add_right ..)
    have c_le : 2^c ≤ (2^a + 2^b) + 2^c := Nat.le_add_left ..
    rcases le_total b c with bc | cb
    · rw [max_eq_right bc]
      rcases le_total a c with ac | ca
      · simpa only [max_eq_right ac] using c_le
      · simpa only [max_eq_left ca] using a_le
    · rw [max_eq_left cb]
      rcases le_total a b with ab | ba
      · simpa only [max_eq_right ab] using b_le
      · simpa only [max_eq_left ba] using a_le
  exact ((one.add ((room.donors.mul two).add room.sites)).mul width_).add out_

theorem bounded_end (L : ∀h,ι h→RoleControl.Layout) (room : ScalarRoom L)
    (start : Bounded (fun h i=>(L h i).base)) : Bounded (fun h i=>(L h i).endAddress) := by
  simpa only [endAddress,outBase,Nat.add_assoc] using start.add (bounded_extent L room)

end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleControl.Layout

end OAI
