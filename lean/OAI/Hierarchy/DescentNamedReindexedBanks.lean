import OAI.Hierarchy.DescentIndexedRootState
import OAI.Hierarchy.DescentCalendarPrivatePages
import OAI.Hierarchy.DescentFrontEarlierRoot

namespace OAI
/-! # All preceding operand addresses survive transport to the reached reset coordinates -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots
open DescentDatedAddressBook ProtocolRAM
open CandidateFront
variable {D cap N n r c H G K R M hm lb tiny field Ht w : ℕ}
  {D' cap' n' r' c' H' G' Ht' : ℕ}
  (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
  (d : D=D') (a : cap=cap') (nn : n=n') (rr : r=r')
  (cc : c=c') (hh : H=H') (gg : G=G') (ht : Ht=Ht')
local notation "y" => x.reindex d a nn rr cc hh gg ht
theorem earlier_eq {Du ku cu nu : ℕ} (d₀ : D'=Du) (r₀ : r'=ku) (c₀ : cap'=cu) (n₀ : n'=nu)
    (oldId oldHub : Bank) (dir : DescentResetNewActorDirectory.Layout) (actor : Bank) :
    EarlierBanks.castTo d₀ r₀ c₀ n₀ (EarlierBanks.fromRoot (y).receiver (y).book (y).sources oldId oldHub dir actor)=
      EarlierBanks.castTo (d.trans d₀) (rr.trans r₀) (a.trans c₀) (nn.trans n₀)
        (EarlierBanks.fromRoot x.receiver x.book x.sources oldId oldHub dir actor):=by
  subst D' cap' n' r' c' H' G' Ht'
  rfl
end Hierarchy.DescentFallbackPeriod.Projected.Receiver.IndexedRoots

namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
theorem cap_cast {D r c n c' : ℕ} (b : EarlierBanks D r c n) (eqn : c=c') :
    castTo rfl rfl eqn rfl b = cast (congrArg (fun t=>EarlierBanks D r t n) eqn) b :=by
  subst c'
  rfl
end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

end OAI
