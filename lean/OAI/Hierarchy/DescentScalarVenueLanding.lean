import OAI.Hierarchy.DescentScalarActorTickets
import OAI.Hierarchy.DescentDonorWalkRead

namespace OAI
/-! # The physical ticket accepts exactly the host and the post-merge heap/slot -/
namespace Hierarchy.DescentScalarVenueMask
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentPacking.PackedMatch.Local
open DescentHostDirectory DescentHostDirectory.SiteDecode DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {D H k gain slots low : ℕ}
variable (next : V→Fin D→Option V) (rank : V→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (stored : ∀z j y,next z j=some y→R (rank z) j=some (rank y))
local notation "walks"=>Gather.reaching R
local notation "raw"=>(2^(k+1)*slots)

omit [DecidableEq V] in
theorem launched (root : V) (w : Walk) (q : Key V) (valid : q∈keys k slots) (truth : walked next root w q) :
    ∃u : Fin raw,issue D slots raw w=some (ActorPath.index D w,u) ∧ u.val=localNumber k slots q :=by
  have code : w.2.2.1*slots+w.2.2.2=localNumber k slots q:=by
    obtain ⟨_,p⟩:=truth;rw [show w.2.2.1=DescentPacking.PackedMatch.Local.heap q.2.1 from congrArg Prod.fst p,show w.2.2.2=q.2.2 from congrArg Prod.snd p]
    simp [localNumber,packedNumber,nodeNumber,DescentPacking.PackedMatch.Local.heap]
  have bound : localNumber k slots q<raw:=by simpa [trim] using trim_lt k 0 slots (fun _:V=>false) q valid
  exact ⟨⟨_,bound⟩,by simp only [issue,code,dite_eq_left bound],rfl⟩

include stored in
omit [DecidableEq V] in
theorem landing (root : V) (w : Walk) (q : Key V) (legal : q∈keys k slots) (truth : walked next root w q)
    (receiver : Fin H) (donor : Fin (breadth D)) (found : DescentSortedRoster.indexed walks receiver donor=some (rank root))
    (hub : V→Bool) (receivedHub : Cell 1) (hubAt : rank q.1=receiver→decide (receivedHub≠0)=hub q.1) (l : Fin low) :
    returned k gain slots raw low walks donor receiver receivedHub (issue D slots raw w)=Packed.token (some l) ↔
      rank q.1=receiver ∧ localNumber k slots (mergeHub hub k gain q)=l.val :=by
  obtain ⟨u,formed,code⟩:=launched (k:=k) (slots:=slots) next root w q legal truth
  have travels:=ActorPath.emitted next rank R stored root w q truth
  have hit : DescentScalarVenueDirectory.hit walks donor receiver (ActorPath.index D w)=true ↔ rank q.1=receiver:=by
    simp [DescentScalarVenueDirectory.hit,found,Gather.reaching,travels]
  rw [returned_iff,formed]
  constructor
  · rintro ⟨i,t,same,arrived,atLow⟩
    have names:=Option.some.inj same;obtain rfl:=congrArg Prod.fst names;obtain rfl:=congrArg Prod.snd names
    have present:=hit.mp arrived
    exact ⟨present,by simpa only [code,hubAt present,trim_key k gain slots hub q legal] using atLow⟩
  · rintro ⟨present,cell⟩
    exact ⟨_,u,rfl,hit.mpr present,by simpa only [code,hubAt present,trim_key k gain slots hub q legal] using cell⟩

/-- The previous group is carried in the parallel lane. The current host is
queried numerically and the actual old group stays fixed along both hops. -/
theorem grouped_landing {J Z : Type} [Fintype J] [DecidableEq J] [Fintype Z] [DecidableEq Z]
    (move : J×Z→Fin D→Option (J×Z)) (vertex : Z↪Fin H) (adj : Fin H→Fin D→Option (Fin H))
    (measured : ∀a j b,move a j=some b→adj (vertex a.2) j=some (vertex b.2)) (preserve : ∀a j b,move a j=some b→b.1=a.1)
    (donor : J×Z) (w : Walk) (q : Key (J×Z)) (legal:q∈keys k slots) (printed:walked move donor w q)
    (recv : J×Z) (s : Fin (breadth D)) (found : DescentSortedRoster.indexed (Gather.reaching adj) (vertex recv.2) s=some (vertex donor.2))
    (lane : donor.1=recv.1) (hub : J×Z→Bool) (flag : Cell 1) (data_ : decide (flag≠0)=hub recv) (l : Fin low) :
    returned k gain slots raw low (Gather.reaching adj) s (vertex recv.2) flag (issue D slots raw w)=Packed.token (some l) ↔
      q.1=recv ∧ localNumber k slots (mergeHub hub k gain q)=l.val :=by
  have group_:q.1.1=recv.1:=(DescentRawCablePanel.kept_group Prod.fst move preserve printed).trans lane
  have real : vertex q.1.2=vertex recv.2 ↔ q.1=recv:=⟨fun eqn=>Prod.ext group_ (vertex.injective eqn),fun eqn=>congrArg (fun a:J×Z=>vertex a.2) eqn⟩
  rw [landing move (fun a=>vertex a.2) adj measured donor w q legal printed (vertex recv.2) s found hub flag (fun eqn=>(real.mp eqn) ▸ data_),real]

end
end Hierarchy.DescentScalarVenueMask

end OAI
