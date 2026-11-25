import OAI.Hierarchy.DescentDonorWalkObservation
import OAI.Hierarchy.DescentObservedDonor
import OAI.Hierarchy.DescentPackedActorPath

namespace OAI
/-! # The physical four-hop chart supplies each of the five donor observations -/
namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSixParty DescentSharedCableNames DescentHostDirectory DescentHaloWalkRAM
open DescentPacking.PackedMatch.Local
open scoped Classical
noncomputable section
variable {Z : Type} {H D : ℕ}
variable (roster : Fin H→Fin D→Option (Fin H)) (start : Fin H) (flag : Fin H→Bool)

def readWalk (w : Walk) : LocalActor :=
  ⟨observedRank roster start (ActorPath.index D w),observedHub roster start flag (ActorPath.index D w),w.2.2.1,w.2.2.2⟩

def atKey (order : Z→Fin H) (z : Key Z) : LocalActor :=
  ⟨Ranks.earlier (Rebase.terminal roster) start (order z.1).val,flag (order z.1),heap z.2.1,z.2.2⟩

theorem readWalk_atKey (next : Z→Fin D→Option Z) (order : Z→Fin H)
    (real : ∀z i y,next z i=some y→ roster (order z) i=some (order y)) (root : Z)
    {w : Walk} {z : Key Z} (read_ : walked next root w z) :
    readWalk roster (order root) flag w=atKey roster (order root) flag order z := by
  have travel:=ActorPath.emitted next order roster real root w z read_
  have a:=congrArg Prod.fst read_.2
  have b:=congrArg Prod.snd read_.2
  simp only [readWalk,atKey,observedRank,observedHub,DescentHaloCompilation.reached,travel,number,Option.elim_some,a,b]
  rfl

theorem same_rank (next : Z→Fin D→Option Z) (order : Z→Fin H)
    (real : ∀z i y,next z i=some y→ roster (order z) i=some (order y)) (root : Z)
    {w u : Walk} {z y : Key Z} (left : walked next root w z) (right : walked next root u y) :
    (atKey roster (order root) flag order z).rank=(atKey roster (order root) flag order y).rank ↔ order z.1=order y.1 := by
  have one:=ActorPath.emitted next order roster real root w z left
  have two:=ActorPath.emitted next order roster real root u y right
  let table_:=Rebase.terminal roster
  have l : table_ (order root) (ActorPath.index D w)=(order z.1).val := by simp [table_,Rebase.terminal,one,number]
  have r : table_ (order root) (ActorPath.index D u)=(order y.1).val := by simp [table_,Rebase.terminal,two,number]
  constructor
  · intro h
    change Ranks.earlier table_ (order root) (order z.1).val=Ranks.earlier table_ (order root) (order y.1).val at h
    apply Fin.ext
    apply le_antisymm
    · by_contra! bad
      have lt_:=Ranks.strict table_ (order root) ⟨_,r⟩ bad
      omega
    · by_contra! bad
      have lt_:=Ranks.strict table_ (order root) ⟨_,l⟩ bad
      omega
  · intro h
    simp [atKey,h]

private theorem keep_location {U : Type} (group : Z→U) (next : Z→Fin D→Option Z)
    (preserve : ∀z i t,next z i=some t → group t=group z) {root t : Z} (q : Address)
    (hit : location next root q=some t) : group t=group root := by
  by_cases self:q.1=0
  · have origin : root=t:=by simpa [location,self] using hit
    rw [origin]
  · by_cases valid:q.1-1<D
    · exact preserve _ _ _ (by simpa [location,self,valid] using hit)
    · simp [location,self,valid] at hit

theorem kept_group {U : Type} (group : Z→U) (next : Z→Fin D→Option Z)
    (preserve : ∀z i t,next z i=some t → group t=group z) {root : Z} {q : Walk} {z : Key Z}
    (read_ : walked next root q z) : group z.1=group root := by
  have finish:=read_.1
  change (location next root (q.1,0,0)).bind (fun t=>location next t q.2)=some z.1 at finish
  cases step_:location next root (q.1,0,0) with
  | none=>simp [step_] at finish
  | some t =>
    exact (keep_location group next preserve q.2 (by simpa [step_] using finish)).trans
      (keep_location group next preserve _ step_)

/-- Use only the common physical host directory. The group coordinate stays
inside the same parallel lane throughout each of the donor's two steps. -/
theorem same_grouped_rank {J V : Type} (next : J×V→Fin D→Option (J×V)) (order : V↪Fin H)
    (real : ∀(z : J×V) i (y : J×V),next z i=some y→ roster (order z.2) i=some (order y.2))
    (preserve : ∀z i y,next z i=some y→y.1=z.1) {root : J×V} {w u : Walk} {z y : Key (J×V)}
    (left : walked next root w z) (right : walked next root u y) :
    (atKey roster (order root.2) flag (fun q=>order q.2) z).rank=
      (atKey roster (order root.2) flag (fun q=>order q.2) y).rank ↔ z.1=y.1 := by
  rw [same_rank roster flag next (fun q=>order q.2) real root left right]
  constructor
  · intro code
    exact Prod.ext ((kept_group Prod.fst next preserve left).trans (kept_group Prod.fst next preserve right).symm) (order.injective code)
  · intro h
    rw [h]

theorem own_rank_bound (w : Walk) : observedRank roster start (ActorPath.index D w)<breadth D :=
  Ranks.bound (Rebase.terminal roster) start (ActorPath.index D w)

end
end Hierarchy.DescentRawCablePanel

end OAI
