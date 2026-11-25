import OAI.Hierarchy.DescentDonorNumericHeads
import OAI.Hierarchy.DescentPackedActorHeads
import OAI.Hierarchy.DescentHaloPackedRebase
import OAI.Hierarchy.DescentHaloPackedGather

namespace OAI
/-! # Rebase the two relative words printed by the actual previous-stage actor lookup -/
namespace Hierarchy.DescentHaloWalkRAM.ActorPath
open DescentSixParty DescentPacking.PackedMatch.Local DescentSIMDLookup DescentSharedCableNames
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {Z : Type} {D H : ℕ}

theorem hop_at (next : Z→Fin D→Option Z) (rank : Z→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (real : ∀z i y,next z i=some y→R (rank z) i=some (rank y)) (z u : Z) (q : Address) (hit : location next z q=some u) :
    step R (some (rank z)) (slot D q.1)=some (rank u) :=by
  by_cases zero:q.1=0
  · have eqn:z=u:=by simpa [location,zero] using hit
    subst u;simp [step,slot,zero]
  · by_cases live:q.1-1<D
    · rw [slot,dite_eq_left ⟨zero,live⟩,step,dite_eq_left live];apply real;simpa [location,live,zero] using hit
    · simp [location,live,zero] at hit

theorem emitted (next : Z→Fin D→Option Z) (rank : Z→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (real : ∀z i y,next z i=some y→R (rank z) i=some (rank y)) (z : Z) (w : Walk) (x : DescentHostDirectory.Key Z) (printed : walked next z w x) :
    walk R (rank z) (path (index D w)) 4=some (rank x.1) :=by
  have end_:=printed.1
  change (location next z (w.1,0,0)).bind (fun y=>location next y w.2)=some x.1 at end_
  cases first : location next z (w.1,0,0) with
  | none=>simp [first] at end_
  | some y=>
    have second : location next y w.2=some x.1:=by simpa [first] using end_
    have a:=hop_at next rank R real z y (w.1,0,0) first
    have b:=hop_at next rank R real y x.1 w.2 second
    simp only [index,path,Equiv.symm_apply_apply]
    change step R (step R (step R (step R (some (rank z)) (slot D w.1)) (slot D w.2.1)) (Fin.last D)) (Fin.last D)=_
    rw [a,b];simp [step]

/-- In particular this is the true rank and reverse path for every `.old`
from `Stage.prior_head` and every `.born` from `Stage.born_walk`, including
the self/stay code in either one of the actual two short registers. -/
theorem rebase (next : Z→Fin D→Option Z) (rank : Z→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (real : ∀z i y,next z i=some y→R (rank z) i=some (rank y)) (symmetric : ∀v u i,R v i=some u→∃j,R u j=some v)
    (z : Z) (w : Walk) (x : DescentHostDirectory.Key Z) (printed : walked next z w x) :
    ∃q,walk R (rank x.1) (path q) 4=some (rank z) ∧ Rebase.value R .path (rank z) (index D w)=q.val ∧
      Rebase.value R .rank (rank z) (index D w)=Ranks.earlier (Rebase.terminal R) (rank x.1) (rank z).val :=
  Rebase.actual R symmetric _ _ _ (emitted next rank R real z w x printed)

theorem received_once (next : Z→Fin D→Option Z) (rank : Z→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (real : ∀z i y,next z i=some y→R (rank z) i=some (rank y)) (symmetric : ∀v u i,R v i=some u→∃j,R u j=some v)
    (z : Z) (w : Walk) (x : DescentHostDirectory.Key Z) (printed : walked next z w x) :
    ∃!q,Gather.select (Gather.reaching R) (rank x.1) q=some (rank z) :=by
  obtain ⟨q,hit,_,_⟩:=rebase next rank R real symmetric z w x printed
  exact Gather.once _ _ _ ⟨q,hit⟩

/-- A one-based peer code can be assembled before the common-rack rebase
without revealing the rank of either endpoint to its local state chip. -/
def encodeHop (D n : ℕ) : Cell (Packed.bits D) :=⟨min n D,lt_of_lt_of_le (Nat.lt_succ_of_le (min_le_right ..)) (Nat.le_pow_clog (by decide) _)⟩

def pathChip (D : ℕ) (a b : Cell (Packed.bits D)) : Cell (Packed.bits (breadth D)) :=Packed.token (some (finFunctionFinEquiv (hops D a.val b.val)))

theorem bounds (next : Z→Fin D→Option Z) {z y : Z} (q : Address) (hit : location next z q=some y) : q.1≤D:=by
  unfold location at hit;split at hit <;> first | omega | split at hit <;> first | omega | contradiction

theorem chip_at (next : Z→Fin D→Option Z) (z : Z) (w : Walk) (x : DescentHostDirectory.Key Z) (printed : walked next z w x) :
    pathChip D (encodeHop D w.1) (encodeHop D w.2.1)=Packed.token (some (index D w)) :=by
  have path_:=printed.1
  change (location next z (w.1,0,0)).bind (fun y=>location next y w.2)=some x.1 at path_
  cases first : location next z (w.1,0,0) with
  | none=>simp [first] at path_
  | some y=>
    have second:=bounds next w.2 (show location next y w.2=some x.1 by simpa [first] using path_)
    have few:w.1≤D:=bounds next _ first
    simp [pathChip,encodeHop,min_eq_left few,min_eq_left second,index]

end
end Hierarchy.DescentHaloWalkRAM.ActorPath

end OAI
