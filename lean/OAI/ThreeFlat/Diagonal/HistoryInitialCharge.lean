import OAI.ThreeFlat.Diagonal.HistoryStageCharges
import OAI.ThreeFlat.Diagonal.TraceBucketInitial
import OAI.ThreeFlat.Diagonal.LaneBucketAddresses

namespace OAI
/-! # Charges at true and relay leaves of the actual addressed trace -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

open HistoryContraction
variable {F : Type*} [CommSemiring F] {p k low o slots r H : ℕ} {N : BitNetwork F p}
    {P : RowLayout N (k+1) low o slots} {lane : Lane (k+1)} (I : BucketIndex P lane)

theorem first_resources (A : BitNetwork.Rectangular.Address I.h H) (i : Fin (k+1)) :
    (Tree.atom (I.firstNetwork (r:=r) A i)).resources = 1+2*H+I.c+(r+1)*2*I.t+2*I.t := by
  rw [Tree.resources_atom]
  change H+(((r+1)*2*I.t+I.t)+(I.c+I.t+H))+1=_
  omega

theorem relay_resources (i : Fin (k+1)) :
    (Tree.atom (I.initialNetwork (r:=r) false i)).resources = 1+(r+1)*2*I.t+I.t := by
  rw [Tree.resources_atom]
  change 0+((r+1)*2*I.t+I.t)+1=_
  omega

/-- On a pure relay, all scan work is covered by its local incident width.
Only the cursor-zero leaf contains the actual CPU/template rows. -/
theorem relay_resources_le (i : Fin (k+1)) :
    (Tree.atom (I.initialNetwork (r:=r) false i)).resources ≤ 1+2*((r+1)*2*I.t) := by
  rw [relay_resources]
  have cap : I.t ≤ (r+1)*2*I.t := by
    exact (Nat.one_mul _).symm.le.trans (Nat.mul_le_mul_right _ (by omega))
  omega

theorem first_resources_le (A : BitNetwork.Rectangular.Address I.h H) (i : Fin (k+1)) :
    (Tree.atom (I.firstNetwork (r:=r) A i)).resources ≤ 1+2*H+I.c+2*((r+1)*2*I.t) := by
  rw [first_resources]
  have cap := Nat.mul_le_mul_right I.t (show 2≤(r+1)*2 by omega)
  omega

/-- The CPU, hidden and reservation slabs are all linear in the low-row
count. The coefficient is independent of the number of lanes. -/
theorem rectangular_charge (A : BitNetwork.Rectangular.Address I.h (2^low*H)) (i : Fin (k+1))
    (cells : I.c=2^low*slots) (tags : I.t=o*(2^low*(slots*3))) :
    (Tree.atom (I.firstNetwork (r:=r) A i)).resources ≤
      1+2^low*(2*H + slots + 12*(r+1)*o*slots) := by
  apply (first_resources_le I A i).trans
  rw [cells,tags]
  exact le_of_eq (by ring)

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

end OAI
