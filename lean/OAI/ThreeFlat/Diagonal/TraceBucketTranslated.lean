import OAI.ThreeFlat.Diagonal.TraceBucketMetadata

namespace OAI
/-! # Absolute to owner-local addresses at live reservation sources -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex
open RAM.BitLayout
variable {F : Type*} [CommSemiring F] {p k low o c r H : ℕ} {N : BitNetwork F p}
    {P : RowLayout N (k+1) low o c} {lane : Lane (k+1)} (I : BucketIndex P lane)

omit [CommSemiring F] in
/-- An admitted source already belongs to the requested lane. Its pin
address is a translated contiguous interval and its hidden address is a
single owner-local reservation after both physical half-port banks. -/
theorem translate_live (A : BitNetwork.Rectangular.Address I.h H) (s : BitSource N.internal p)
    (receiver : Row (k+1) low) (start : ℕ) (slot : ℕ → ℕ)
    (wiredAt : wired s) (owner : (splitRow _ _ (sourceRow P.hiddenRow P.pinRow receiver s)).1=lane)
    (pinned : ∀ (j : Fin p) (own : (splitRow _ _ (P.pinRow j)).1=lane),
      (I.ext.symm ⟨j,own⟩).val=j.val-start ∧ start≤j.val)
    (hidden : ∀ (j : Fin N.internal) (own : (splitRow _ _ (P.hiddenRow j)).1=lane),
      (A.put (I.hidden.symm ⟨j,own⟩)).val=slot j.val) :
    I.translateWord (r:=r) A s =
      if sourceAddress s<2+p then sourceAddress s-start else
        2+I.x+ports r I.t+slot (sourceAddress s-(2+p)) := by
  cases s with
  | constant b => exact wiredAt.elim
  | pin j =>
    change (splitRow _ _ (P.pinRow j)).1=lane at owner
    have hp := pinned j owner
    have small : sourceAddress (BitSource.pin j : BitSource N.internal p)<2+p := by
      change 2+j.val<2+p
      exact Nat.add_lt_add_left j.isLt 2
    rw [ite_eq_left small]
    simp only [translateWord,dite_eq_left owner,sourceAddress,hp.1]
    omega
  | hidden j =>
    change (splitRow _ _ (P.hiddenRow j)).1=lane at owner
    have hh := hidden j owner
    have big : ¬sourceAddress (BitSource.hidden j : BitSource N.internal p)<2+p := by
      change ¬2+p+j.val<2+p
      omega
    rw [ite_eq_right big]
    simp only [translateWord,dite_eq_left owner,sourceAddress,hiddenBase,hh,Nat.add_assoc]
    rw [show 2+(p+j.val)-(2+p)=j.val by omega]

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

end OAI
