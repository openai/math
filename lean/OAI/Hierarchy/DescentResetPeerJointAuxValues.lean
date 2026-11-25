import OAI.Hierarchy.DescentResetPeerJointAux

namespace OAI
/-! # The four finite fields at the receiver's own sparse address -/
namespace Hierarchy.DescentResetPeerJointPacked.Aux
open DescentResetPeerJointRAM DescentResetOriginHaloRAM DescentSortedRoster
open scoped Classical BigOperators
noncomputable section
variable {P N H O D b : ℕ} (width : ℕ) (name : Fin N→Fin P)
    (old : Fin O→Fin D→Option (Fin O)) (near : Fin P→Fin 3→Option (Fin P)) (v : Fin H)
variable (live : v.val < N)
variable (inside : (name ⟨v.val,live⟩).val/width < O)

theorem self_halo (distinct : ∀r i j z,old r i=some z→ old r j=some z→i=j) :
    let parent : Fin O:=⟨(name ⟨v.val,live⟩).val/width,inside⟩
    value width name old near v 0=1+before (closed old) parent parent := by
  intro parent
  simp only [value, Fin.val_zero, show (0:ℕ)≠3 by decide, show (0:ℕ)≠2 by decide,
    ite_false, dite_eq_left live, dite_eq_left inside]
  change DescentClosedHaloChip.value (old parent) parent parent 0=_
  rw [label old parent parent 0 distinct,ite_eq_left ((mem_present_closed old parent parent).2 (.inl rfl))]

theorem self_joint (distinct : ∀r i j z,old r i=some z→ old r j=some z→i=j) :
    let parent : Fin O:=⟨(name ⟨v.val,live⟩).val/width,inside⟩
    value width name old near v 1=(name ⟨v.val,live⟩).val%width*radix D+1+before (closed old) parent parent := by
  intro parent
  have one : (1:Fin 4).val=1:=rfl
  simp only [value,one,show (1:ℕ)≠3 by decide,show (1:ℕ)≠2 by decide,show (1:ℕ)≠0 by decide,
    ite_false,dite_eq_left live,dite_eq_left inside]
  change DescentClosedHaloChip.value (old parent) parent parent ((name ⟨v.val,live⟩).val%width*radix D)=_
  rw [label old parent parent _ distinct,ite_eq_left ((mem_present_closed old parent parent).2 (.inl rfl))]

theorem raw_missing : value width name old near v 2=if ∀j,near (name ⟨v.val,live⟩) j≠some (name ⟨v.val,live⟩) then 1 else 0 := by
  simp [value,live]

theorem old_self (distinct : ∀r i j z,old r i=some z→ old r j=some z→i=j) :
    let parent : Fin O:=⟨(name ⟨v.val,live⟩).val/width,inside⟩
    value width name old near v 3=2*before (closed old) parent parent+(decide (parent∉present old parent)).toNat := by
  intro parent
  simp only [value,show (3:Fin 4).val=3 by rfl,DescentResetPeerOldCorrection.value,
    dite_eq_left live,dite_eq_left inside]
  exact DescentResetPeerOldCorrection.code_eq old parent distinct

theorem value_lt (j : Fin 4) (_distinct : ∀r i k z,old r i=some z→ old r k=some z→i=k)
    (positive : 0 < width) (joint : width*radix D ≤ 2^b) (corr : 2*(D+1) ≤ 2^b) :
    value width name old near v j < 2^b := by
  have zero:=Nat.two_pow_pos b
  by_cases last : j.val=3
  · simpa only [value,ite_eq_left last] using
      (DescentResetPeerOldCorrection.value_lt (width:=width) name old v corr)
  simp only [value,ite_eq_right last]
  split
  next live =>
    split
    next absent =>
      split <;> omega
    next other =>
      split
      next located =>
        let current:=name ⟨v.val,live⟩
        let a : Fin O:=⟨current.val/width,located⟩
        have small : DescentClosedHaloChip.weight (old a) a a ≤ D := by
          unfold DescentClosedHaloChip.weight
          simp only [lt_self_iff_false,ite_false,Nat.zero_add]
          calc
            _ ≤ ∑ _ : Fin D,1:=Finset.sum_le_sum (fun i _=>by split <;> omega)
            _ = D:=by simp
        have rad : D+2 ≤ radix D:=Nat.le_pow_clog (by decide) _
        have step:=Nat.mul_le_mul_right (radix D) (Nat.mod_lt current.val positive)
        rw [Nat.succ_mul] at step
        change DescentClosedHaloChip.value (old a) a a (if j.val=0 then 0 else current.val%width*radix D) < _
        simp only [DescentClosedHaloChip.value,eq_self,true_or,ite_true]
        split <;> omega
      next outside => exact zero
  next ghost => exact zero

end
end Hierarchy.DescentResetPeerJointPacked.Aux

end OAI
