import OAI.Hierarchy.DescentSparseWordOrder

namespace OAI
/-! # Aligned intervals in the chronological concatenation of whole cable widths -/

namespace Hierarchy.DescentOrderedWords
open scoped BigOperators Classical
noncomputable section
variable {I : Type*} [Fintype I] {N p : ℕ} (key : I↪Fin N) (width : I→ℕ)

/-- An aligned block is given by its word number in the concatenated bit budget. -/
structure Aligned (p width : ℕ) where
  row : ℕ
  fits : (row+1)*p≤width

def Aligned.bit {width : ℕ} (z : Aligned p width) (d : Fin p) : Fin width :=
  ⟨z.row*p+d.val,(Nat.add_lt_add_left d.isLt _).trans_le (by simpa [Nat.add_mul] using z.fits)⟩

theorem offset_dvd (whole : ∀i,p∣width i) (i : I) : p∣offset key width i :=
  Finset.dvd_sum (fun j _=>whole j)

/-- The rank scan starts this whole source word at the earlier local word
count; every digit retains its original offset modulo the word width. -/
def inside (whole : ∀i,p∣width i) (i : I) (z : Aligned p (width i)) : Aligned p (∑i,width i) where
  row:=offset key width i/p+z.row
  fits:=by
    have paid:=Nat.div_mul_cancel (offset_dvd key width whole i)
    calc (offset key width i/p+z.row+1)*p = offset key width i + (z.row+1)*p := by
            rw [Nat.add_assoc (offset key width i/p) z.row 1, Nat.add_mul,paid]
         _ ≤ offset key width i+width i := Nat.add_le_add_left z.fits _
         _ ≤ _ := end_le key width i

@[simp] theorem inside_read (whole : ∀i,p∣width i) (i : I) (z : Aligned p (width i)) (d : Fin p) :
    (inside key width whole i z).bit d=address key width ⟨i,z.bit d⟩ := by
  apply Fin.ext
  change (offset key width i/p+z.row)*p+d.val=offset key width i+(z.row*p+d.val)
  rw [Nat.add_mul,Nat.div_mul_cancel (offset_dvd key width whole i)]
  omega

theorem outside (whole : ∀i,p∣width i) (hp : 0<p) (z : Aligned p (∑i,width i)) :
    ∃ i : I, ∃ part : Aligned p (width i), ∀d,(address key width).symm (z.bit d)=⟨i,part.bit d⟩ := by
  obtain ⟨⟨i,t⟩,yes⟩ := (address key width).surjective (z.bit ⟨0,hp⟩)
  have whereAt:=congrArg Fin.val yes
  change offset key width i+t.val=z.row*p+0 at whereAt
  obtain ⟨oa,ha⟩:=offset_dvd key width whole i
  obtain ⟨wa,hb⟩:=whole i
  have oaLess : oa≤z.row := by
    apply (Nat.mul_le_mul_left_iff hp).mp
    rw [←ha,Nat.mul_comm p]
    omega
  let localRow:=z.row-oa
  have tv : t.val=localRow*p := by
    have split : oa+localRow=z.row := Nat.add_sub_of_le oaLess
    rw [←split,Nat.add_mul,←Nat.mul_comm p oa,←ha] at whereAt
    omega
  have ok : localRow<wa := by
    apply (Nat.mul_lt_mul_right hp).mp
    simpa only [←tv,←Nat.mul_comm p wa,←hb] using t.isLt
  let part : Aligned p (width i) := ⟨localRow,by rw [hb,Nat.mul_comm p wa];exact Nat.mul_le_mul_right p ok⟩
  refine ⟨i,part,fun d=>(Equiv.symm_apply_eq _).2 ?_⟩
  apply Fin.ext
  change z.row*p+d.val=offset key width i+(localRow*p+d.val)
  omega

end
end Hierarchy.DescentOrderedWords

end OAI
