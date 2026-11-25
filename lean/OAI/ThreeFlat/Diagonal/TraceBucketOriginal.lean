import OAI.ThreeFlat.Diagonal.TraceBucketGeometry
import OAI.ThreeFlat.Diagonal.TraceBucketMetadata
import OAI.ThreeFlat.RAM.TraceBucketFields

namespace OAI
/-! # Native numeric addresses of the actual incoming original-cell legs -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex
open RAM RAM.BitLayout
open scoped Classical
variable {F : Type*} [CommSemiring F] {p k low o c r : ℕ} {N : BitNetwork F p}
    {P : RowLayout N (k+1) low o c} {lane : Lane (k+1)} (I : BucketIndex P lane)

omit [CommSemiring F] in
private theorem live_iff (s : BitSource N.internal p) : wired s ↔ 2 ≤ sourceAddress s := by
  cases s with
  | constant b => cases b <;> simp [wired,sourceAddress]
  | pin j => simp [wired,sourceAddress]
  | hidden h => simp [wired,sourceAddress,hiddenBase]; omega

/-- Word addresses supplied by the fixed emitter for an original cell.
For coefficient requests, the source read is immaterial and may have any
value. -/
def checkedArgs (i : Fin I.c) (j : Fin 4) (dictionary ids : ℕ) : Fin 13 → ℕ :=
  let cell := (I.cell i).val
  let source := if hj : j.val<3 then N.source cell ⟨j.val,hj⟩ else .constant false
  let site := (P.cellAddress cell).1
  let owner := sourceRow P.hiddenRow P.pinRow site source
  ![j.val,sourceAddress source,owner.val,site.val,c,(P.cellAddress cell).2.val,2^low,I.x,
    I.t,bank r I.t,2^(low+k),dictionary,ids]

omit [CommSemiring F] in
theorem original_word (tag : ((Fin 3→Bool)→F)→ℕ)
    (m : ℕ→ℕ) (dictionary ids : ℕ)
    (invMask : ∀ a : Occurrence N, m (dictionary+(P.offset (P.code a)).val)=(P.code a).val)
    (table : ∀ a : Fin N.cells, m (ids+(P.cellAddress a).2.val)=tag (N.table a))
    (ordered : ∀ t, (I.tag.symm t).val=((tagOrder o low c).symm t).val) (i : Fin I.c) (j : Fin 4) :
    TraceBucketFields.originalNat m (I.checkedArgs (r:=r) i j dictionary ids)=I.original (r:=r) tag i j := by
  let a := (I.cell i).val
  by_cases hj : j.val<3
  · let leg : Fin 3 := ⟨j.val,hj⟩
    let source := N.source a leg
    by_cases hw : wired source
    · let e : Occurrence N := ⟨(a,leg),hw⟩
      have big : ¬sourceAddress source<2 := by have := (live_iff source).mp hw; omega
      have xor := P.owner_xor e
      have tagVal : (I.tag.symm (P.tag e)).val =
        (((P.code e).val*2^low+(P.owner e).val%2^low)*c+(P.cellAddress a).2.val)*3+j.val := by
        exact (ordered _).trans (P.tag_occurrence e)
      have arc := P.selected_bit (r:=r) (Fin.last k) (P.code e)
      dsimp only [source,leg,a] at big hw
      simp only [original,hj,dite_true,hw,Equiv.apply_symm_apply]
      simp only [TraceBucketFields.originalNat,checkedArgs,hj,dite_true,ite_true,Matrix.cons_val_zero,
        Matrix.cons_val_one,big,ite_false]
      change 2+I.x+bank r I.t+
        ((((P.owner e).val ^^^ (P.cellAddress a).1.val)/2^(low+k))%2)*I.t+
        (((m (dictionary+((P.owner e).val ^^^ (P.cellAddress a).1.val))*2^low+(P.owner e).val%2^low)*c+
          (P.cellAddress a).2.val)*3+j.val) =
        2+I.x+bank r I.t+((selected (r:=r) P.mask (P.code e) (Fin.last k)).val*I.t+(I.tag.symm (P.tag e)).val)
      rw [xor,invMask,tagVal,arc]
      simp only [Fin.val_last]
      omega
    · have small : sourceAddress source<2 := Nat.lt_of_not_ge (fun h => hw ((live_iff source).mpr h))
      simp [TraceBucketFields.originalNat,checkedArgs,original,hj,source,a,leg] at hw small ⊢
      simp [hw,small]
  · simpa [TraceBucketFields.originalNat,checkedArgs,original,hj] using table a

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

end OAI
