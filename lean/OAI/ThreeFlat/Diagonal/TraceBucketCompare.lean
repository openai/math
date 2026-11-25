import OAI.ThreeFlat.Diagonal.TraceBucketEmit
import OAI.ThreeFlat.Diagonal.TraceBucketTranslated
import OAI.ThreeFlat.Diagonal.TraceBucketGeometry
import OAI.ThreeFlat.RAM.TraceBucketFields

namespace OAI
/-! # Numerical comparison and padding record semantics for a physical lane -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex
open RAM RAM.BitLayout
open scoped Classical
variable {F : Type*} [CommSemiring F] {p k low o c r H : ℕ} {N : BitNetwork F p}
    {P : RowLayout N (k+1) low o c} {lane : Lane (k+1)}

omit [CommSemiring F] in
private theorem probe_eq (I : BucketIndex P.canonical lane) (R : P.Rectangular)
    (t : Fin o × PayloadAddress low c) :
    I.probe t = P.canonical.reverseProbe (Rectangular.canonicalized P R) lane t := by
  cases h : I.probe t with
  | some a => exact ((P.canonical.reverseProbe_iff _ _ _ _).mpr ((I.probe_some t a).mp h)).symm
  | none =>
    cases hx : P.canonical.reverseProbe (Rectangular.canonicalized P R) lane t with
    | none => rfl
    | some a =>
      have := (I.probe_some t a).mpr ((P.canonical.reverseProbe_iff _ _ _ _).mp hx)
      simp [h] at this

omit [CommSemiring F] in
private theorem map_emission (I : BucketIndex P.canonical lane)
    (A : BitNetwork.Rectangular.Address I.h H) (t : Fin I.t) :
    I.emissionWord (r:=r) A t =
      ((I.probe (I.tag t)).map (fun a => N.source a.val.1 a.val.2)).elim 0 (I.translateWord (r:=r) A) := by
  unfold emissionWord
  cases I.probe (I.tag t) <;> rfl

/-- The received source and the requested owner come from the unique
candidate cell at `owner XOR displacement`. Only the true source
owner, selected arc, and canonical offset number determine the result. -/
theorem compare_word (I : BucketIndex P.canonical lane) (R : P.Rectangular)
    (A : BitNetwork.Rectangular.Address I.h H) (label : ((Fin 3→Bool)→F)→ℕ)
    (pinStart : ℕ) (localSlot : ℕ → ℕ)
    (pinned : ∀ (j : Fin p) (own : (splitRow _ _ (P.pinRow j)).1=lane),
      (I.ext.symm ⟨j,own⟩).val=j.val-pinStart ∧ pinStart≤j.val)
    (hidden : ∀ (j : Fin N.internal) (own : (splitRow _ _ (P.hiddenRow j)).1=lane),
      (A.put (I.hidden.symm ⟨j,own⟩)).val=localSlot j.val)
    (canonical : ∀ j, firstMask P.offset j=decide (j.val≠k+1+low+1))
    (t : Fin I.t) (j : Fin 4) :
    let i := I.tag t
    let own := (splitRow _ _).symm (lane,i.2.1)
    let dest := partner own (P.offset i.1)
    let s := N.source (R.cell dest i.2.2.1) i.2.2.2
    let home := sourceRow P.hiddenRow P.pinRow dest s
    let x := sourceAddress s
    TraceBucketFields.compareNat ![j.val,x,home.val,own.val,i.1.val,k+1+low,p,pinStart,I.x,
      ports r I.t,localSlot (x-(2+p)),((P.offset i.1).val/2^low)%2,I.t,t.val,label
        (fun z => if z 0=z 1 then 1 else 0)] =
      I.compareRow (r:=r) A label t j := by
  intro i own dest s home x
  have source := P.reverse_source R lane i
  change _ = if 2≤x ∧ home.val=own.val ∧ firstMask P.offset i.1=true then some s else none at source
  have proj := I.map_emission (r:=r) A t
  rw [probe_eq I R,source,canonical] at proj
  have arc := P.canonical.selected_bit (r:=r) (0 : Fin (k+1)) i.1
  change _ = ((P.offset i.1).val/2^low)%2 at arc
  change (if j.val=0 then _ else if j.val=1 then _ else if j.val=2 then _ else _) = _
  unfold compareRow
  by_cases first : j.val=0
  · simp only [first,ite_true]
    exact congrArg (fun a => 2+I.x+a*I.t+t.val) arc.symm
  · simp only [first,ite_false]
    by_cases second : j.val=1
    · simp only [second,ite_true]
      by_cases small : x<2
      · have neg : ¬2≤x := by omega
        simp [neg] at proj
        simpa [small] using proj.symm
      · have big : 2≤x := by omega
        by_cases dup : i.1.val=k+1+low+1
        · simp [dup] at proj
          simpa [small,dup] using proj.symm
        · by_cases hrow : home.val=own.val
          · have eqrow : home=own := Fin.ext hrow
            have ownLane : (splitRow _ _ home).1=lane := by rw [eqrow]; exact congrArg Prod.fst ((splitRow _ _).apply_symm_apply _)
            have wire : wired s := by
              cases he : s with
              | constant b => cases b <;> simp [x,he,sourceAddress] at big
              | hidden u | pin u => trivial
            have tr := I.translate_live (r:=r) A s dest pinStart localSlot wire ownLane pinned hidden
            simp [big,hrow,dup,tr] at proj
            simpa [small,dup,hrow,x] using proj.symm
          · simp [hrow] at proj
            simpa [small,dup,hrow] using proj.symm
    · simp only [second,ite_false]
      rfl

/-- A physically reserved hidden slot receives a unary zero-test precisely
when its mixed-radix inverse does not exist. -/
theorem hole_word (I : BucketIndex P lane) (A : BitNetwork.Rectangular.Address I.h H)
    (label : ((Fin 3→Bool)→F)→ℕ) (q : Fin H) (j : Fin 4) :
    (if j.val<3 then 2+I.x+ports r I.t+q.val else if (A.get q).isNone then
      label (fun z => if z 0=true then 0 else 1) else label (fun _ => 1)) =
      I.holeRow (r:=r) A label q j := by
  unfold holeRow
  cases h : A.get q <;> simp [Nat.add_assoc]

end ThreeFlat.Diagonal.LaneCursor.RowLayout.BucketIndex

end OAI
