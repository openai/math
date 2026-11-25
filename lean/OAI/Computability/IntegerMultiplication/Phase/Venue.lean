import OAI.Computability.IntegerMultiplication.Phase.Rig

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Strip Dims Loom Packed Pos
variable {I J : Type} {P T d : Tape} {h g l m : ℕ}
variable [Fintype J] [DecidableEq J] (f : J≃Fin m)
variable {x : Series I}
omit [Fintype J] in
private theorem stair (a b c : J) (t : f a < f b) (u : f b < f c)
    (e : Seal x d) :
    ∃ r : Rig (order P T (threads x f))
      (P++leftF f d a) (midF f d a b) (midF f d b c) (rightF f d c++T) x,
      (∀ i : Base P T (J→I),Rig.why r i=(i.2.1 a,i.2.1 b,i.2.1 c)) ∧
      ∀ i : Base P T (J→I),∀ w,Rig.serve r i w=(i.1,Function.update (Function.update (Function.update i.2.1 a w.1) b w.2.1) c w.2.2,i.2.2) := by
  obtain ⟨z,s,v⟩ := depth d e (f a) (f b) (f c) t u
  have useUpd (w : J→I) (i : J) (s : I) :
      (pullback x f).cast (Function.update w i s)=
      Function.update ((pullback x f).cast w) (f i) s := by
    ext j : 1
    obtain ⟨j,rfl⟩ := f.surjective j
    change Function.update w i s (f.symm _) = _
    have h (w : J→I) : (pullback x f).cast w = (fromOrder f I).symm w := rfl
    by_cases e : j=i
    · simp [h,e]
    have y : f j≠f i := fun h => e (f.injective h)
    simp [h,y,e]
  let zi := (pullback x f).thenDo z
  refine ⟨(Rig.store_r (Rig.store_s zi (Adopt.same _)) (Adopt.same _)),fun i => ?_, fun i w => ?_⟩ -- dot for abbrev maybe
  · rcases i with ⟨_P,i,_T⟩
    change z.why ((pullback x f).cast i) = _
    rw [s]
    change ((fromOrder f I).symm i _,_,_)= _
    simp only [show (pullback x f).cast= (fromOrder f I).symm from rfl,Loom.use_f,Equiv.symm_apply_apply]
  rcases i with ⟨_P,i,_T⟩
  rw [Rig.do_f]
  have hb := Rig.do_b zi (Adopt.same (layout T)) i _T w
  have hs := Rig.shipped z (pullback x f) i w
  calc
    _ = (_P, Rig.serve zi i w, _T) := congrArg (fun v => (_P,v)) hb
    _ = (_P, (pullback x f).cast.symm (z.serve ((pullback x f).cast i) w), _T) :=
      congrArg (fun v => (_P,v,_T)) hs
    _ = _ := by
      rw [v,← useUpd,← useUpd,← useUpd,Equiv.symm_apply_apply]

omit [Fintype J] [DecidableEq J] in
private theorem sorting (q : Pos → J) (i : Function.Injective q) :
    ∃ d : Equiv.Perm Pos,f (q (d sun))<f (q (d noon)) ∧ f (q (d noon))<f (q (d moon)) := by
  let A j := f (q j)
  change ∃ d : Equiv.Perm Pos,A (d _) < A (d _) ∧ A (d _) < A (d _)
  have p (a b) (e : a≠b) : A a≠A b := fun h => e (i (f.injective h))
  -- within three distinct.
  rcases lt_or_gt_of_ne (p sun noon (by decide)) with k|k
  · rcases lt_or_gt_of_ne (p noon moon (by decide)) with z|z
    · exact ⟨Equiv.refl _,k,z⟩
    rcases lt_or_gt_of_ne (p sun moon (by decide)) with w|w
    · exact ⟨Equiv.swap moon noon,w,z⟩ -- d defeq computable
    exact ⟨(Equiv.swap noon moon).trans (Equiv.swap sun moon),w,k⟩
  rcases lt_or_gt_of_ne (p sun moon (by decide)) with z|z
  · exact ⟨Equiv.swap noon sun,k,z⟩
  rcases lt_or_gt_of_ne (p noon moon (by decide)) with w|w
  · exact ⟨(Equiv.swap noon moon).trans (Equiv.swap sun noon),w,z⟩
  exact ⟨Equiv.swap sun moon,w,k⟩

include f in
private theorem extra (e : 3 ≤ m) (j k : J) :
    ∃ i : J,i≠j ∧ i≠k := by
  by_contra! h
  have t : (Finset.univ : Finset J) ⊆ insert j ({k}:Finset J) := by
    intro a _
    by_cases y:a=j; simp [y]; simp [h a y]
  have ht := (Finset.card_le_card t).trans (Finset.card_insert_le ..)
  simp only [Finset.card_univ,Finset.card_singleton] at ht
  have a := Fintype.card_congr f
  simp only [Fintype.card_fin] at a
  omega

theorem agent_changes (z : Equiv.Perm Pos) (w : Triple (slot h g l)) (i : Pos) :
    note ((agent z plusRow) w) i =
      if i=z noon then replace_ (note w (z sun)) (note w (z noon)) else note w i := by
  change note (mark (note (addRow (mark _)) ∘ ⇑z.symm)) i=_
  rw [noted]
  obtain ⟨a,rfl⟩ := z.surjective i
  change note (addRow _) _ = _
  rw [Equiv.symm_apply_apply]
  cases a <;> simp only [addRow,note,mark,Function.comp_apply,
    Equiv.apply_eq_iff_eq]
  all_goals simp

omit [Fintype J] in
private theorem utility (q : Pos → J) (e : Function.Injective q)
    (v : J → slot h g l) (w : Triple (slot h g l)) (a : Pos) :
    Function.update (Function.update (Function.update v (q sun) w.1)
        (q noon) w.2.1) (q moon) w.2.2 (q a) = note w a := by
  cases a <;> simp [note,e.eq_iff]

omit [Fintype J] in
theorem remap (z : Equiv.Perm Pos) (q : Pos → J) (e : Function.Injective q)
    (j k : J) (u : q (z sun)=j) (t : q (z noon)=k) (v : J→slot h g l) :
    let w := (agent z plusRow) (mark (v ∘ q))
    Function.update (Function.update (Function.update v (q sun) w.1)
        (q noon) w.2.1) (q moon) w.2.2 =
    Function.update v k (replace_ (v j) (v k)) := by
  intro w
  funext i
  by_cases m : ∃ a:Pos,q a=i
  · obtain ⟨a,rfl⟩ := m
    rw [utility q e _ _ a]
    dsimp only [w]
    rw [agent_changes,noted,← t,← u,Function.update_apply] -- dep dite
    by_cases h : a=z noon
    · subst a; simp
    simp [h, show q a≠q (z noon) from fun v0 => h (e v0)]
  simp only [not_exists] at m
  simp [← t,show ∀ a:Pos,i≠q a from fun a hh=>m a hh.symm]

variable (j k : J)
/-- Full stream venue with three slots sorted; spectator regions consist of a constant
number of slots, so unary controls for their Tape shape stay polynomial. -/
theorem playfield (e : 3 ≤ m) (u : j≠k) :
    ∃ a b c : ℕ, ∃ z : Equiv.Perm Pos, -- a b c = physical positions
      ∀ P T : Tape, ∀ h g l, let v := Packed.slot h g l
        let x := Track (chunks h g) (l+1)
        ∀ d : Tape, Seal x d →
        ∃ t : Rig (order P T (threads x f))
          (P++Rack d a) (Rack d (b-a-1))
          (Rack d (c-b-1)) (Rack d (m-c-1) ++ T) x,
          ∀ i : Base P T (J→v), Rig.serve t i ((agent z plusRow) (Rig.why t i))=
            (i.1,Function.update i.2.1 k (replace_ (i.2.1 j) (i.2.1 k)),i.2.2) := by
  obtain ⟨w,g,h⟩ := extra f e j k
  let p₀ := (j,k,w)
  let q := note p₀
  have z : Function.Injective q := by
    intro a b m
    cases a <;> cases b
    all_goals simp [q,note,p₀,u,g,h,g.symm,h.symm,u.symm] at *
  obtain ⟨z',a,b⟩ := sorting f q z
  let s := q ∘ z'
  refine ⟨(f (s sun)).val,(f (s noon)).val,(f (s moon)).val,z'.symm,fun P T p H l D en => ?_⟩
  obtain ⟨n,i,k'⟩ := stair (P:=P) (T:=T) f _ _ _ a b en
  refine ⟨n,fun x => ?_⟩
  erw [k',i]
  change (x.1,_,x.2.2)=(x.1,_,x.2.2)
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  have hp (a) : s (z'.symm a)=q a := by simp [s]
  exact remap z'.symm s (z.comp z'.injective) j k (hp sun) (hp noon) _
end Phase

end IntegerMultiplication
end Computability
end OAI
