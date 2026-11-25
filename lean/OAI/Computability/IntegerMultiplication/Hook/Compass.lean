import OAI.Computability.IntegerMultiplication.Hook.Inlet

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Strip Loom Strip.Dims Code Adic Packed Net Net.Tensor Net.Walsh Earth Staff Phase Axon
variable {p t:Tape} {f g k m : ℕ}
noncomputable section

abbrev st (f k:ℕ) := Adic.field 2 (f*k)
abbrev deckland (f k:ℕ) : Seal (useD f k) (st f k) := atoms f k
abbrev spanned (i:Fin g) : Single (useD f k) (st f k) g i := Loom.pick _ _ (deckland f k) _
abbrev colH (u:Fin g) := (spanned (f:=f) (k:=k) u).shape.exit (deckland f m)
abbrev colT' := (Slot.sole (useD f m)).enter (cup f g k)
theorem learn (v : Fin g) (x : col f g k m) :
    (colH v).read x=x.1 v :=
  (Slot.exit_read ..).trans (Single.who ..)
theorem classT (x : col f g k m) :
    colT'.read x = x.2 := rfl
theorem learn_r (u : Fin g) (x : col f g k m) (v) :
    (colH u).alter x v=(Function.update x.1 u v,x.2) := by
  rcases x with ⟨w₁,w₂⟩; exact (Slot.exit_alter ..).trans (congrArg (fun v=> (v,w₂)) (Single.put ..))
theorem classT_r (x : col f g k m) (v):
    colT'.alter x v = (x.1,v) := by
  rcases x with ⟨i,c⟩; exact Slot.enter_alter ..

-- under p t
abbrev baz (p t : Tape) (f g k m : ℕ) := Base p t (col f g k m)
private def tucked {K : ℕ} {v b : Tape} (d : Slot (colT f g k m) v (useD f K) b) :
    Slot (Loom.Board p (colT f g k m) t) (p++v) (useD f K) (b++t) :=
  (d.exit (Adopt.same _)).enter (Adopt.same _)
private theorem tucked_r {K : ℕ} {v b : Tape} (d : Slot (colT f g k m) v (useD f K) b)
    (x : baz p t f g k m) :
    (tucked d).read x=d.read x.2.1 := rfl
private theorem tucked_w {K : ℕ} {v b:Tape} (d : Slot (colT f g k m) v (useD f K) b)
    (x : baz p t f g k m) (y) :
    (tucked d).alter x y=(x.1,d.alter x.2.1 y,x.2.2) := by
  rcases x with ⟨x,w,u⟩
  rw [tucked,Slot.enter_alter,Slot.exit_alter]
def browser : baz p t f g k m≃(Pin p × Pin t) × Scr (Fin f) (Ht g k m) where
  toFun x := ((x.1,x.2.2),legend x.2.1)
  invFun x := (x.1.1,legend.symm x.2,x.1.2)
  left_inv x := by simp
  right_inv x := by simp

-- export
abbrev colPrefix (i:Fin g) := Rack (st f k) (spanned (f:=f) (k:=k) i).before
abbrev colPost (i:Fin g) := Rack (st f k) (spanned (f:=f) (k:=k) i).after ++ st f m
abbrev colStart (f g k:ℕ) := Adic.field 2 (g*(f*k)) ++ []
def notch (i:Fin g) : Slot (Phase.order p t (colT f g k m)) (p++colPrefix (f:=f) (k:=k) i) (useD f k)
    ((colPost (f:=f) (k:=k) (m:=m) i)++t) := tucked (colH i)
def final_ : Slot (Phase.order p t (colT f g k m)) (p++colStart f g k)
    (useD f m) ([]++t) := tucked colT'

theorem sees (u:Fin g) (j : Fin k) :
    Stream (notch (p:=p) (t:=t) (f:=f) u) (browser (m:=m))
      (knot g k m (.inl (u,j))) j where
  can x s := by rw [notch,tucked_r,learn]; exact (wears x.2.1 (s,.inl (u,j))).symm
  report x y := by
    set e := knot g k m with de
    change ((_,_),legend _)=((_,_),_)
    rw [notch,tucked_w,learn_r,tucked_r,learn]
    dsimp only
    congr 1; funext s i
    obtain ⟨i,rfl⟩ := e.surjective i
    rcases i with ⟨q,l⟩|l
    · change legend _ s (e (.inl (q,l)))=Function.update (legend x.2.1 s) ((knot g k m) _) (y s) _
      rw [show ∀ x,legend x s (e (.inl (q,l)))=layBit _ (x.1 q s) l from fun x=>wears x (s,.inl (q,l))]
      dsimp only [Prod.fst]
      by_cases h : q=u
      · subst q; rw [Function.update_self]
        change layBit _ ((layBit _).symm _) _=_
        rw [Equiv.apply_symm_apply]
        by_cases h:l=j
        · subst l
          rw [Function.update_self]
          change y s = Function.update (legend x.2.1 s) (e (.inl (u,j))) (y s) (e (.inl (u,j)))
          rw [Function.update_self]
        rw [Function.update_of_ne h,Function.update_of_ne (show e (.inl (u,l)) ≠ e (.inl (u,j)) by simp [h])]
        exact (wears x.2.1 (s,.inl (u,l))).symm
      rw [Function.update_of_ne h,Function.update_of_ne (show e (.inl (q,l))≠e (.inl (u,j)) by simp [h])]
      exact (wears x.2.1 (s,.inl (q,l))).symm
    · change legend _ s (e (.inr l))=Function.update (legend x.2.1 s) ((knot g k m) _) (y s) _
      rw [Function.update_of_ne (show e (.inr l)≠e (.inl (u,j)) by simp)]
      rw [show ∀ (x:col f g k m),legend x s (e (.inr l))=layBit _ (x.2 s) l from fun x=> wears x (s,.inr l)]
      exact (wears x.2.1 (s,.inr l)).symm
theorem wrapUp (i:Fin m) :
    Stream (final_ (p:=p) (t:=t) (f:=f)) browser (knot g k m (.inr i)) i where
  can x s := by rw [final_,tucked_r]; exact (wears x.2.1 (s,.inr i)).symm
  report x y := by
    let e := knot g k m
    change ((_,_),legend _)=((_,_),_)
    rw [final_,tucked_w,classT_r,tucked_r,classT]
    dsimp only
    congr 1; funext s j
    obtain ⟨j,rfl⟩ := e.surjective j
    rcases j with ⟨u,q⟩ | q
    · change legend _ s (e (.inl (u,q)))=Function.update (legend x.2.1 s) ((knot g k m) _) (y s) _
      rw [Function.update_of_ne (show e (.inl (u,q))≠knot g k m (.inr i) by change e _≠ e _; simp)]
      exact (show ∀ (a:col f g k m),legend a s (e (.inl (u,q)))=layBit _ (a.1 u s) q from
        fun x=> wears x (s,.inl (u,q))) _ |>.trans (wears x.2.1 (s,.inl (u,q))).symm
    · change legend _ s (e (.inr q))=Function.update (legend x.2.1 s) ((knot g k m) _) (y s) _
      rw [show ∀ (x:col f g k m),legend x s (e (.inr q))=layBit _ (x.2 s) q from fun x=> wears x (s,.inr q)]
      change layBit _ ((layBit _).symm _) q=_
      rw [Equiv.apply_symm_apply]
      by_cases h : q=i
      · subst q; simp [e]
      rw [Function.update_of_ne h,Function.update_of_ne (show e (.inr q) ≠knot g k m (.inr i) by change e _≠ e _; simp [h])]
      exact (wears x.2.1 (s,.inr q)).symm

end
end Hook

end IntegerMultiplication
end Computability
end OAI
