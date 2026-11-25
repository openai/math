import OAI.Computability.IntegerMultiplication.Phase.Venue

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Walsh Strip Strip.Optic Strip.Dims Packed Loom
variable {J X : Type} [Fintype J] [DecidableEq J]
variable (j k : J)
variable {P T G C S Y : Tape} {h g m n b : ℕ}
local notation "a_" => joint P T h g J n
-- changing all occurrences of a selected row
abbrev rebind (x y : Screen h g (Fin n)) : Screen h g (Fin n) :=
  fun i => bind (x i) (y i)
def urge (e : k≠j) : Equiv.Perm (Panels P T h g J n) :=
  field a_ (project (convey j (lad k) (by simp [lad,e.symm])))

theorem urge_atom (x y : Chunk h g) :
    pulse.symm ((pulse y).1+(pulse x).1,(pulse y).2) = bind x y := by
  suffices w : ∀ a b : Fin 2, ((a : ZMod 2)+b)=other a b by
    change (((y.1.1,_),y.2):Chunk h g) = _
    exact congrArg (fun z : Fin 2 => ((y.1.1,z),y.2)) (w y.1.2 x.1.2)
  intro a b; fin_cases a <;> fin_cases b <;> decide

omit [Fintype J] in
theorem urge_r (e : k≠j) (x : Panels P T h g J n) :
    urge j k e x = (x.1,Function.update x.2.1 k (rebind (x.2.1 j) (x.2.1 k)),x.2.2) := by
  refine Prod.ext rfl (Prod.ext (funext fun z => funext fun i => ?_) rfl)
  change pulse.symm (((pulse (x.2.1 z i)).1 + lad k z*(pulse (x.2.1 j i)).1),_) = _
  change pulse.symm _ = Function.update x.2.1 k _ z i
  by_cases v : z=k
  · subst z
    simp only [lad,ite_true, one_mul,Function.update_self,rebind]
    exact urge_atom _ _
  simp [lad,v]
  rfl
omit [Fintype J] in
theorem reversed (e : k≠j) :
    ((urge (P:=P) (T:=T) (h:=h) (g:=g) (n:=n) j k e)).symm = urge j k e := by apply Equiv.ext; intro; rfl

omit [Fintype J] in
theorem reform (e : k≠j) (z : Equiv.Perm Pos) (f : J≃Fin m)
    (t : Rig (front P T h g (b+1) f) G C S Y (Track (chunks h g) (b+1)))
    (r : ∀ i,Rig.serve t i ((agent z plusRow) (Rig.why t i))=
            (i.1,Function.update i.2.1 k (replace_ (i.2.1 j) (i.2.1 k)),i.2.2)) i :
    t.cast (urge j k e i) = invoke (agent z plusRow) G C S Y (t.cast i) := by
  rw [urge_r,show rebind (i.2.1 j) (i.2.1 k)=replace_ (i.2.1 j) (i.2.1 k) from rfl]
  rw [← r,go,Rig.why,Rig.set_r]
omit [Fintype J] in
theorem reform_t (e : k≠j) (z : Equiv.Perm Pos) (f : J≃Fin m)
    (t : Rig (front P T h g (b+1) f) G C S Y (Track (chunks h g) (b+1)))
    (r : ∀ i,Rig.serve t i ((agent z plusRow) (Rig.why t i))=
            (i.1,Function.update i.2.1 k (replace_ (i.2.1 j) (i.2.1 k)),i.2.2))
    (F : Panels P T h g J (b+1) → X) :
    (travel (invoke (agent z plusRow) ..) (F ∘ t.cast.symm)) ∘ t.cast =
      travel (urge j k e) F := by
  funext i
  obtain ⟨i,rfl⟩ := (urge j k e).surjective i
  change F (t.cast.symm ((invoke (agent z plusRow) G C S Y).symm _))=_
  rw [reform j k e z f t r,Equiv.symm_apply_apply,Equiv.symm_apply_apply,completed]

def united (j : J) (u : Addr J) (r : u j=0) :
    Equiv.Perm (Panels P T h g J n) :=
  field a_ (project (convey j u r))
abbrev turns (l : List J) := ∀ i∈l,i≠j
def playup : (l : List J) → turns j l → Equiv.Perm (Panels P T h g J n)
| [],_ => Equiv.refl _
| i::l,w => (urge j i (w i List.mem_cons_self)).trans (playup l (fun x h => w x (List.mem_cons_of_mem _ h)))
omit [Fintype J] in
theorem played (l : List J) (w : turns j l) (x) :
    (a_ (playup (P:=P) (T:=T) (h:=h) (g:=g) (n:=n) j l w x)) =
    ((fun i => l.foldl (fun f t => sync j (lad t) f) ((a_ x).1 i)),(a_ x).2) := by
  induction l generalizing x with
  | nil => rfl
  | cons t l ih =>
    rw [playup,Equiv.trans_apply,ih]
    have e : a_ (urge j t (w t List.mem_cons_self) x)=(fun i => sync j (lad t) ((a_ x).1 i), (a_ x).2) := by
      change a_ ((a_).symm _)=_
      rw [Equiv.apply_symm_apply]; rfl
    rw [e]; rfl
theorem team (v : Addr J) (t : v j=1) :
    ∃ l : List J, ∃ w : turns j l,∀ P T h g n,
      playup (P:=P) (T:=T) (h:=h) (g:=g) (n:=n) j l w =
      united j (reduced v j) (forfeit v j t) := by
  obtain ⟨l,w,u⟩ := tape j (reduced v j) (forfeit v j t)
  refine ⟨l,w,fun P T h g n=>Equiv.ext (fun x=>?_ )⟩
  apply (joint _ _ _ _ J _).injective
  rw [played]
  change (_,_)=(joint _ _ _ _ _ _) ((joint P T h g J n).symm _)
  rw [Equiv.apply_symm_apply]
  refine Prod.ext (funext fun i=>?_) rfl
  exact u _
end Phase

end IntegerMultiplication
end Computability
end OAI
