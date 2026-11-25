import OAI.Computability.IntegerMultiplication.Larch.Split

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Larch
open Param Scale Halo Strip Dims Loom Phase Echo Cap IntegerMultiplication.Fourier
variable {n:ℕ} (h:Season n)
private abbrev D:= Rack [wall n] (Focn n)
private abbrev Belt (n:ℕ) := Loom.park (Series.natural (wall n)) [wall n] (t_s _) (Focn n)
private abbrev CapS :=
  (((Slot.sole (Series.natural (Param.room n))).enter (Belt n)).exit (t_s (wall n))).arrive (cult h)
private abbrev CapE :=
  ((Slot.sole (Peace n)).enter (((Belt n).split (t_s _)).thenDo (unite (D (n:=n)) [Param.room n]))).arrive (cult h)
variable (x:primeV n)(y:sucV n)(z:dayV n)
theorem near_ne (a:Scouts n):
    near h≠rook a:=fun e=>by have q:=congrArg (@Fin.val (lanes n)) e; change Focn n=a.val at q; have := a.isLt; omega
theorem rear_ne (a:Scouts n):
    rear h≠rook a:=fun e=>by have q:=congrArg (@Fin.val (lanes n)) e; change Focn n+1=a.val at q; have := a.isLt; omega
theorem near_e:near h≠rear h:=fun e=>by have q:=congrArg (@Fin.val (lanes n)) e; change Focn n=Focn n+1 at q; omega

theorem near_j (t:Fin (S (near h))):
    uX h x (Fin.cast (near_s h) t) z= Echo.alter (uX h x y z) (near h) t := by
  refine funext (Halo.cases_ h (fun a=>uX h x _ z a=Echo.alter (uX h x y z) (near h) t a) ?_ ?_ ?_)
  · intro v
    rw [Echo.alter,Function.update_of_ne (near_ne h _).symm]
    apply Fin.ext; change numeral h _ _=numeral h _ _; simp
  · rw [Echo.alter,Function.update_self]
    apply Fin.ext; exact numeralS h _
  rw [Echo.alter,Function.update_of_ne (near_e h).symm]; apply Fin.ext
  change numeral h _ _=numeral h _ _; simp
theorem rear_j (t:Fin (S (rear h))):
    uX h x y (Fin.cast (rear_f h) t)= Echo.alter (uX h x y z) (rear h) t := by
  refine funext (Halo.cases_ h (fun a=>uX h x y _ a=Echo.alter (uX h x y z) (rear h) t a) ?_ ?_ ?_)
  · intro v
    rw [Echo.alter,Function.update_of_ne (rear_ne h _).symm]
    apply Fin.ext; change numeral h _ _=numeral h _ _; simp
  · rw [Echo.alter,Function.update_of_ne (near_e h)]; apply Fin.ext
    change numeral h _ _=numeral h _ _; simp
  rw [Echo.alter,Function.update_self]
  apply Fin.ext; exact numeralR h _

def narrow:Vista h (near h) where
  p:=D++[]
  q:= []++[wall n]
  cam:= rail (near_s h).symm (CapS h)
  sees v:=by
    obtain ⟨⟨⟨x,y⟩,z⟩,rfl⟩:= (culture h).surjective v
    rw [lookrail,CapS,Slot.pull]
    rw [show (culture h) ((x,y),z)=uX h x y z from rfl,cult_r]
    rw [Slot.exit_read,Slot.enter_read,Slot.sole_check]
    apply Fin.ext; exact (numeralS h (x,y,z)).symm
  gives v a:=by
    obtain ⟨⟨⟨x,y⟩,z⟩,rfl⟩:= (culture h).surjective v
    rw [feel,CapS]
    apply (cult h).cast.injective
    rw [show culture h ((x,y),z)=uX h x y z from rfl, ← near_j,Slot.endorse,cult_r,cult_r,Slot.exit_alter,Slot.enter_alter,Slot.sole_exchange]
  span_:=by rw [List.append_nil,sizeR]; simp [Dims.room,Halo.near]

def last_:Vista h (rear h) where
  p:= (D++[Param.room n])++[]
  q:=[]
  cam:=rail (rear_f h).symm (CapE h)
  sees v:=by
    obtain ⟨⟨⟨x,y⟩,z⟩,rfl⟩:= (culture h).surjective v
    rw [lookrail,CapE,Slot.pull]
    rw [show (culture h) ((x,y),z)=uX h x y z from rfl,cult_r,Slot.enter_read,Slot.sole_check]
    apply Fin.ext; exact (numeralR h (x,y,z)).symm
  gives v a:=by
    obtain ⟨⟨⟨x,y⟩,z⟩,rfl⟩:= (culture h).surjective v
    rw [feel,CapE]
    apply (cult h).cast.injective
    rw [show culture h ((x,y),z)=uX h x y z from rfl, ← rear_j,Slot.endorse,cult_r,cult_r,Slot.enter_alter,Slot.sole_exchange]
  span_:=by rw [List.append_nil,room_cat,sizeR]; simp [Dims.room,Halo.rear]

noncomputable def frame (a:Direction n): Vista h a := Classical.choice
  (Halo.cases_ h (fun a=>Nonempty (Vista h a)) (fun i=>⟨front h i⟩) ⟨narrow h⟩ ⟨last_ h⟩ a)

end Larch

end IntegerMultiplication
end Computability
end OAI
