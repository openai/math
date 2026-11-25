import OAI.Computability.IntegerMultiplication.Halo.Diagram

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Larch
open Param Scale Halo Strip Dims Loom Phase Echo Cap IntegerMultiplication.Fourier
variable {n:ℕ}
abbrev S (a:Direction n):= criterion n a
abbrev nom (a: Direction n):=Series.natural (S a)
structure Vista (h:Season n) (a:Direction n) where
  p:Tape
  q:Tape
  cam : Slot (Halo.walk h) p (nom a) q
  sees (x:Tri n):cam.read x=x a
  gives (x:Tri n)(t:Fin (S a)):cam.alter x t=Echo.alter x a t
  span_ : Dims.room p=(if a.val=Focn n+1 then (wall n)^(Focn n)*(Param.room n) else (wall n)^a.val)

variable {A B:ℕ}{X:Type} {d:Series X}{P Q:Tape}
-- exact field toggle equal widths, casts preserving read
def rail(h:A=B)(z:Slot d P (Series.natural A) Q): Slot d P (Series.natural B) Q :=
  h ▸ z
theorem lookrail(h:A=B)(z:Slot d P (Series.natural A) Q)(x):
    (rail h z).read x= (finCongr h) (z.read x):= by subst h; rfl
theorem feel(h:A=B)(z:Slot d P (Series.natural A) Q)(x)(y:Fin B):
    (rail h z).alter x y=z.alter x (Fin.cast h.symm y):= by subst B; rfl

def t_s(k:ℕ):Seal (Series.natural k) [k]:=
  ((Adopt.skip (Series.natural k)).back).thenDo (Adopt.turn ((Series.natural k).cart (layout [])) (Dims.hinge k []))
theorem sizeR (d:Tape) (k :ℕ):Dims.room (Loom.Rack d k)=Dims.room d^k:=by
  induction k with
  | zero=>rfl
  | succ k ih=>change Dims.room (_++_)=_; rw [room_cat,ih,pow_succ']

variable (h:Season n)
-- alignment of arbitrary axis. x decomposed via cult
abbrev Quad n := (primeV n×sucV n)×dayV n
abbrev qual (n:ℕ):Series (Quad n):= (Floorplan n).cart (Peace n)
abbrev culture : Quad n≃Tri n:=(Equiv.prodAssoc ..).trans (prism h).symm
abbrev cult: Adopt (Halo.walk h) (qual n):=(Adopt.turn _ (culture h)).back
@[simp] theorem cult_r (x y z): (cult h).cast (uX h x y z) = ((x,y),z):= by
  exact Equiv.symm_apply_apply (culture h) ((x,y),z)
variable (i:Scouts n)(x:primeV n)(y:sucV n)(z:dayV n)
theorem fst_j (t:Fin (S (rook i))):
    uX h (Function.update x i (Fin.cast (rook_f i) t)) y z = Echo.alter (uX h x y z) (rook i) t := by
  apply funext
  intro j
  apply Fin.ext
  refine Halo.cases_ h (fun j=> (uX h (Function.update x i (Fin.cast _ t)) y z j).val=(Echo.alter _ (rook i) t j).val) ?_ ?_ ?_ j
  · intro a
    by_cases v:a=i
    · subst a
      rw [Echo.alter,Function.update_self]
      change numeral h _ (rook i)= _
      rw [numeralP]; dsimp only
      simp
    have U: rook a ≠ rook i := by
      intro g; apply v; apply Fin.ext; exact congrArg (@Fin.val (lanes n)) g
    unfold Echo.alter
    rw [Function.update_of_ne U]
    change numeral h _ (rook a)=numeral h _ (rook a)
    simp [Function.update_of_ne v]
  · rw [Echo.alter,Function.update_of_ne]
    · simp
    intro g
    have q := congrArg Fin.val g
    change Focn n=i.val at q
    have t:=i.isLt
    omega
  rw [Echo.alter,Function.update_of_ne]
  · simp
  intro g; have q:=congrArg Fin.val g; change Focn n+1=i.val at q
  have t:=i.isLt; omega
private abbrev e0 (i:Scouts n) := Loom.pick (Series.natural (wall n)) [wall n] (t_s _) i -- unknown Psys0 use Series.natural
private def pCam(i: Scouts n):
    Slot (Halo.walk h)
      (Loom.Rack [wall n] (e0 i).before) (Series.natural (wall n))
      ((Loom.Rack [wall n] (e0 i).after++ [Param.room n])++[wall n]) :=
  (((e0 i).shape.exit (t_s _) |>.exit (t_s _))).arrive (cult h)
private theorem read_a (v:Tri n):
    (pCam h i).read v=Fin.cast (rook_f i) (v (rook i)):= by
  obtain ⟨⟨⟨x,y⟩,z⟩,rfl⟩:= (culture h).surjective v
  rw [pCam,Slot.pull]
  simp only [show (cult h).cast ((culture h) ((x,y),z))=((x,y),z) from cult_r ..,Slot.exit_read,Single.who]
  exact Fin.ext (numeralP h (x,y,z) i).symm
private theorem alter_a (v:Tri n) (u:Fin (wall n)):
    (pCam h i).alter v u=Echo.alter v (rook i) (Fin.cast (rook_f i).symm u) := by
  obtain ⟨⟨⟨x,y⟩,z⟩,rfl⟩:= (culture h).surjective v
  let y0:Fin (S (rook i)):= Fin.cast (rook_f i).symm u
  have o : Fin.cast (rook_f i) y0=u:=rfl -- proof irrelevance/subtype
  apply (cult h).cast.injective
  rw [show culture h ((x,y),z)= uX h x y z from rfl,← fst_j, pCam,Slot.endorse]
  simp only [cult_r, Slot.exit_alter, Single.put]
  rfl

def front: Vista h (rook i) where
  p:= Rack [wall n] (e0 i).before
  q:= ((Rack [wall n] (e0 i).after++ [Param.room n])++[wall n])
  cam:=rail (rook_f i).symm (pCam h i)
  sees x:=by rw [lookrail,read_a]; rfl
  gives x t:=by rw [feel,alter_a];rfl
  span_:=by rw [sizeR,(e0 i).pos]; rw [ite_eq_right]
            · simp [Dims.room];rfl -- maybe simp
            change i.val≠ Focn n+1; have t:=i.isLt; omega
end Larch

end IntegerMultiplication
end Computability
end OAI
