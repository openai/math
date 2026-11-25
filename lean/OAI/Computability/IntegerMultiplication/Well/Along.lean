import OAI.Computability.IntegerMultiplication.Well.Mist
import OAI.Computability.IntegerMultiplication.Larch.Stroke
import OAI.Computability.IntegerMultiplication.Moira.Cube

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Well
open Halo Param Scale Brief Strip Code Dims Larch Cap Echo Loom
open Moira Bureau Staff Carry
variable {I:Type}
variable (n:I→ℕ)
variable {r: Regime I}(T:Origin n r)(h:(i:I)→Season (n i))
variable (a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
noncomputable section
abbrev vv (i:I):=frame (h i) (a i)
abbrev prefixL(i:I):= Dims.layout (vv n h a i).p
abbrev suffixL(i:I):=Dims.layout (vv n h a i).q
abbrev axio(i:I):= Larch.S (a i)
abbrev mid_(i:I):= Series.natural (axio n a i)
def shine (i:I): Adopt (Halo.walk (h i)) (((prefixL n h a i).cart (mid_ n a i)).cart (suffixL n h a i)) :=
  ((vv n h a i).cam.view).thenDo (Adopt.rotate _ _ _).back

theorem volume (i:I):
    ct (prefixL n h a) i * (axio n a i) * ct (suffixL n h a) i = load (n i) := by
  rw [← Bureau.census (h i),(shine n h a i).cost]
  rw [Series.count_cart, Series.count_cart,Series.count_natural] -- maybe

abbrev rig (i:I):= Halo.Tri (n i)
abbrev fctor (f:(i:I)→Tri (n i)→Tree)(i:I)(x:Pin (vv n h a i).p)(y:Fin (axio n a i))(z:Pin (vv n h a i).q):Tree:=
  f i ((shine n h a i).cast.symm ((x,y),z))
abbrev text (f:(i:I)→Tri (n i)→Tree):= fun i=>stripe (Halo.walk (h i)) (f i)
theorem faith (f:(i:I)→Tri (n i)→Tree):
    raw (prefixL n h a) (mid_ n a) (suffixL n h a) (fctor n h a f)=text n h f :=
  funext (fun i=> by
    unfold raw; rw [(shine n h a i).packet]
    apply congrArg (stripe _); funext x; exact congrArg (f i) (Equiv.symm_apply_apply (shine n h a i).cast x))

-- axis license
abbrev preC:=ct (prefixL n h a)
abbrev endC:=ct (suffixL n h a)
abbrev lic:= Atlas n (prefixL n h a) (mid_ n a) (suffixL n h a)
theorem passport : lic n h a where
  l i:=by
    have v:= volume n h a i
    have u:= Nat.pow_pos (n:=Param.total (n i)) (by decide :(0:ℕ)<2)
    by_contra! k; rw [show ct (prefixL n h a) i=0 by omega] at v; simp [load] at v; omega
  m i:=by rw [ct,mid_,Series.count_natural]; exact Nat.pos_of_ne_zero (NeZero.ne _)
  p i:=by
    have z:=volume n h a i
    by_contra! c; rw [show ct (suffixL n h a) i=0 by omega] at z
    simp [load] at z; have := Nat.pow_pos (n:=Param.total (n i)) (by decide:(0:ℕ)<2); omega
  total i:=by
    change ct _ _ *(Series.natural _).count* ct _ _≤ _; rw [Series.count_natural,volume n h a]
    exact Nat.le_mul_of_pos_right _ (budget_p _)

include T A
abbrev room_ : Calendar r n:= T.toCalendar -- include def parameter? references T
abbrev line_ : RoomLine r n a := ⟨room_ n T,A⟩
theorem target: Realizes r (axio n a):=RoomLine.targetSize a (line_ n T a A)
theorem Pt : Figure r (ct (mid_ n a)) := by
  unfold ct mid_
  simp_rw [Series.count_natural]
  exact Figure.of_spoken (target n T a A)
theorem know : Figure r (preC n h a) := by
  let d:=fun i=>(a i).val
  let v:= wall ∘ n
  have e: Realizes r v := T.localRoom
  let l:= Focn ∘ n
  have k:Realizes r l:=T.guide.positions n
  have Q : Figure r (fun i=> (v i)^(d i)) := (Figure.of_spoken e).repeated A
  have W : Figure r (fun i=> (v i)^(l i)* Param.room (n i)) :=
    ((Figure.of_spoken e).repeated k).multiplied (T.guide.side_short n)
  have uC := (k.plus (Realizes.fix 1))
  have R : Classified r (fun i=>d i=l i+1) :=
    ⟨_, (Regime.Has.pair A uC).ez (Iter.linked (X:=Unit) (Y:=Unit)),
      fun i=> by simp only [d,l, Function.comp_def, Staff.box,tally_length,decide_eq_true_eq]⟩
  unfold preC ct prefixL
  simp only [Dims.space,Vista.span_]
  exact W.variant Q R
theorem sure : Figure r (endC n h a):= by
  let u i:= Param.load (n i)
  have p : Figure r u:=(Figure.natural 2).repeated (T.guide.exSize n)
  have w:=know n T h a A
  have V: Figure r (axio n a):=Figure.of_spoken (target n T a A)
  have q(i): u i/(preC n h a i*axio n a i)=endC n h a i:=by
    unfold u; rw [← volume n h a i,Nat.mul_div_cancel_left]; exact Nat.mul_pos
      ((passport n h a).l i) (Nat.pos_of_ne_zero (NeZero.ne _))
  have E:=p.quotients (w.multiplied V)
  simp_rw [q] at E; exact E
end
end Well

end IntegerMultiplication
end Computability
end OAI
