import OAI.Computability.IntegerMultiplication.Olive.Roll

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Code Rivulet Dusk Grid
open Echo Cone Cap Brief Staff IntegerMultiplication.Fourier Dial
open Finset
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)
variable (h:∀ i,Season (n i))(a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
variable (P:Faculty n)(B:P.release n r)
noncomputable section
abbrev θA (i:I):= Radius (Scale.L (n i))
abbrev θB (i:I):= Radius (briefL (n i))
abbrev ψA (i:I)(y:Fin (θA n i))(x:Fx n i):= Echo.street (a i) (give n a (seln n a (fun _=>shift _ y) h) (strokeA n a P (fun _=>shift _ y)) i) x
-- replace define operators on each x without family
abbrev ψB (u:Bool)(i:I)(y:Fin (θB n i))(x:Fx n i):=
  Echo.street (a i) (give n a (end_ n a (fun _=>shift _ y) h) (strokeB n a P (fun _=>shift _ y) u) i) x
abbrev incA(i:I): Fx n i→Fx n i:=
  Echo.street (a i) (Cone.extend_ n P i (h i) (a i))
abbrev incB(u:Bool)(i:I):Fx n i→Fx n i:=
  Echo.street (a i) (Cone.close_ n P i (h i) (a i) u)

structure FigR {X:Type}(n:X→ℕ)(r:Regime X)(i:(x:X)→Direction (n x))(o:X→ℤ)(P:Faculty n):Prop where
  orig: Origin n r
  who:Realizes r (fun x=>(i x).val)
  obj:Realizes r (fun x=>(wrap (modN n i x) (o x)).val)
  emp:P.release n r

include A T B
private theorem hand {D:I→ℕ} (W:Realizes r D)(L:∀i,D i ≤ modN n a i)
    (c:Realizes r (Radius ∘ D)):
    let K:= Radius ∘ D
    let V:= Ctx n K
    let p:= pivot n K
    let R:= rctx n K c
    let O:V→ℤ:= fun v:V=>shift (D (p v)) (Dial.focus K v)
    let y:=n ∘ p
    let E:=fun v:V=>a (p v)
    FigR y R E O (daughter n P p) := by
  let p:=pivot n (Radius ∘ D)
  let y:=n ∘ p
  let R:=rctx n (Radius ∘ D) c
  let E:=fun v=>a (p v)
  let X:=Tr n
  have T0:=slid T (Radius ∘ D) c X
  have S : Realizes R (fun i=> (a (p i)).val) := Well.smooth _ c X A
  refine ⟨T0,S,radius_ y T0 E S (D ∘ p) (Well.smooth (a:=fun i=>send (Code.tally (D i))) _ c X W) (fun x=>L _)
    (fun i=> Dial.focus (Radius ∘ D) i) (Well.spot _ c X),babies n P B (r':=R) (f:=p) (fun x h=> Well.smooth _ c X h)⟩
-- define FigR
omit A B in
theorem stem_data : Realizes r (θA n):=
  ((Realizes.fix 2).times (T.toCalendar.lamp n)).plus (Realizes.fix 1)
omit A B in
theorem stem_meta : Realizes r (θB n):=
  ((Realizes.fix 2).times ((T.toCalendar.drills n).times (T.toCalendar.rate n))).plus (.fix 1)
omit T A B in
private theorem neB i:1≤boundG n i:=by exact_mod_cast tax_pos (Scale.W (n i))

abbrev costS (i:I):= boundG n i*((θA n i:ℝ)+1)
abbrev costB (i:I):=boundG n i*((θB n i:ℝ)+1)
variable (x:(i:I)→Farm (n i))
set_option maxHeartbeats 1000000 in
theorem axisA :
    Mid n r (costS n) (LandN n h x) (LandN n h (fun i=>incA n h a P i (x i))) := by
  let k:=θA n
  let l(i:I):=Scale.L (n i)
  let A0 : Realizes r k:= ((Realizes.fix 2).times (T.toCalendar.lamp n)).plus (.fix 1)
  let t:=pivot n k
  let y:=n ∘ t
  let q(i):=a (t i)
  let H i: Season (y i):= h (t i)
  let o (i:Ctx n k):=shift (l (t i)) (Dial.focus k i)
  let L:=daughter n P t
  have v(i:I): l i ≤ modN n a i:=Nat.le_of_lt ((Nat.le_mul_of_pos_left (l i) (by decide:0<2)).trans_lt ((h i).grass (a i)).1)
  have E:= hand n T a A P B (T.toCalendar.lamp n) v A0
  have p:Ticket n h k A0 (boundG n) (ψA n h a P) :=
    lesson y E.orig H q E.who (seln y q o H) (strokeA y q L o)
      (menu0 y q o) _ (oracleA y E.orig q E.who L E.emp o E.obj H)
      (fun i=>i.1.value.1)
  have K1 := reserve n T h k A0 (boundG n) (fun i=>by exact_mod_cast tax_pos (Scale.W (n i))) (ψA n h a P) p x
  have w i: (∑ j:Fin (k i), ψA n h a P i j (x i))=incA n h a P i (x i) :=
    calc
     _ = ∑ j∈rad (l i),hotN_ n a P h (fun _=>j) x i:=(project (l i) _).symm
     _ = _:=visitA n a P h x i
  simp_rw [w] at K1; exact K1

set_option maxHeartbeats 1000000 in
theorem axisB (u:Bool):
    Mid n r (costB n) (LandN n h x) (LandN n h (fun i=>incB n h a P u i (x i))) := by
  let k:=θB n; let l(i:I):=briefL (n i)
  let A0: Realizes r k:=((Realizes.fix 2).times ((T.toCalendar.drills n).times (T.toCalendar.rate n))).plus (.fix 1)
  let t:=pivot n k
  let y:=n ∘ t
  let q(i):=a (t i)
  let H i: Season (y i):= h (t i)
  let o (i:Ctx n k):=shift (l (t i)) (Dial.focus k i)
  let L:=daughter n P t
  have v (i:I): l i≤ modN n a i:= Nat.le_of_lt ((Nat.le_mul_of_pos_left (l i) (by decide:0<2)).trans_lt ((h i).grass (a i)).2.1)
  have E:=hand n T a A P B ((T.toCalendar.drills n).times (T.toCalendar.rate n)) v A0
  have p:Ticket n h k A0 (boundG n) (ψB n h a P u) :=
    lesson y E.orig H q E.who (end_ y q o H) (strokeB y q L o u)
      (menu1 y q o H) _ (oracleB y E.orig q E.who L E.emp o E.obj H u)
      (fun i=>i.1.value.1)
  have K1:= reserve n T h k A0 (boundG n) (fun i=>by exact_mod_cast tax_pos (Scale.W (n i))) (ψB n h a P u) p x
  have w i : (∑ j:Fin (k i), ψB n h a P u i j (x i))=incB n h a P u i (x i):=
    calc
     _ = ∑ j∈rad (l i),pale n a P h u (fun _=>j) x i:= (project (l i) _).symm
     _ = _:= visitB n a P h x u i
  simp_rw [w] at K1; exact K1
end
end Olive

end IntegerMultiplication
end Computability
end OAI
