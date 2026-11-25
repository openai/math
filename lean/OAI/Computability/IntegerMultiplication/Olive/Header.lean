import OAI.Computability.IntegerMultiplication.Olive.Static

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Code
open Rivulet Dusk Grid Echo Cone Cap Brief Staff IntegerMultiplication.Fourier Carry
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)
variable (a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
variable (P:Faculty n)(B:P.release n r)
abbrev modN(i:I):=modulus (n i) (a i)

-- repeated index access utility
theorem acquire {Y:Type}[Codec Y] (y:Y){k:I→ℕ}(f:(i:I)→Fin (k i)→Y)
    (i:(x:I)→Fin (k x))(t:r.Has fun x=>List.ofFn (f x))(v:Realizes r (fun x=>(i x).val)):
    r.Has (fun x=> f x (i x)) := by
  have h := (Regime.Has.pair t (g:=fun x=>List.ofFn (f x)) (f:=fun x=>Code.tally (i x).val) v).ez (Iter.facile y)
  simpa only [Iter.entry] using h

include A B
theorem startA (x:(i:I)→Spot (axio n a i))(y:(i:I)→Spot (modN n a i))
    (u:Realizes r (fun i=>(x i).val))(v:Realizes r (fun i=>(y i).val)):
    r.Has (fun i=>mark (P.widen i (a i) (x i) (y i))) := by
  have R:= acquire [] (fun i(a:Direction (n i))=>List.ofFn fun j: Spot (criterion (n i) a)=>
    List.ofFn fun k:Spot (modulus (n i) a)=> Dusk.mark (P.widen i a j k)) a B.A A
  exact acquire ([],[]) _ y
    (acquire [] (fun i j=>List.ofFn fun k:Spot (modN n a i)=>mark (P.widen i (a i) j k)) x R u) v

theorem startB (e:Bool)(x y:(i:I)→Spot (modN n a i))
    (u:Realizes r (fun i=>(x i).val))(v:Realizes r (fun i=>(y i).val)):
    r.Has (fun i=>mark (P.narrow e i (a i) (x i) (y i))) :=
  let R:= acquire [] (fun i(a:Direction (n i))=>List.ofFn fun j:Spot (modulus (n i) a)=>List.ofFn
    fun k:Spot (modulus (n i) a)=>mark (P.narrow e i a j k)) a (B.B e) A
  acquire ([],[]) _ y (acquire [] (fun i j=>List.ofFn (fun k=>mark (P.narrow e i (a i) j k)))
    x R u) v
-- lift Faculty naturally
omit A
variable {J:Type} {f:J→I} {r':Regime J}
variable {Y:Type}
abbrev daughter (f:J→I) : Faculty (n ∘ f):=
  { widen:=fun j=>P.widen (f j)
    narrow:=fun i j=>P.narrow i (f j)
    bank:=fun j=>P.bank (f j) }
theorem babies (a:∀ p:I→Tree,r.Small p→ r'.Small (p ∘ f)):
    (daughter n P f).release (n ∘ f) r':=
  ⟨a _ B.A,fun i=>a _ (B.B i),a _ B.C⟩
variable (o:I→ℤ)(H:Realizes r (fun i=>(wrap (modN n a i) (o i)).val))
abbrev yo (i:I)(k:Fin (modN n a i)):=wrap (modN n a i) (rep k+o i)

omit B in
theorem jump (H:Realizes r (fun i=>(wrap (modN n a i) (o i)).val))
    (D:Realizes r (modN n a))(x:(i:I)→Fin (modN n a i))(v:Realizes r (fun i=>(x i).val)):
    Realizes r (fun i=>(yo n a o i (x i)).val):= by
  have g := (v.plus H).rem D
  have M(i:I):((x i).val+(wrap (modN n a i) (o i)).val)% (modN n a i) =
      (yo n a o i (x i)).val:=by
    zify
    change (rep (x i)+ rep (wrap _ _))%_=rep (wrap _ _)
    rw [rep_wrap,rep_wrap]
    simp [Int.add_emod]
  simp_rw [M] at g; exact g
abbrev plane(i:I)(x:Fin (axio n a i)) := yo n a o i (river (s:=modN n a i) x)
abbrev strokeA(i:I)(x:Fin (axio n a i)):= P.widen i (a i) x (plane n a o i x)
-- strokeB pad
abbrev strokeB(e:Bool)(i:I)(x:Fin (axio n a i)) : G (n i):=
  Echo.hair (s:=modN n a i) (fun v:Fin (modN n a i)=> P.narrow e i (a i) v (yo n a o i v)) x

include A T H
abbrev rigA i:= List.ofFn (coupon n a (strokeA n a P o) i)
theorem vesselA :
    r.Has (rigA n a P o) := by
  let k:= axio n a
  have K:Realizes r k:=RoomLine.targetSize a ⟨T.toCalendar,A⟩
  apply harvest k K
  let v:=at_ k
  let π : Regime (Across k):=signal k K
  let G:= Scale.RoomLine.levels a (r:=r) (show RoomLine r n a from ⟨T.toCalendar,A⟩) k K
  have Z:= floor_ k K
  have E:= babies n P B (r':=π) (f:=v) (sendRoof _ _)
  let y:(i:Across k)→ Fin (modN n a i.1):= fun i=>river (s:=modN n a i.1) (i.2)
  have F:Realizes π (fun i=>(y i).val):=
    ((G.sourceSize _).times Z).dividing (G.targetSize _)
  have j:Regime.Has π (fun (i:Across k)=>Dusk.mark (strokeA n a P o i.1 i.2)) :=
    startA (n ∘ v) (fun i=>a i.1) G.aux_ (daughter n P v) E (fun i=>i.2) _ Z
      (jump (n ∘ v) (fun i=>a i.1) (o ∘ v) (landing k K _ H) (G.sourceSize _) y F)
  exact Regime.Has.pair (f:=fun (i:Across k)=>Dusk.mark (strokeA n a P o i.1 i.2)) (g:=fun i=>Code.tally ((Scale.F ∘ (n ∘ v)) i)) -- fix notation
    (G.toCalendar.fraction (n ∘ v)) j
abbrev rigB (e:Bool)(i:I):=List.ofFn (coupon n a (strokeB n a P o e) i)
omit T H A B
private theorem zero (i:I→ℕ)(g:Realizes r i):
    r.Has (fun x=> mark (0:Grain (i x))) := by
  let Z (x):Bits.Word:= Bits.phrase (i x+1) 0
  have t : r.Has Z:= (Figure.natural 0).phrase_ (g.plus (Realizes.fix 1)) (fun _=>by positivity)
  have j (x:I): (Z x,Z x)=Dusk.mark (0:Grain (i x)) := by simp [Z,Dusk.mark,Dusk.trip] -- simp?
  simp_rw [← j]; exact t.pair t
include A T H B
theorem vesselB (e:Bool):
    r.Has (rigB n a P o e) := by
  let G : RoomLine r n a:=⟨T.toCalendar,A⟩
  let k:= axio n a
  let K:Realizes r k:= G.targetSize a
  apply harvest k K
  let v:=at_ k
  let π:Regime (Across k):=signal k K
  have H' := G.levels a k K
  have J:= floor_ k K
  have E:= babies n P B (r':=π) (f:=v) (sendRoof _ _)
  let s:= modN n a
  let z (i:Across k):Fin (s i.1):=⟨i.2.val%(s i.1),Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩
  have u:Realizes π (fun i=>(z i).val):= J.rem (H'.sourceSize _)
  let X(i:Across k):=Dusk.mark (P.narrow e i.1 (a i.1) (z i) (yo n a o i.1 (z i)))
  have q : π.Has X:= startB (n ∘ v) (fun i=>a i.1) H'.aux_ (daughter n P v) E e _ _ u
    (jump (n ∘ v) (fun i=>a i.1) (o ∘ v) (landing k K _ H) (H'.sourceSize _) z u)
  let W:=Scale.W ∘ (n ∘ v)
  let y(i:Across k):= Dusk.mark (0:Grain (W i))
  have c: π.Has y:= zero W (H'.toCalendar.format _)
  obtain ⟨f,A,h⟩:= J.below (H'.sourceSize _)
  have e0:= (A.pair (c.pair q)).ez (Easy.ifst Easy.fst Easy.snd)
  have V(i:Across k): (bif f i then X i else y i) = Dusk.mark (strokeB n a P o e i.1 i.2):= by
    have E:=h i
    unfold strokeB hair
    cases g:f i <;> dsimp [g,X]
    · rw [dite_eq_right]; rfl; intro b; have := E.mp b; simp_all
    rw [dite_eq_left (show i.2.val< modN n a i.1 from E.mpr g)]
    have t0:i.2.val<s i.1:= E.mpr g
    have t1:z i=(⟨i.2.val,t0⟩:Fin (modN n a i.1)):=Fin.ext (Nat.mod_eq_of_lt t0)
    rw [t1]
    simp
  exact Regime.Has.pair (g:=fun i=> Code.tally ((Scale.F ∘ (n ∘ v)) i)) (f:=fun (i:Across k)=>Dusk.mark (strokeB n a P o e i.1 i.2))
    (H'.toCalendar.fraction _) (by simp_rw [← V]; exact e0)
end Olive

end IntegerMultiplication
end Computability
end OAI
