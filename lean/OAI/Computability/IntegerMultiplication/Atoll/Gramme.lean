import OAI.Computability.IntegerMultiplication.Atoll.Rank

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Strip Loom Cap Dims
variable {d : ℕ}
set_option allowUnsafeReducibility true -- for rewrite transparency
attribute [local reducible] Cap.body Atoll.top Atoll.bot
abbrev digitCoat (k:ℕ): Seal (Series.natural k) [k]:=
  ((Adopt.skip (Series.natural k)).back).thenDo (Adopt.turn ((Series.natural k).cart (layout [])) (Dims.hinge k []))
def Widths : {d:ℕ}→Bounds d→Tape
| 0,_ => []
| _+1,r=>[r 0]++Widths (body r)
def Shallow : {d:ℕ}→Bounds d→Tape
| 0,_=>[]
| _+1,r=>Shallow (body r)++[r 0]
abbrev D0 {d:ℕ}(r:Bounds (d+1)):=body r
def coat : {d:ℕ}→(r:Bounds d)→Seal (top r) (Widths r)
| 0,r=> (Adopt.turn _ (Vacant r)).back
| _d+1,r=>
  (((Adopt.turn _ (Expand r)).back).thenDo ((digitCoat (r 0)).split (coat (body r)))).thenDo
    (Loom.unite [r 0] _)
def coatB : {d:ℕ}→(r:Bounds d)→Seal (bot r) (Shallow r)
| 0,r=> coat r
| _d+1,r=>
  (((Adopt.turn _ (Contract r)).back).thenDo ((coatB (body r)).split (digitCoat (r 0)))).thenDo
    (Loom.unite _ [r 0])

variable (s:Bounds d)(i:Fin d)
structure Shade where
  p:Tape
  q:Tape
  cam:Slot (top s) p (Series.natural (s i)) q
  sees (x):cam.read x=x i
  gives (x)(v:Fin (s i)):cam.alter x v=Function.update x i v
  fee:Dims.room p=base s i
  prior :∀ x y:Vector_ s,(cam.view.cast x).1=(cam.view.cast y).1→∀ j,j < i → x j=y j
structure Shadow where
  p:Tape
  q:Tape
  cam:Slot (bot s) p (Series.natural (s i)) q
  sees (x):cam.read x=x i
  fee:Dims.room q=base s i

variable (s2:Bounds (d+1))
private theorem update_lead (a:Fin (s2 0))(x:Vector_ (body s2))(v):
    Expand s2 (v,x) = Function.update (Expand s2 (a,x)) 0 v:= by
  funext i; refine Fin.cases (by rw [Function.update_self]; rfl) (fun j=>?_) i
  rw [Function.update_of_ne (Fin.succ_ne_zero _)]
  exact Eq.refl _
private theorem update_next (a:Fin (s2 0))(x:Vector_ (body s2))(i:Fin d)(v):
    Expand s2 (a,Function.update x i v)=Function.update (Expand s2 (a,x)) i.succ v:=by
  funext j
  refine Fin.cases ?_ (fun k=>?_) j
  · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero _))]
    rfl
  change Function.update x i v k=_
  by_cases p:k=i
  · subst k; rw [Function.update_self,Function.update_self]
  rw [Function.update_of_ne p,Function.update_of_ne (fun h=>p (Fin.succ_inj.mp h))]
  rfl

private def leading :
    Shade s2 0 :=
  let L:= ((Slot.sole (Series.natural (s2 0))).exit (coat (body s2)))
  let e:= (Adopt.turn _ (Expand s2)).back
  ⟨[],[]++Widths (body s2), L.arrive e,
    fun x=> rfl,
    fun x v=>by
      obtain ⟨⟨a,t⟩,rfl⟩:= (Expand s2).surjective x
      apply e.cast.injective
      rw [← update_lead]
      rw [Slot.endorse]
      change L.alter ((Expand s2).symm _) _= (Expand s2).symm _
      simp only [Equiv.symm_apply_apply, L, Slot.exit_alter, Slot.sole_exchange],
    by simp [Dims.room],fun _ _ _ _ h=>False.elim (Nat.not_lt_zero _ h)⟩
private def trailing :
    Shadow s2 0 :=
  let L:= ((Slot.sole (Series.natural (s2 0))).enter (coatB (body s2)))
  let e:= (Adopt.turn _ (Contract s2)).back
  ⟨Shallow (body s2)++[],[], L.arrive e,fun x=>rfl,by simp [Dims.room]⟩

private def follow (i:Fin d)(b: Shade (body s2) i) :
    Shade s2 i.succ :=
  let L:=b.cam.enter (digitCoat (s2 0))
  let e:Adopt (top s2) _:= (Adopt.turn _ (Expand s2)).back
  ⟨[s2 0]++b.p,b.q,L.arrive e,
    fun x=>by rw [Slot.pull]; change L.read (x 0,bodyV x)=_; simpa only [L,Slot.enter_read] using b.sees (bodyV x),
    fun x v=>by
      obtain ⟨⟨a,t⟩,rfl⟩:= (Expand s2).surjective x
      apply e.cast.injective
      rw [← update_next,Slot.endorse]
      change L.alter ((Expand s2).symm _) _= (Expand s2).symm _
      rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
      simp only [L,Slot.enter_alter,b.gives],
    by rw [room_cat,b.fee];simp [Dims.room],
    fun x y h=>by
      have t : Union [s2 0] b.p ((digitCoat _).cast (x 0),(b.cam.view.cast (bodyV x)).1) =
        Union [s2 0] b.p ((digitCoat _).cast (y 0),(b.cam.view.cast (bodyV y)).1) := h
      have V := (Union [s2 0] b.p).injective t
      intro j
      refine Fin.cases (fun _=>(digitCoat _).cast.injective (congrArg Prod.fst V))
        (fun k h=>b.prior _ _ (congrArg Prod.snd V) _ (Fin.succ_lt_succ_iff.mp h)) j⟩ -- replace
private def followB (i:Fin d)(b: Shadow (body s2) i) :
    Shadow s2 i.succ :=
  let L:=b.cam.exit (digitCoat (s2 0))
  let e: Adopt (bot s2) _:= (Adopt.turn _ (Contract s2)).back
  ⟨b.p,b.q++[s2 0],L.arrive e,
    fun x=>by
      rw [Slot.pull]
      change L.read (bodyV x,x 0)=_
      simpa [L,Slot.exit_read] using b.sees (bodyV x),
    by rw [room_cat,b.fee];simp [Dims.room,Nat.mul_comm]⟩
def window : {d:ℕ}→ (s2:Bounds d)→(i:Fin d)→ Shade s2 i
| 0,_,i=>i.elim0
| _d+1,s2,i=> Fin.cases (leading s2) (fun i=>follow s2 i (window (body s2) i)) i
def drawer : {d:ℕ}→ (s2:Bounds d)→(i:Fin d)→ Shadow s2 i
| 0,_,i=>i.elim0
| _d+1,s2,i=> Fin.cases (trailing s2) (fun i=>followB s2 i (drawer (body s2) i)) i

end Atoll

end IntegerMultiplication
end Computability
end OAI
