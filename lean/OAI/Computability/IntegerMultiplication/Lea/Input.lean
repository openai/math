import OAI.Computability.IntegerMultiplication.Lea.Ruler
import OAI.Computability.IntegerMultiplication.Partial

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Lea
open Param Scale Code Strip Bureau Cap Echo Dusk Cone Brief Dune Staff Carry Bits
noncomputable section
-- msb
variable {I:Type}(n:I→ℕ)(h:∀ i,Season (n i))(x:I→Word)(hx:∀ i,(x i).length=n i)
abbrev rays(i:I):Hint (n i)→Word:=crop (P (n i)) (boxes (n i)) (x i).reverse
abbrev lot(i:I):=value ∘ rays n x i
abbrev water(i:I): GrainV (n i):= fluid (n i) ∘ lot n x i
theorem cardP(i:I)(j:Hint (n i)): (rays n x i j).length=P (n i):= (crop_ ..).1 j
theorem lotP(i:I)(j:Hint (n i)):lot n x i j<2^P (n i):= (cardP n x i j) ▸ value_lt (rays n x i j)

include h hx
theorem scoreR(i:I):score (radix (P (n i))) (lot n x i)= bitValue (x i):= by
  rw [endianness]
  refine scoreV _ _ _ ?_
  rw [List.length_reverse,hx]
  exact enough_x (h i)
theorem sparseR (i:I)(j:Hint (n i))(e:Param.amount (n i)≤j.val): lot n x i j=0:= by
  refine emptyCrop (P (n i)) (boxes (n i)) _ (Param.amount (n i)) ?_ ?_ j e
  · rw [List.length_reverse,hx]; exact budget_times (n i)
  rw [List.length_reverse,hx]; exact enough_x (h i)

-- data transfer
variable {Z:Type}[Codec Z]
omit hx h [Codec Z] in
theorem repeat_ (x:Z)(a:ℕ):List.replicate a x=List.ofFn (fun (_:Fin a)=>x):= by
  apply List.ext_getElem (by simp); intro; simp
omit hx h in
theorem maskLock {X Y Z:Type}[Codec X][Codec Y][Codec Z]{m:ℕ}(x:X)(y:Y)(g:X×Y→Z)(t:Fin m→X)(p:Y):
    lock g x y (List.ofFn t,List.replicate m p)= List.ofFn (fun a=>g (t a,p)):= by
  have e {Z:Type}(q:Fin m→Z): (Series.natural m).tab q=List.ofFn q:=by
    change (List.finRange m).map _=_
    apply List.ext_getElem (by simp); intro; simp
  rw [repeat_,← e,← e,← e,paired]
theorem loomso :
    Wood n (send ∘ x) (Lexi n (water n x)) := by
  have E:=sizeInput n x hx
  let a:= scoop E
  have J:= me E
  let p:= P ∘ n; let k:=tagK n
  have L:= (a.chain (planT n h _ (tagP n) 1 (fun i=>Nat.le_mul_of_pos_left _ (le_refl 1)))).twice (a.chain (periodT n h))
  have V:=L.twice (J.chain (Carries.func J.budget J.out List.reverse Easy.reverse))
  have V': Wood n (send ∘ x) (fun i=>send (List.ofFn (rays n x i))):= by
    let y i:= ((List.replicate (k i) (Code.tally (p i)),Code.tally (k i*p i)),(x i).reverse)
    have q:= V.chain (Carries.func V.budget (show Volume (token n) (send ∘ y) from V.out) saw sawE)
    unfold Function.comp at q
    simp_rw [y,sawn] at q
    exact q
  let J₀:=(Scale.birthday h).fraction n
  have W:= a.chain (planT n h _ (dispatch J₀) 4096 (fun i=>le_refl (Scale.F (n i))))
  have w(i):stripT n (Scale.F ∘ n) i=send (List.replicate (k i) (Code.tally (Scale.F (n i)))):=rfl
  have B:= V'.twice W
  let z:I →List Word × List Tally:= fun i=> (List.ofFn (rays n x i),List.replicate (k i) (Code.tally (Scale.F (n i))))
  have G:=B.chain (Carries.func B.budget (show Volume (token n) (send ∘ z) from B.out) (lock pedal [] []) (easy_lock _ pedalE _ _))
  have Y(i:I): lock pedal ([]:Word) [] (z i)=List.ofFn (Dusk.mark ∘ water n x i):= by
    unfold z k tagK
    dsimp only [Function.comp_apply]
    rw [maskLock (m:=boxes ..)] -- boxes .. fills too much
    congr 1
    funext j
    exact runs (n i) (lotP n x i j)
  simp_rw [Y] at G
  exact G
end
end Lea

end IntegerMultiplication
end Computability
end OAI
