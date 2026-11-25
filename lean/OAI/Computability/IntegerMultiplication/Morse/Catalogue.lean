import OAI.Computability.IntegerMultiplication.Morse.Tablet
import OAI.Computability.IntegerMultiplication.Halo.Lyric

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Bits Staff Brief Carry
variable {I:Type}{r:Regime I}(k w p:I→ℕ)(q:I→Word)(b:(i:I)→ℕ→Grain (w i))
abbrev page i:= List.ofFn fun t:Fin (2^k i)=>Dusk.mark (b i t)
theorem minister (v:r.Has fun i=>Grid.telex (p i) (k i) (b i)) :
    r.Has (page k w b) := by
  let F : Ask.Card Orb→Dusk.Pair:= fun x=> x.2.2
  have e:= v.ez (Easy.mapping (show Easy F from by unfold F; fun_prop))
  simp only [Grid.telex,List.map_ofFn, F] at e
  exact e

variable (P:Realizes r p)(K:Realizes r k)(D:Realizes r (fun i=>2^k i))(Q:Realizes r (value ∘ q))
    (A:r.Has (page k w b))
theorem circle {x:I→ℕ}(a:Realizes r x) : Figure r (fun i=> 2^x i) :=
  (Figure.natural 2).repeated a
theorem cypress {x y:I→ℕ}(a:Realizes r x) (b:∀i,x i≤y i)(v:Realizes r (fun i=>2^y i)):
    Realizes r (fun i=>2^x i) :=
  (circle a).pay ((diameter _ v).mono (fun i=>Nat.pow_le_pow_right (by decide) (b i)))

include D A
omit D in
theorem position {x:I→ℕ}(a:Realizes r x)(v:∀i,x i<2^k i):
    r.Has (fun i=>Dusk.mark (b i (x i))) := by
  let U := page k w b
  have e:= (A.pair (g:=U) (f:=fun i=>tally (x i)) a).ez (Iter.facile ([],[]))
  have g i: Iter.pick ([],[]) (U i,tally (x i))=Dusk.mark (b i (x i)) :=
    Iter.entry _ (⟨x i,v i⟩:Fin (2^k i)) _
  simpa only [g] using e

-- derive row family under signal across tap. m step
include Q P K
omit K in
theorem row (m v:I→ℕ)(h:∀i,v i+1+m i=k i)(V:Realizes r v)(M:Realizes r m) :
    r.Has (fun i=>rowT (p i) (q i) (inflate (b i) (m i)) (v i)) := by
  simp_rw [script]
  let H i:=2^v i
  have U:Realizes r H := cypress V (by intro i; specialize h i; exact h ▸ (by omega)) D
  apply harvest H U
  let f:=at_ H
  let R:=signal H U
  have X := floor_ H U
  have Y (x:I→ℕ)(a:Realizes r x):Realizes R (x ∘ f):=landing _ _ x a
  have T:(R.Has (page (k ∘ f) (w ∘ f) (fun i=>b i.1))) :=
    sendRoof H U _ A
  let G a : Across H→ℕ:=fun j=>2^(m ∘ f) j*((value (q j.1)*pin a*j.2.val)%2^(v j.1+1))
  have hh (a:B)(j:Across H):
      G a j<2^k j.1 := calc
    _ < 2^(m j.1)*2^(v j.1+1) := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ (by positivity)) (by positivity)
    _ = _:= by rw [← pow_add,Nat.add_comm (m j.1),h j.1]
  have Z(a:B): R.Has (fun i:Across H=> atom (p i.1) (q i.1) (b i.1) (v i.1) (m i.1) a i.2.val) := by
    let E: Realizes r (fun i=>2^(m i)):= cypress M (fun i=>by specialize h i; omega) D
    have N: Realizes r (fun i=>2^(v i+1)):= cypress (V.plus (Realizes.fix 1)) (fun i=>by specialize h i; omega) D
    have q0:Realizes R (G a):=(Y _ E).times (((((Y _ Q).times (Realizes.fix _)).times X).rem (Y _ N)))
    exact Regime.Has.pair (g:=fun i=>tally ((p ∘ f) i)) (Y _ P) (position (r:=R) (k ∘ f) (w ∘ f) _ T q0 (hh a))
  exact Regime.Has.pair (Z 0) (Z 1)

theorem bib :
    r.Has (fun i=> scroll (p i) (q i) (b i) (k i)) := by
  simp_rw [alone]
  apply harvest k K
  let f:=at_ k
  let R:=signal k K
  have y (a:I→ℕ)(x:Realizes r a):Realizes R (a ∘ f):=landing _ _ a x
  have m:=floor_ k K
  exact row (k ∘ f) (w ∘ f) (p ∘ f) (q ∘ f) (fun i=>b i.1)
    (y _ P) (y _ D) (y _ Q) (sendRoof k K _ A) _ _ (by
      intro i; have t:= i.2.isLt; change k i.1-(i.2.val+1)+1+i.2.val=k i.1; change i.2.val<k i.1 at t; omega) ((y _ K).minused (m.plus (Realizes.fix 1))) m

end Morse

end IntegerMultiplication
end Computability
end OAI
