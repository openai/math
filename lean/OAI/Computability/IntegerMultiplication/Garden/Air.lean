import OAI.Computability.IntegerMultiplication.Garden.Walk

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Garden
open Code Brief Grid Staff Strip

variable {I:Type} (r:Regime I)
variable (n k m : I→ℕ) (h:Realizes r n)
abbrev Local_ := Across n
abbrev earth : Local_ n → I := Sigma.fst
abbrev stream (h:Realizes r n) := signal n h
abbrev tick (x:Local_ n) := n x.1
abbrev Wide := Across (tick n)
abbrev sky : Wide n→Local_ n := Sigma.fst
abbrev ocean (h:Realizes r n) := landing n h n h
abbrev tide (h:Realizes r n) := signal (tick n) (ocean r n h)
abbrev casts {X : Type} (f:(i:I)→Fin (n i)→X) (x:Local_ n) : X:= f x.1 x.2
abbrev scales {X : Type} (f:(i:I)→Fin (n i)→Fin (n i)→X) (x:Wide n) := f x.1.1 x.1.2 x.2
structure Academy (x:(i:I)→Scene (n i)) : Prop where
  ray : Signed (stream r n h) (casts n (fun i=>(x i).ray))
  seal_ : Signed r (fun i=>(x i).end_)
  table_: Signed (tide r n h) (scales n fun i=>(x i).square)
variable {r n} {h}
namespace Academy
variable (x:(i:I)→Scene (n i)) (G:Academy r n h x)
include G
theorem prepare (K:Realizes r k) :
    ∃ p:I→Plan,r.Has p ∧ ∀ i,shown (p i) (x i) (k i) := by
  obtain ⟨⟨v,H,e⟩,⟨y,V,t⟩,⟨u,Q,g⟩⟩:=G
  let A (z:Local_ n) (i:Fin (tick n z)):= u ⟨z,i⟩
  let b (i:Local_ n): Brick:= (v i,List.ofFn (A i))
  have U : (stream r n h).Has b :=
    H.pair (harvest _ (ocean r n h) _ Q)
  have p := (harvest n h (fun i a=> b ⟨i,a⟩) U).pair (V.pair (f:=fun i=> tally (k i)) K)
  refine ⟨_,p,fun i=>⟨⟨_,rfl,?_,?_⟩, t _,rfl⟩⟩
  · intro j
    exact ⟨_,rfl,fun c=> g _⟩
  exact fun _=> e _
end Academy
theorem ecology (V:(i:I)→ List S) (q:r.Has V)
    (x:(i:I)→ Fin (n i)→ℤ) (t:∀ i,Lines (V i) (x i)):
    Signed (stream r n h) (casts n x) := by
  have Q : (stream r n h).Has (V ∘ earth n) :=
    sendRoof n h (send ∘ V) q
  have p : (stream r n h).Has (fun i:Local_ n=> tally i.2.val) := floor_ n h
  have T:= (Q.pair p).ez (Iter.facile Z0)
  refine ⟨_,T,fun z=>?_⟩
  obtain ⟨v,H,e⟩:= (t z.1).issued
  dsimp only [Function.comp_apply,earth]
  rw [H,Iter.entry,e]

variable (x:(i:I)→Scene (n i)) (q:(i:I)→Notes (n i))
variable (G:Academy r n h x) (u:Signed r (fun i=>(q i).2))
variable (T:Signed (stream r n h) (casts n (fun i=>(q i).1)))
variable (K:Realizes r k) (M:Realizes r m)
include G u T K M
/-- header exports orbit answers under polynomial unary axis dimension and bit width,
requiring proof each intermediate result fits the supplied bit width. -/
theorem export_ (e:∀ i,∀ j < m i, trim (k i) ((act (x i))^[j+1] (q i))) :
    let v (i:I):= (act (x i))^[m i] (q i)
    Signed (stream r n h) (casts n (fun i=>(v i).1)) ∧ Signed r (fun i=>(v i).2) := by
  obtain ⟨p,H,Q⟩:=G.prepare k x K
  obtain ⟨f,y,t⟩:=T
  obtain ⟨g,P,d⟩:=u
  let L (i:I):F:=(List.ofFn fun a=> f ⟨i,a⟩,g i)
  have hp : ∀ i,frame (L i) (q i) :=
    fun i=>⟨⟨_,rfl,fun _=> t _⟩,d i⟩
  have D : r.Has L :=
    (harvest n h _ y).pair P
  have i:= (Regime.Has.pair (g:=fun i:I=> tally (m i)) M (H.pair D)).thenDo polyOrbit
  have A i:= imprint (Q i) (hp i) (m i) (e i)
  exact ⟨ecology _ (i.ez Easy.fst) _ (fun i=>(A i).1),
    ⟨_,i.ez Easy.snd,fun i=>(A i).2⟩⟩
end Garden

end IntegerMultiplication
end Computability
end OAI
