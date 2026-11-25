import OAI.Computability.IntegerMultiplication.Carry.Many
import OAI.Computability.IntegerMultiplication.Carry.Wide
import OAI.Computability.IntegerMultiplication.Staff.Tabs

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Carry
open Code Bits Staff Strip

/- Closed header/setup language for polynomial time binary magnitudes with polynomial bit
length; can mint unary output on demand when the analysis validates its allowance. No random access.
-/
variable {I : Type} (r : Regime I)
def Figure (a : I→ℕ) : Prop := ∃ x:I→Word,r.Has x ∧ ∀ i,Bits.value (x i)=a i
namespace Figure
variable {r}
variable {a b : I→ℕ} (u:Figure r a) (v: Figure r b)
include u
theorem lift1 {f : Word→Word} (p:Poly f) {g:ℕ→ℕ} (t : ∀ x,value (f x)=g (value x)) :
    Figure r (fun i=>g (a i)) := by
  obtain ⟨x,h,e⟩ := u
  exact ⟨f ∘ x,h.thenDo p,by intro i; rw [Function.comp_apply,t,e]⟩
include v
theorem lift2 {f : Two→Word} (p:Poly f) {g:ℕ→ℕ→ℕ}
    (t : ∀ x y,value (f (x,y))=g (value x) (value y)) :
    Figure r (fun i=>g (a i) (b i)) := by
  obtain ⟨x,h,e⟩ := u
  obtain ⟨y,m,z⟩ := v
  exact ⟨fun i=> f (x i,y i),(h.pair m).thenDo p,fun i=> by rw [t,e,z]⟩
omit u v
theorem natural (n:ℕ) :
    Figure r (fun _=>n) := ⟨fun _=>born n,Regime.fixed _,fun _i=>birthValue n⟩
theorem of_spoken (p : Realizes r a) :
    Figure r a := by
  have q := Regime.Has.ez (g:=fun i=>tally (a i)) p easy_chart
  simp only [tally_length] at q
  exact ⟨born ∘ a,q,fun i=>birthValue _⟩
include u v
theorem added : Figure r (fun i=>a i+b i) :=
  lift2 u v swift add_val
theorem subtracted : Figure r (fun i=>a i-b i) :=
  lift2 u v sub0_r sub0_v
theorem multiplied : Figure r (fun i=>a i*b i) :=
  lift2 u v polyTime tm_value
theorem quotients : Figure r (fun i=> a i/b i) :=
  lift2 u v polyND.fstCompose (fun x y=> (division_rules x y).1)
theorem modded : Figure r (fun i=> a i%b i) :=
  lift2 u v polyND.sndCompose (fun x y=> (division_rules x y).2)
theorem compare_ :
    Classified r (fun i=> a i < b i) := by
  obtain ⟨x,h,e⟩:=u
  obtain ⟨y,t,g⟩:=v
  refine ⟨fun i=>decide (a i< b i),?_,by simp⟩
  have t := (h.pair t).thenDo ltPoly
  simpa only [lt_r,e,g] using t
theorem variant {d:I→Prop} [DecidablePred d] (h:Classified r d) :
    Figure r (fun i=> if d i then a i else b i) := by
  obtain ⟨x,t,e⟩:=u; obtain ⟨y,q,v⟩ := v; obtain ⟨k,L,C⟩ := h
  have Z := (L.pair (t.pair q)).ez (condition (X:=Bool×Word×Word) Prod.fst (fun x=>x.2.1) (fun x=>x.2.2) (by fun_prop) (by fun_prop) (by fun_prop))
  refine ⟨_,Z,?_⟩
  intro i; specialize C i; cases h:k i <;> simp_all
theorem maximum : Figure r (fun i=>max (a i) (b i)) := by
  have t := v.variant u (u.compare_ v)
  simpa only [max_def_lt] using t -- max_def vs max_def lt
omit v
theorem rooted : Figure r (fun i=>(a i).sqrt) :=
  lift1 u rescuePoly rescued
theorem repeated (h: Realizes r b) :
    Figure r (fun i=> a i ^ b i) := by
  obtain ⟨x,k,e⟩ := u
  exact ⟨_,(k.pair (g:=x) (f:=fun i=>box (b i)) h).thenDo firesPoly,
    fun i=>by dsimp only; rw [fires_r,e,tally_length]⟩

theorem short_log : Realizes r (fun i=> Nat.clog 2 (a i)) := by
  obtain ⟨x,h,e⟩:=u
  have t := h.thenDo lightPoly
  simpa only [light_v,e,Realizes,Function.comp_def,box] using t

theorem pay (e: Dom r.scale a) :
    Realizes r a := by
  obtain ⟨x,h,t⟩ := u
  have z : r.Small (send ∘ x) := h
  have Z := z.extent.add e
  have Y := rice.on x
  simp only [t] at Y
  exact z.chain ⟨_,Z,Y⟩

theorem write (v:Realizes r b) :
    r.Has (fun i=> short (b i) (a i)) := by
  obtain ⟨x,h,t⟩ := u
  have e := (h.pair (f:=fun i=>box (b i)) v)
    |>.ez (Easy.exchange.compose (easy_resize Easy.identity))
  have q (i:I) : (resize ((x i,box (b i)).swap))= short (b i) (a i) :=
    word_inject _ _ (by rw [short_length]; exact sized_length ..) (by rw [value_short]; exact (sized_low (b i) (x i)).trans (by rw [t]))
  simpa only [id_eq,q] using e

theorem phrase_ (v:Realizes r b) (p:∀ i,a i<2^b i) :
    r.Has (fun i=> phrase (b i) (a i)) := by
  simpa only [short,Nat.mod_eq_of_lt (p _)] using u.write v

omit u
theorem fact (h: Realizes r a) :
    Figure r (fun i=> Nat.factorial (a i)) :=
  ⟨_,Regime.Has.thenDo (g:=fun i=> tally (a i)) h factorCost,fun _i=>factors_v _⟩
end Figure
end Carry

end IntegerMultiplication
end Computability
end OAI
