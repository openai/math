import OAI.Computability.IntegerMultiplication.Strip.Narrow
import OAI.Computability.IntegerMultiplication.Strip.Adopt

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Thin
open Strip Code
open Code.Task
variable {I X Y : Type} {w : I→ℝ} {z : I→Tree}
variable {S T U V : I→Type}
-- structures with unit budget arbitrary
def Roll {A:I→Type} (w:I→ℝ) (z:I→Tree) (s:(i:I)→Series (A i)) :=
  Carries w z (fun i=> send (tally (s i).count))
namespace Roll
variable (s:(i:I)→Series (S i))
theorem rate (r : Roll w z s) : ∃ D:ℕ,∀ i,(s i).count ≤ (D:ℝ)*w i := by
  obtain ⟨D,t⟩ := r.out
  refine ⟨D,fun i=> ?_⟩
  specialize t i
  change (size (tally _):ℝ) ≤ _ at t
  rw [size_tally,tally_length] at t; push_cast at t
  linarith [Nat.cast_nonneg (α:=ℝ) ((s i).count)]
end Roll
-- sufficient cheap area
-- static size fixed nonempty
structure Rim (w : I→ℝ) (z:I→Tree) (s:(i:I)→Series (S i)) : Prop where
  pay : Roll w z s
  li (i):1≤(s i).count

namespace Rim
variable (s : (i:I)→Series (S i)) (t:(i:I)→Series (T i))
theorem rigid (u : Series X) (h : Volume w z) (d : ∀i,1≤w i) (g : 1≤u.count) :
    Rim w z (fun _=>u) :=
  ⟨fixture h d (send (tally _)),fun _=>g⟩
theorem mulR (a : Rim w z s) (b : Rim w z t)
    (h : ∃ D : ℕ,∀ i, (s i).count*(t i).count ≤ (D:ℝ)*w i) :
    Rim w z (fun i=>(s i).cart (t i)) := by
  have d : ∃ D:ℕ,∀ i,((s i).count+1:ℝ)*((t i).count+1)≤(D:ℝ)*w i := by
    obtain ⟨D,h⟩ := h; refine ⟨4*D,fun i=>?_⟩
    push_cast; specialize h i
    have y : (1:ℝ)≤(s i).count := by exact_mod_cast a.li i
    have x : (1:ℝ)≤(t i).count := by exact_mod_cast b.li i
    calc
     _ ≤ ((s i).count:ℝ)*2*((t i).count*2) := by gcongr <;> linarith
     _ ≤ _ := by linarith
  refine ⟨?_,fun i=> ?_⟩
  · have c := row_data s t (a.pay.twice b.pay) d
    have q := c.chain (Carries.func (y:=fun i=>List.replicate (s i).count (tally (t i).count)) c.budget c.out List.flatten Easy.flatten)
    simpa only [Function.comp_def,Rim,Roll,Dims.tallies, Series.count_cart] using q
  rw [Series.count_cart]
  exact Nat.mul_pos (a.li i) (b.li i)
theorem fixR (a : Rim w z s) (u : Series X) (h:1≤u.count) :
    Rim w z (fun i=> (u.cart (s i))) := by
  obtain ⟨D,d⟩ := Roll.rate s a.pay
  exact mulR _ _ (rigid u a.pay.small a.pay.budget h) a ⟨u.count*D,fun i=> by
    push_cast; rw [mul_assoc]; gcongr; exact d i⟩
theorem capR (a : Rim w z s) (u : Series X) (h:1≤u.count) :
    Rim w z (fun i=> ((s i).cart u)) := by
  obtain ⟨D,d⟩ := Roll.rate s a.pay
  exact mulR _ _ a (rigid u a.pay.small a.pay.budget h) ⟨u.count*D,fun i=> by
    push_cast; rw [mul_assoc]; rw [mul_comm ((s i).count:ℝ) ↑u.count]; gcongr; exact d i⟩
end Rim
variable (s : (i:I)→Series (S i)) (t:(i:I)→Series (T i))
variable (S₀:Series X)
variable (h : Rim w z s)
variable (d : Rim w z t)
variable (u : Rim w z (fun i=> (s i).cart (t i)))

private theorem area {p g:I→ℕ} (a : ∀ i,1≤p i) (b : ∀ i,1≤g i) (k:ℕ)
    (h : ∃ D:ℕ,∀ i,(p i:ℝ)*g i ≤ (D:ℝ)*w i) :
    ∃ E:ℕ,∀ i, ((k:ℝ)*(p i:ℝ)+1)*(g i+1) ≤ (E:ℝ)*w i := by
  obtain ⟨D,t⟩ := h
  refine ⟨(k+1)*2*D,fun i=> ?_⟩
  have P : (1:ℝ)≤p i := by exact_mod_cast a i
  have t₁ : (1:ℝ)≤g i := by exact_mod_cast b i
  specialize t i
  calc
   _ ≤ ((k:ℝ)+1)*p i*((g i:ℝ)*2) := by gcongr <;> linarith
   _ = ((k:ℝ)+1)*2*((p i:ℝ)*g i) := by ring
   _ ≤ _ := by push_cast; rw [mul_assoc _ (D:ℝ)]; gcongr

include h d u
theorem trail
    (x : (i:I)→X× S i×T i→Tree)
    (a : Carries w z (stackRun (fun i=>S₀.cart ((s i).cart (t i))) x))
    (p : 1≤S₀.count) :
    Carries w z (stackRun (fun i=> (s i).cart (S₀.cart (t i))) fun i v=> x i (v.2.1,v.1,v.2.2)) := by
  let A i := Adopt.rotate S₀ (s i) (t i)
  let B i := Adopt.rotate (s i) S₀ (t i)
  have ag : Carries w z (stackRun (fun i=>(S₀.cart (s i)).cart (t i)) (fun i=> x i ∘ (A i).cast)) := by
    unfold stackRun at *; simpa only [(A _).packet] using a
  obtain ⟨D,d₁⟩ := Roll.rate _ u.pay
  have hg := area h.li d.li S₀.count (p:=fun i=>(s i).count) (g:=fun i=>(t i).count) (w:=w) ⟨D,fun i=>by
    simpa only [Series.count_cart,Nat.cast_mul] using d₁ i⟩
  have y := carve (fun i=>S₀.cart (s i)) t _ ag ((Rim.fixR s h S₀ p).pay.twice d.pay) (by simpa only [Series.count_cart,Nat.cast_mul] using hg)
  have v := Strip.sink S₀ s _ y h.pay
  have c := flatten (fun i=>(s i).cart S₀) t (fun i a=> x i (a.1.2,a.1.1,a.2)) v -- expects x curried, v defeq?
  unfold stackRun
  simp_rw [(B _).packet]
  exact c

theorem antTrail
    (x : (i:I)→S i× X ×T i→Tree)
    (a : Carries w z (stackRun (fun i=>(s i).cart (S₀.cart (t i))) x))
    (p : 1≤S₀.count) :
    Carries w z (stackRun (fun i=> S₀.cart ((s i).cart (t i))) fun i v=> x i (v.2.1,v.1,v.2.2)) := by
  let A i := Adopt.rotate (s i) S₀ (t i)
  let B i := Adopt.rotate S₀ (s i) (t i)
  have ag : Carries w z (stackRun (fun i=>((s i).cart S₀).cart (t i)) (fun i=> x i ∘ (A i).cast)) := by
    unfold stackRun at *; simpa only [(A _).packet] using a
  obtain ⟨D,d₁⟩ := Roll.rate _ u.pay
  have hg := area h.li d.li S₀.count (p:=fun i=>(s i).count) (g:=fun i=>(t i).count) (w:=w) ⟨D,fun i=>by
    simpa only [Series.count_cart,Nat.cast_mul] using d₁ i⟩
  have y := carve (fun i=>(s i).cart S₀) t _ ag ((Rim.capR s h S₀ p).pay.twice d.pay) (by
    simpa only [Series.count_cart,Nat.cast_mul,mul_comm (S₀.count:ℝ) ((s _).count:ℝ)] using hg)
  have v := Strip.bubble S₀ s _ y h.pay
  have c := flatten (fun i=>S₀.cart (s i)) t (fun i a=> x i (a.1.2,a.1.1,a.2)) v
  unfold stackRun
  simp_rw [(B _).packet]; exact c
end Thin

end IntegerMultiplication
end Computability
end OAI
