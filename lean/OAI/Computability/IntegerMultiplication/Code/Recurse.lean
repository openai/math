import OAI.Computability.IntegerMultiplication.Code.Oracle
import OAI.Computability.IntegerMultiplication.Code.Repeat

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Prog
variable {X Y Z : Type*}
namespace Tunnel
theorem solve (o : Oracle X) {w : X→ℝ} {a : X → List X}
    (h : Tunnel o w a o.query o.reply)
    (pos : ∀ x,1 ≤ o.fare x)
    (hw : ∀ x, w x ≤ o.fare x)
    (eps : ℝ) (he : 0<eps)
    (budget : ∀ x, o.reserve (a x)+eps*o.fare x ≤ o.fare x)
    (height : X→ℕ) (order : ∀ x y, y∈a x → height y < height x) :
    Sized o.fare o.query o.reply := by
  obtain ⟨_,c,K,g⟩ := h
  obtain ⟨D,t⟩ := exists_nat_gt ((K:ℝ)/eps)
  have ke : (K:ℝ) ≤ D*eps := by
    exact ((div_lt_iff₀ he).mp t).le
  have hh (x : X) (env : Env) : Acc (c::env) c (o.query x) (o.reply x) ((D:ℝ)*o.fare x) := by
    suffices hz : ∀ n, ∀ y, height y=n →
        Acc (c::env) c (o.query y) (o.reply y) ((D:ℝ)*o.fare y) by exact hz _ _ rfl
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx r
      specialize g x c env D (fun y hy => ih _ (by rw [← hx]; exact order x y hy) _ rfl) r
      refine g.mono ?_
      calc
       _ ≤ ((D:ℝ)*eps)*o.fare x+D*o.reserve (a x) := by
        have f := pos x
        have wp := hw x
        -- K≥0 w≤fare, Ke, fare≥0
        exact add_le_add (le_trans (by gcongr : (K:ℝ)*w x ≤ (K:ℝ)*o.fare x)
          (mul_le_mul_of_nonneg_right ke (by linarith))) (le_refl _)
       _ ≤ _ := by
        rw [mul_assoc, ← mul_add,add_comm (eps*o.fare x)]
        gcongr; exact budget _
  -- directly wraps Fits, use ceil
  refine ⟨pos,fun x => ⌈(D:ℝ)*o.fare x⌉₊+1, ?_, D+3,fun x => ?_⟩
  · refine ⟨.tie c,1,fun x env r => ?_⟩
    obtain ⟨n,v,e⟩ := hh x env r
    apply (e.tie).mono
    dsimp only; rw [one_mul]
    have : n ≤ ⌈(D:ℝ)*o.fare x⌉₊ := by
      exact_mod_cast v.trans (Nat.le_ceil _)
    omega
  push_cast
  have z := pos x
  have p : 0≤(D:ℝ)*o.fare x := by exact mul_nonneg (by positivity) (by linarith)
  have v := Nat.ceil_lt_add_one p
  linarith

theorem drift (o : Oracle X) {w : X→ℝ} {a : X → List X}
    (h : Tunnel o w a o.query o.reply)
    (tight : ∀ x, w x + o.reserve (a x) ≤ o.fare x)
    (height : X→ℕ) (order : ∀ x y, y∈a x → height y < height x)
    (e : ∀ x, 1≤o.fare x) :
    Sized o.fare o.query o.reply := by
  obtain ⟨_,c,K,g⟩ := h
  have hh (x : X) (env : Env) : Acc (c::env) c (o.query x) (o.reply x) ((K:ℝ)*o.fare x) := by
    suffices hz : ∀ n, ∀ y, height y=n →
        Acc (c::env) c (o.query y) (o.reply y) ((K:ℝ)*o.fare y) by exact hz _ _ rfl
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx r
      apply (g x c env K (fun y hy => ih _ (by rw [← hx]; exact order x y hy) _ rfl) r).mono
      rw [← mul_add]; gcongr; exact tight _
  refine ⟨e,fun x => ⌈(K:ℝ)*o.fare x⌉₊+1, ?_, K+3,fun x => ?_⟩
  · refine ⟨.tie c,1,fun x env r => ?_⟩
    obtain ⟨n,v,d⟩ := hh x env r
    apply (d.tie).mono
    dsimp only; rw [one_mul]
    have : n ≤ ⌈(K:ℝ)*o.fare x⌉₊ := by exact_mod_cast v.trans (Nat.le_ceil _)
    omega
  push_cast
  have z := e x
  have v := Nat.ceil_lt_add_one (show 0≤(K:ℝ)*o.fare x from mul_nonneg (by positivity) (by linarith))
  linarith
end Tunnel

namespace Sized
variable {w s : X → ℝ} {p f : X → Tree}
theorem suspend (g : X → Task.Event X)
    (h : Sized w p fun x => Task.Event.signal p f x (g x)) (hg : ∀ x, Task.Event.sound p f x (g x))
    (ss : ∀ x : X,1 ≤ s x)
    (ht : ∀ x : X, w x + (match g x with | .done => 0 | .jump y => s y | .ask y _ z => s y+s z) ≤ s x) :
    Sized s p f := by
  obtain ⟨po,b,d,D,v⟩ := h
  have pr (x) : 0 ≤ (D:ℝ)*s x := by
    exact mul_nonneg (by positivity) (by have := ss x; linarith)
  let m := fun x => ⌊(D:ℝ)*s x⌋₊
  have eq (x) : b x + 1 + Task.Event.more m (g x) ≤ m x := by
    unfold m; rw [Nat.le_floor_iff (pr x)]
    push_cast
    specialize ht x; specialize v x
    have he := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α:=ℝ) D)
    cases e : g x with
    | done =>
      rw [e] at he; simp only [add_zero] at he; simpa [Task.Event.more] using le_trans v he
    | jump y =>
      rw [e] at he
      dsimp only [Task.Event.more] at *
      rw [mul_add] at he
      linarith [Nat.floor_le (pr y)]
    | ask y _ z =>
      rw [e] at he
      dsimp only [Task.Event.more] at *
      push_cast; simp_rw [mul_add] at he
      linarith [Nat.floor_le (pr y),Nat.floor_le (pr z)]
  refine ⟨ss,m, Task.loop g d hg eq,D+1,fun x => ?_⟩
  push_cast
  dsimp [m]
  linarith [ss x,Nat.floor_le (pr x)]

end Sized
end Code

end IntegerMultiplication
end Computability
end OAI
