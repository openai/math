import OAI.Computability.IntegerMultiplication.Code.Auto
import OAI.Computability.IntegerMultiplication.Code.Repeat
import Mathlib.Tactic.Ring

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code

variable {X Y Z : Type*}

/-- A (pointwise) polynomial budget uniformly over a domain measured by p. -/
def Dom (p t : X → ℕ) : Prop :=
  ∃ k C : ℕ, ∀ x, t x ≤ C*(p x+1)^k

namespace Dom
variable {p a b : X → ℕ} {d : Y → X}

theorem mono (h : Dom p a) (e : ∀ x, b x≤a x) : Dom p b := by
  obtain ⟨k,C,h⟩ := h
  exact ⟨k,C,fun x => (e x).trans (h x)⟩

theorem map (h : Dom p a) (d : Y→X) : Dom (fun y => p (d y)) (fun y => a (d y)) := by
  obtain ⟨k,C,h⟩ := h; exact ⟨k,C,fun x => h _⟩

theorem const (p : X → ℕ) (i : ℕ) : Dom p (fun _ => i) := ⟨0,i,by simp⟩

theorem base (p : X → ℕ) : Dom p p := ⟨1,1,by simp⟩

theorem upper {k j : ℕ} (h : k≤j) (C p : ℕ) :
    C*(p+1)^k ≤ C*(p+1)^j := by gcongr; omega

theorem add (h : Dom p a) (e : Dom p b) : Dom p (fun x => a x+b x) := by
  obtain ⟨k,C,h⟩ := h
  obtain ⟨j,B,e⟩ := e
  refine ⟨k+j,C+B,fun x => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((h _).trans (upper (by omega) ..)) ((e _).trans (upper (by omega) ..))

theorem mul (h : Dom p a) (e : Dom p b) : Dom p (fun x => a x*b x) := by
  obtain ⟨k,C,h⟩ := h
  obtain ⟨j,B,e⟩ := e
  refine ⟨k+j,C*B,fun x => (Nat.mul_le_mul (h _) (e _)).trans (Nat.le_of_eq ?_)⟩
  rw [pow_add]
  ring

theorem pow (h : Dom p a) (n : ℕ) : Dom p (fun x => (a x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const p 1
  | succ n ih =>
    simpa only [pow_succ] using ih.mul h

/-- Substitution of the bounding size itself. -/
theorem sub (h : Dom b a) (e : Dom p b) : Dom p a := by
  obtain ⟨k,C,h⟩ := h
  exact ((const p C).mul ((e.add (const p 1)).pow k)).mono h

end Dom

namespace Task
variable {p t : X → ℕ} {v u : X → Tree}

/-- Package claims for which we explicitly provide polynomial time in a parameter. -/
def BT (p : X → ℕ) (x y : X → Tree) : Prop :=
  ∃ t, Dom p t ∧ Task t x y

namespace BT
theorem mono (h : BT t v u) (e : Dom p t) : BT p v u := by
  obtain ⟨a,g,r⟩ := h
  exact ⟨a,g.sub e,r⟩

theorem map (h : BT p v u) (g : Y→X) :
    BT (fun i => p (g i)) (fun i => v (g i)) (fun i => u (g i)) := by
  obtain ⟨t,h,r⟩ := h; exact ⟨_,h.map g,r.on g⟩

theorem compose {s : X → Tree} (h : BT p v u) (e : BT p u s) :
    BT p v s := by
  obtain ⟨a,g,r⟩ := h; obtain ⟨b,j,w⟩ := e
  exact ⟨_,g.add j,r.compose w⟩

theorem length (h : BT p v u) (g : Dom p fun i => (v i).count) :
    Dom p fun i => (u i).count := by
  obtain ⟨a,h,e⟩ := h; obtain ⟨C,e⟩ := e.sizeBound
  exact (g.add ((Dom.const _ _).mul (h.add (Dom.const _ _)))).mono e
end BT
end Task

open _root_.OAI.Computability.IntegerMultiplication.Code.Task (BT)

variable [Codec X] [Codec Y] [Codec Z]

@[fun_prop]
def Poly (f : X → Y) : Prop :=
  BT size send (fun i => send (f i))

theorem Easy.poly {f : X → Y} (h : Easy f) : Poly f :=
  ⟨size,Dom.base _,h⟩

-- if query input size budget p (ghost)
theorem Poly.on {U : Type*} {f : X → Y} {q : U → X} (h : Poly f) {p : U → ℕ}
    (e : Dom p fun i => size (q i)) : BT p (fun i => send (q i)) (fun i => send (f (q i))) :=
  (Task.BT.map h q).mono e

theorem Poly.of_bound {f : X → Y} {p : X → ℕ} (h : Computes p f) (e : Dom size p) : Poly f :=
  ⟨p,e,h⟩

namespace Poly

@[fun_prop]
theorem identity : Poly (fun i : X => i) := Easy.identity.poly

@[fun_prop]
theorem const (y : Y) : Poly (fun _ : X => y) := (Easy.const _).poly

theorem length {f : X → Y} (h : Poly f) : Dom size (fun x => size (f x)) := Task.BT.length h (Dom.base _)

@[fun_prop]
theorem compose {f : X → Y} {g : Y → Z}
    (h : Poly f) (e : Poly g) : Poly (fun x => g (f x)) :=
  Task.BT.compose h (e.on h.length)

@[fun_prop]
theorem fstCompose {f : X → Y × Z} (h : Poly f) : Poly (fun x => (f x).1) :=
  h.compose Easy.fst.poly
@[fun_prop]
theorem sndCompose {f : X → Y × Z} (h : Poly f) : Poly (fun x => (f x).2) :=
  h.compose Easy.snd.poly

theorem onleft {f : X → Y} (h : Poly f) : Poly (fun i : X × Z => (f i.1,i.2)) := by
  obtain ⟨c,e,g⟩ := h
  exact .of_bound ((g.on Prod.fst).left (fun i : X × Z => send i.2)) ((e.map _).sub ((Dom.base _).mono (by simp; omega)))

@[fun_prop]
theorem pair {f : X → Y} {g : X → Z} (h : Poly f) (e : Poly g) :
    Poly (fun x : X => (f x,g x)) :=
  (Easy.clone.poly.compose h.onleft).compose ((Easy.exchange.poly.compose e.onleft).compose Easy.exchange.poly)

@[fun_prop]
theorem cons : Poly (fun i : X × List X => i.1::i.2) := Easy.cons.poly

@[fun_prop]
theorem rev {f : X → List Y} (h : Poly f) : Poly (fun x => (f x).reverse) :=
  h.compose Easy.reverse.poly

@[fun_prop]
theorem app {f g : X → List Y} (h : Poly f) (e : Poly g) : Poly (fun x => f x ++ g x) :=
  (h.pair e).compose Easy.append.poly

-- alternative choice via boolean tags
@[fun_prop]
theorem choose {v : X → Bool} {f g : X → Y} (h : Poly v) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => bif v x then f x else g x) :=
  (h.pair (hf.pair hg)).compose ((Easy.ifst (Y:=Y) (X:=Y×Y) Easy.snd Easy.fst).poly)

end Poly

end Code

end IntegerMultiplication
end Computability
end OAI
