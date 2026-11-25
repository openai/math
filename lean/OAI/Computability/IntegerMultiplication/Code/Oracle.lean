import OAI.Computability.IntegerMultiplication.Code.Train
import Mathlib

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Prog
variable {X Y Z : Type*}
def Meter (env : Env) (c : Cmd) (p q : Deck) (w : ℝ) :=
  ∃ n : ℕ, (n:ℝ) ≤ w ∧ Fits env c p q n
namespace Meter
variable {env : Env} {a b : Cmd} {p q r} {w u : ℝ}
theorem mono (e : Meter env a p q w) (h : w ≤ u) : Meter env a p q u := by
  obtain ⟨n,d,e⟩ := e; exact ⟨n,d.trans h,e⟩
theorem cast {n} (e : Fits env a p q n) : Meter env a p q n := ⟨n,le_rfl,e⟩
theorem join (i : Meter env a p q w) (h : Meter env b q r u) :
    Meter env (.join a b) p r (w+u+2) := by
  obtain ⟨n,d,i⟩ := i; obtain ⟨k,e,h⟩ := h
  exact ⟨_,by push_cast; linarith,i.join h⟩
theorem opened {i x y f w r} (h : Meter env a (pile i x (pile i y r)) q w) :
    Meter env (splitRoot i f a) (pile i (.fork x y) r) q (w+4) := by
  obtain ⟨n,e,d⟩ := h; exact ⟨_,by push_cast; linarith,fits_pair d⟩
theorem tagged {i r a} {f : Bool → Cmd} (h : Meter env (f a) r q w) :
    Meter env (splitRoot i f b) (pile i (.atom a) r) q (w+4) := by
  obtain ⟨n,e,d⟩ := h; exact ⟨_,by push_cast; linarith,fits_bit d⟩
end Meter
structure Oracle (X : Type*) where
  fare : X → ℝ
  query : X → Tree
  reply : X → Tree

def Oracle.reserve (o : Oracle X) (l : List X) := (l.map o.fare).sum
@[simp] theorem Oracle.cat (o : Oracle X) (l r : List X) :
    o.reserve (l++r)=o.reserve l + o.reserve r := by simp [Oracle.reserve]

def Acc (env : Env) (c : Cmd) (p q : Tree) (m : ℝ) :=
  ∀ r, Meter env c (pile 0 p r) (pile 0 q r) m

/-- In-scope procedure using a bounded list of calls to growing-time procedure;
'local time' excludes exactly call time, but includes .again overhead. Lists are
multisets for this purpose. All passed commands MUST execute with foreign ancestor
env; all Fits-based algorithms carrying ∀env proof can thus be run without change. -/
structure Tunnel (o : Oracle X) (w : Y → ℝ) (allow : Y → List X) (p q : Y → Tree) : Prop where
  pos : ∀ x, 1≤w x
  build :
    ∃ (c : Cmd) (K : ℕ), ∀ (x : Y) (parent : Cmd) (env : Env) (D : ℕ),
      (∀ y∈allow x, Acc (parent::env) parent (o.query y) (o.reply y) ((D:ℝ)*o.fare y)) →
        Acc (parent::env) c (p x) (q x) ((K:ℝ)*w x + (D:ℝ)*o.reserve (allow x))
namespace Tunnel
variable {o : Oracle X} {w u : Y → ℝ} {a b : Y → List X} {p q r : Y → Tree}
theorem walkway (h : Sized w p q) : Tunnel o w (fun _ => []) p q := by
  obtain ⟨i,d,⟨c,K,e⟩,J,v⟩ := h
  refine ⟨i,c,K*J,fun x parent env D _ z => ?_⟩
  refine (Meter.cast (e x (parent::env) z)).mono ?_
  simp [Oracle.reserve]; rw [mul_assoc]
  gcongr
  exact v x

theorem slide (h : Tunnel o w a p q) (f : Z → Y) :
    Tunnel o (w ∘ f) (a ∘ f) (p ∘ f) (q ∘ f) := by
  obtain ⟨e,c,K,u⟩ := h
  exact ⟨fun _ => e _, c,K,fun _ => u _⟩

theorem join (f : Tunnel o w a p q) (g : Tunnel o w b q r) :
    Tunnel o w (fun i => a i ++ b i) p r := by
  obtain ⟨d,c,K,h⟩ := f
  obtain ⟨_,m,U,z⟩ := g
  refine ⟨d,.join c m,K+U+2,fun x par E D allow j => ?_⟩
  have e := (h x par E D (fun y hy => allow y (List.mem_append.mpr (.inl hy))) j).join
    (z x par E D (fun y hy => allow y (List.mem_append.mpr (.inr hy))) j)
  apply e.mono
  rw [Oracle.cat]; push_cast; have := d x; linarith

theorem summon (f : Y → X) (d : ∀ x,1≤w x) :
    Tunnel o w (fun x => [f x]) (o.query ∘ f) (o.reply ∘ f) := by
  refine ⟨d,.again 0,2,fun x par E D q j => ?_⟩
  obtain ⟨n,h,v⟩ := q (f x) (by simp) j
  apply (Meter.cast v.again0).mono
  simp [Oracle.reserve]
  have := d x; linarith

theorem surround (h : Tunnel o w a p q) (l : Y → Tree) :
    Tunnel o w a (fun x => Tree.fork (p x) (l x)) (fun x => Tree.fork (q x) (l x)) := by
  obtain ⟨i,c,K,g⟩ := h
  refine ⟨i,splitRoot 0 (fun _ => .pass) (.join c (pack 0)),K+12,fun x par env D t j => ?_⟩
  apply (Meter.opened ((g x par env D t _).join (Meter.cast (fits_pack ..)))).mono
  push_cast; have := i x; linarith

theorem fork (d : Y→Bool) (h : Tunnel o (fun x : {x // d x=false} => w x) (fun x => a x)
      (fun x => p x) (fun x => q x))
    (g : Tunnel o (fun x : {x // d x=true} => w x) (fun x => a x) (fun x => p x) (fun x => q x)) :
    Tunnel o w a (fun x => .fork (.atom (d x)) (p x)) q := by
  obtain ⟨i,c,K,h⟩ := h
  obtain ⟨j,m,V,g⟩ := g
  have e (x : Y) : 1 ≤ w x := by cases d' : d x <;> first | exact i ⟨x,d'⟩ | exact j ⟨x,d'⟩
  refine ⟨e,splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun i => bif i then m else c) .pass),
    K+V+8,fun x par env D t s => ?_⟩
  cases d' : d x
  · apply (Meter.opened (Meter.tagged (f:=fun i => bif i then m else c)
      (a:=false) (h ⟨x,d'⟩ par env D t s))).mono
    dsimp only; push_cast; have := e x
    have : 0≤(V:ℝ)*w x := mul_nonneg (by positivity) (by linarith)
    linarith
  apply (Meter.opened (Meter.tagged (f:=fun i => bif i then m else c) (a:=true)
    (g ⟨x,d'⟩ par env D t s))).mono
  dsimp only; push_cast; have := e x
  have : 0≤(K:ℝ)*w x := mul_nonneg (by positivity) (by linarith)
  linarith

end Tunnel
end Code

end IntegerMultiplication
end Computability
end OAI
