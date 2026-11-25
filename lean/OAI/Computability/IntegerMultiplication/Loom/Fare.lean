import OAI.Computability.IntegerMultiplication.Strip.Rails
import OAI.Computability.IntegerMultiplication.Loom.Arrivals
import OAI.Computability.IntegerMultiplication.Code.Recurse

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open IntegerMultiplication.Code Strip
variable {I X Y : Type} {r : Regime I} {n l : I→ℕ} {p q v u : I → Tree}

namespace Fatigue
-- elementary consequences
theorem act {X : Type*} [Codec X] [Codec Y] {x : I→X} (h : Rip r n l p (send ∘ x))
    (f : X→Y) (e : Easy f) : Rip r n l p (fun i => send (f (x i))) := by
  obtain ⟨k,h⟩ := h
  exact ⟨k,h.chain (Carries.func h.budget h.out _ e)⟩

theorem dry (s : Series X) (v : I→X→Tree) (p' : Alive r n l p)
    (h : ∀ x,Rip r n l p (fun i => v i x)) :
    Rip r n l p (stackRun (fun _ => s) v) := by
  unfold stackRun
  simp only [stripe_simple]
  induction s.explore with
  | nil =>
    obtain ⟨k,h⟩ := p'
    exact ⟨k,fixture h.out h.budget _⟩
  | cons a w ih => exact (h a).twice ih
theorem drill (s : Series X) (v : I→X→Tree) (h : Rip r n l p (stackRun (fun _ => s) v)) (x) :
    Rip r n l p (fun i => v i x) := by
  obtain ⟨k,h⟩ := h; exact ⟨k,finite_cell s v h x⟩

theorem entire (s : Series X) (v : I→X→Tree)
    (h : ∀ i,1≤n i)
    (z : ∀x, Alive r n l (fun i => v i x)) :
    Alive r n l (stackRun (fun _ => s) v) := by
  unfold stackRun
  simp only [stripe_simple]
  induction s.explore with
  | nil =>
    refine ⟨0,Carries.idles (unit_mass h _) ⟨1,fun i => ?_⟩⟩
    simpa [Task.forest_nil,Tree.count] using unit_mass (l:=l) (r:=r) h 0 i
  | cons a w ih => exact Rip.alivePair (z _) ih
theorem loom {x : (i:I)→Type} (s : (i:I)→Series (x i))
    (b : Series X) (v : (i:I)→X→x i→Tree)
    (h : Rip r n l p (stackRun s (fun i a => stripe b (fun w => v i w a)))) :
    Rip r n l p (stackRun (fun _ => b) (fun i w => stripe (s i) (v i w))) := by
  obtain ⟨k,h⟩ := h
  exact ⟨k,unlay b s v h⟩
theorem blend {x : (i:I)→Type} (s : (i:I)→Series (x i))
    (b : Series X) (v : (i:I)→X→x i→Tree)
    (h : Rip r n l p (stackRun (fun _ => b) (fun i w => stripe (s i) (v i w))))
    (z : Rip r n l p (stackRun s fun _ _ => .atom false)) :
    Rip r n l p (stackRun s (fun i a => stripe b (fun w => v i w a))) := by
  obtain ⟨k,h⟩ := h; obtain ⟨t,z⟩ := z; exact ⟨k+t,lay b s v
    (h.larger (mass_le (by omega : k≤k+t))) (z.larger (mass_le (by omega : t≤k+t)))⟩
end Fatigue

theorem Tunnel.monoT {w e : I→ℝ} {o : Oracle X} {a : I→List X}
    (h : Tunnel o w a p q) (z : ∀ i,w i ≤ e i) :
    Tunnel o e a p q := by
  obtain ⟨y,c,K,b⟩ := h
  exact ⟨fun i => (y i).trans (z i),c,K,fun i parent env D l j => (b i parent env D l j).mono
    (by gcongr; exact z i)⟩

/-- Tape contractors use a job docket even when the cost allocation remains to
be determined. Exponent must be selected independently of choice of allocation. -/
structure Job (X : Type) where
  issue : X → Tree
  reply : X → Tree

structure Quest (j : Job X) (r : Regime I) (n l : I→ℕ) (use : I → List X) (p q : I → Tree) :
    Prop where
  eligible : ∃ k,∀ e,Tunnel ⟨e,j.issue,j.reply⟩ (mass r n l k) use p q

namespace Quest
variable {j : Job X} {Z : Type} {a b : I → List X}
theorem seam (h : Quest j r n l a p q) (f : Quest j r n l b q v) :
    Quest j r n l (fun i => a i ++ b i) p v := by
  obtain ⟨k,h⟩ := h.eligible; obtain ⟨u,f⟩ := f.eligible
  exact ⟨k+u,fun g => IntegerMultiplication.Code.Tunnel.join (Tunnel.monoT (h g) (mass_le (by omega : k≤k+u)))
    (Tunnel.monoT (f g) (mass_le (by omega : u≤k+u)))⟩

theorem entry (h : Rip r n l p q) :
    Quest j r n l (fun _ => []) p q := by
  obtain ⟨k,h⟩ := h
  exact ⟨k,fun _ => Code.Tunnel.walkway h.runs⟩

theorem board (k : I → X) (h : ∀ i,1≤n i) :
    Quest j r n l (fun i => [k i]) (j.issue ∘ k) (j.reply ∘ k) :=
  ⟨0,fun _ => Code.Tunnel.summon k (unit_mass h 0)⟩
theorem pack (h : Quest j r n l a p q) (v : I→Tree) :
    Quest j r n l a (together p v) (together q v) := by
  obtain ⟨k,h⟩ := h.eligible
  exact ⟨k,fun _ => (h _).surround _⟩
theorem hand (h : Quest j r n l a p q) (i : Rip r n l v p) :
    Quest j r n l a v q := by simpa using (entry i).seam h
theorem transfer (h : Quest j r n l a p q) (i : Rip r n l q v) :
    Quest j r n l a p v := by simpa using h.seam (entry i)

/-- conservative lock-step join side, left gets entire parent pack -/
theorem widen (h : Quest j r n l a p q) (v : I→Tree) (g : Rip r n l p v) :
    Quest j r n l a p (together q v) :=
  (h.pack _).hand (g.again.twice g)

end Quest

-- Counted requests, any in address neighborhood γ
structure Hopto (j : Job X) (r : Regime I) (n l : I→ℕ) (zone : I → X → Prop)
    (limit : ℤ) (p q : I→Tree) : Prop where
  safe : ∃ uses : I → List X, (∀ i,∀x∈uses i,zone i x) ∧
    (∀ i, (uses i).length ≤ limit) ∧ Quest j r n l uses p q
namespace Hopto
variable {j : Job X} {e : I → X → Prop} {h f : ℤ}
theorem chain (a : Hopto j r n l e h p q) (b : Hopto j r n l e f q v) :
    Hopto j r n l e (h+f) p v := by
  obtain ⟨c,A,E,K⟩ := a.safe; obtain ⟨d,B,F,L⟩ := b.safe
  exact ⟨fun i => c i ++ d i,fun i x t =>
    Or.elim (List.mem_append.mp t) (A i x) (B i x),fun i => by dsimp; rw [List.length_append]; push_cast; exact add_le_add (E i) (F i),
    K.seam L⟩
theorem monotone (a : Hopto j r n l e h p q) (w : h≤f) :
    Hopto j r n l e f p q := by
  obtain ⟨c,A,E,K⟩ := a.safe
  exact ⟨c,A,fun i => (E i).trans w,K⟩
theorem tarry (a : Rip r n l p q) :
    Hopto j r n l e 0 p q := ⟨fun _ => [],by simp,by simp,Quest.entry a⟩
theorem pack (a : Hopto j r n l e h p q) (v : I→Tree) :
    Hopto j r n l e h (together p v) (together q v) := by
  obtain ⟨c,A,E,K⟩ := a.safe
  exact ⟨c,A,E,K.pack v⟩
theorem preceded (a : Hopto j r n l e h p q) (g : Rip r n l v p) :
    Hopto j r n l e h v q := by simpa using (tarry g).chain a
theorem afterTask (a : Hopto j r n l e h p q) (g : Rip r n l q v) :
    Hopto j r n l e h p v := by simpa using a.chain (tarry g)
theorem doubleg (a : Hopto j r n l e h p q) (b : Hopto j r n l e f p v)
    (o : Alive r n l p) (d : Alive r n l q) (pv : Alive r n l v) :
    Hopto j r n l e (h+f) p (together q v) := by
  have swap (p q : I → Tree) (hp : Alive r n l p) (hc : Alive r n l q) :
      Rip r n l (together p q) (together q p) :=
    (Rip.split (Rip.alivePair hp hc)).2.twice (Rip.split (Rip.alivePair hp hc)).1
  exact (((a.pack p).afterTask (swap q p d o)).chain
    ((b.pack q).afterTask (swap v q pv d))).preceded (o.twice o)

-- fork conserving given sum, include output bounds separately
variable {W : Type} [Fintype W]
theorem finite (s : Series W) (b : W → ℤ) (_h : ∀ w,0≤b w) (v : I → W→Tree)
    (f : ∀ w,Hopto j r n l e (b w) p (fun i => v i w))
    (pv : Alive r n l p) (a : ∀ w, Alive r n l (fun i => v i w))
    (_hn : ∀ i,1≤n i) :
    Hopto j r n l e (∑ w,b w) p (stackRun (fun _ => s) v) := by
  classical
  have L : ∀ k : List W, k.Nodup →
      Alive r n l (fun i => Task.forest (v i) k) ∧
      Hopto j r n l e (k.toFinset.sum b) p (fun i => Task.forest (v i) k) := by
    intro k hk
    induction k with
    | nil =>
      have u : Rip r n l p (fun i => Task.forest (v i) []) := by
        obtain ⟨k,d⟩ := pv; exact ⟨k,fixture d.out d.budget _⟩
      exact ⟨u.idle,by simpa using (tarry u : Hopto j r n l e 0 _ _)⟩
    | cons t k ih =>
      rw [List.nodup_cons] at hk
      obtain ⟨H,Q⟩ := ih hk.2
      refine ⟨Rip.alivePair (a t) H,?_⟩
      simpa only [Task.forest_cons,together,List.toFinset_cons,Finset.sum_insert (show t ∉ k.toFinset by simpa using hk.1)] using
        (f t).doubleg Q pv (a t) H
  unfold stackRun
  simp_rw [stripe_simple]
  have ha : s.explore.toFinset=Finset.univ := by ext; simp [s.complete]
  simpa [ha] using (L s.explore s.nodup).2
end Hopto
end Loom

end IntegerMultiplication
end Computability
end OAI
