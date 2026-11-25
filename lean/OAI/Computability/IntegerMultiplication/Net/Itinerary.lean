import OAI.Computability.IntegerMultiplication.Net.Parallel

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Circuit
variable {W L A : Type}

def trail (c : Circuit W L) (w : W) := c.ops.map (fun e => e.label w)
def toll [AddMonoid A] (b : L → L → A) : L → List L → A
| _, [] => 0
| i, e::t => b i e + toll b e t

theorem via (c : Circuit W L) [AddMonoid A] (B : L → L → A) (w : W) :
    cost c (fun _ => B) w = toll B (c.init w) (c.trail w) := by
  unfold cost trail
  induction c.ops generalizing c with -- generalizing c nonsense
  | nil => rfl
  | cons e es ih =>
    simp only [costOf, List.map_cons, toll]
    congr 1
    exact ih ⟨e.label,es⟩

/-- property of every edge -/
def smooth (c : Circuit W L) (r : L → L → Prop) :=
  ∀ w, (c.init w :: c.trail w).IsChain r

def con (c d : Circuit W L) : Circuit W L := ⟨c.init,c.ops++d.ops⟩
theorem con_sink (c d : Circuit W L) (h : c.sink=d.init) : (c.con d).sink = d.sink := by
  simp [con, sink, sinkOf, List.foldl_append, ← h]
theorem con_ok (c d : Circuit W L) (hc : c.ok) (hd : d.ok) : (c.con d).ok := by
  intro a ha
  exact (List.mem_append.mp ha).elim (hc a) (hd a)
theorem con_logical {R : Type} [Fintype W] [Ring R] (h : R)
    (c d : Circuit W L) (x : W → R) :
    (c.con d).logical h x = d.logical h (c.logical h x) := by
  simp [logical, con, List.foldl_append]
theorem con_cost {I : Type} [AddMonoid I] (B : L → L → I)
    (c d : Circuit W L) (h : c.sink=d.init) (w : W) :
    (c.con d).cost (fun _ => B) w = c.cost (fun _ => B) w +
      d.cost (fun _ => B) w := by
  simpa only [cost, ← h, con, sink] using
    cost_append (fun (_:W) => B) c.init c.ops d.ops w

theorem con_smooth (c d : Circuit W L) (h : c.sink=d.init)
    (r) (hc : c.smooth r) (hd : d.smooth r) : (c.con d).smooth r := by
  intro w
  specialize hd w
  unfold smooth at hc -- fine?
  rw [← h] at hd -- doesn't rewrite inside smooth
  let g : ∀ (i : W → L) (u : List (Hop W L)),
    (i w :: u.map (fun e => e.label w)).IsChain r →
    (sinkOf i u w :: d.trail w).IsChain r →
    (i w :: (u++d.ops).map (fun e => e.label w)).IsChain r := by
    intro i u
    induction u generalizing i with
    | nil => exact fun _ hz => hz
    | cons a t ih =>
      simp only [List.map_cons, List.cons_append, List.isChain_cons_cons, sinkOf, List.foldl_cons]
      exact fun hc hd => ⟨hc.1, ih a.label hc.2 hd⟩
  apply g
  · exact hc w
  exact hd

open Parallel
variable {P G B : Type} [DecidableEq P]
theorem weave_trail_l (j : Job P W G L) (i : B ≃ Row P W G) (b : B) (p w)
    (h : i b = .inl (p,w)) :
    trail (j.weave i) b = trail (j.child p) w := by
  simp [trail, Job.weave, shift, Parallel.hop, Function.comp_def, h, Job.child]
theorem weave_trail_r (j : Job P W G L) (i : B ≃ Row P W G) (b : B) (g)
    (h : i b = .inr g) :
    trail (j.weave i) b =
      j.prog.map (fun _ => j.idle g) := by
  simp [trail, Job.weave, shift, Parallel.hop, Function.comp_def, h]
theorem weave_smooth (j : Job P W G L) (i : B ≃ Row P W G) (r : L → L → Prop)
    (hc : ∀ p, (j.child p).smooth r) (ref : ∀ l, r l l) :
    (j.weave i).smooth r := by
  intro b
  cases hb : i b with
  | inl t =>
    rcases t with ⟨p,w⟩
    rw [weave_trail_l j i b p w hb]
    simp only [Job.weave, Function.comp_apply, hb, join_l]
    exact hc p w
  | inr g =>
    rw [weave_trail_r j i b g hb]
    simp only [Job.weave, Function.comp_apply, hb, join_r]
    induction j.prog with
    | nil => simp
    | cons t u ih => exact List.IsChain.cons_cons (ref _) ih

end Net.Circuit

end IntegerMultiplication
end Computability
end OAI
