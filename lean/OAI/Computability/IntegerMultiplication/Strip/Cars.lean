import OAI.Computability.IntegerMultiplication.Strip.Encode

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I : Type}
theorem stripe_size {A} (s : Series A) (x : A→Tree) (c : ℕ) (h : ∀ a,(x a).count≤c) :
    (stripe s x).count ≤ (s.count)*(c+1)+1 := by
  rw [stripe_simple,Series.count,Nat.mul_comm]
  exact lenConst h _

theorem stripe_volume {A : I→Type} (s : (i : I)→Series (A i)) (v : (i : I)→A i→Tree)
    (w : I→ℝ) (h : Volume (fun i : Sigma A => w i.1) (fun i => v i.1 i.2))
    (hw : ∀ i, 1 ≤ w i) :
    Volume (fun x => ((s x).count:ℝ)*w x+1) (fun x => stripe (s x) (v x)) := by
  have e := h.car (fun g => hw g.1)
  let g (x : I) := (s x).explore.map (Sigma.mk x)
  have f := e.along g
  simpa only [Function.comp_def,g,cars_map,cars_fixed,Series.count,stripe_simple,forest_map] using f

def stackRun {A : I→Type} (s : (i : I)→Series (A i)) (x : (i : I)→A i→Tree) :=
  fun i => stripe (s i) (x i)

theorem demo {A : I→Type} (s : (i : I)→Series (A i)) (v u : (i : I)→A i→Tree)
    (w : (i : I)→A i→ℝ)
    (h : Carries (fun i : Sigma A => w i.1 i.2) (fun i => v i.1 i.2) (fun i => u i.1 i.2)) :
    Carries (fun i => cars (w i) (s i).explore) (stackRun s v) (stackRun s u) := by
  unfold stackRun
  simpa only [Function.comp_def,stackRun,stripe_simple] using
    (Carries.nested (a:=w) (p:=v) (q:=u) h).slide (fun i : I => Sigma.mk i (s i).explore)

theorem liftoff {A : I→Type} (s : (i : I)→Series (A i)) (v u : (i : I)→A i→Tree)
    (w : I→ℝ)
    (h : Carries (fun i : Sigma A => w i.1) (fun i => v i.1 i.2) (fun i => u i.1 i.2)) :
    Carries (fun i => ((s i).count:ℝ)*w i+1) (stackRun s v) (stackRun s u) := by
  simpa only [cars_fixed,Series.count] using demo s v u (fun i _ => w i) h

abbrev together {A : Type*} (f g : A → Tree) := fun a => Tree.fork (f a) (g a)

theorem zipper {A : I→Type} (s : (i:I)→Series (A i)) (v u : (i:I)→A i→Tree)
    {input : I→Tree} {w : I→ℝ}
    (p : Carries w input (together (stackRun s v) (stackRun s u))) :
    Carries w input (stackRun s fun i => together (v i) (u i)) := by
  apply p.chain
  apply Carries.cheap p.budget p.out
  let f : Sigma A → Tree := fun x => v x.1 x.2
  let g : Sigma A → Tree := fun x => u x.1 x.2
  have z := (zipTrees f g).on (fun x : I => (s x).explore.map (Sigma.mk x))
  simp only [forest_map,f,g] at z
  unfold together stackRun
  simp_rw [stripe_simple]
  exact z.mono fun x => by change (forest (v x) _).count+(forest (u x) _).count ≤ (forest (v x) _).count+(forest (u x) _).count+1; omega

theorem unpair {A : I→Type} (s : (i:I)→Series (A i)) (v u : (i:I)→A i→Tree)
    {input : I→Tree} {w : I→ℝ}
    (p : Carries w input (stackRun s fun i => together (v i) (u i))) :
    Carries w input (together (stackRun s v) (stackRun s u)) := by
  apply p.chain
  apply Carries.cheap p.budget p.out
  let f : Sigma A → Tree := fun x => v x.1 x.2
  let g : Sigma A → Tree := fun x => u x.1 x.2
  unfold together stackRun
  simpa only [stackRun,stripe_simple,together,forest_map,f,g] using
    (unzipTrees f g).on (fun x : I => (s x).explore.map (Sigma.mk x))

theorem coalesce {A : I→Type} (s : (i:I)→Series (A i)) (v u : (i:I)→A i→Tree)
    {input : I→Tree} {w : I→ℝ}
    (p : Carries w input (stackRun s v)) (q : Carries w input (stackRun s u)) :
    Carries w input (stackRun s fun i => together (v i) (u i)) :=
  zipper _ _ _ (p.twice q)

-- arbitrary per-record procedure & communicate descriptor copies first
-- count header argument often built via unary small
theorem spread {A : I→Type} (s : (i:I)→Series (A i)) (l : I→Tree)
    {input : I→Tree} {w : I→ℝ}
    (p : Carries w input (fun i => Tree.fork (send (tally (s i).count)) (l i)))
    (h : ∃ K : ℕ, ∀ i, ((s i).count+1: ℝ)*(l i).count ≤ (K:ℝ)*w i) :
    Carries w input (stackRun s fun i _ => l i) := by
  apply p.sequence
  obtain ⟨K,u⟩ := h
  have e := (IntegerMultiplication.Code.generate (X:=Tree)).on (fun i : I => (tally (s i).count,l i))
  let t := fun i => ((s i).count+1)*(l i).count
  refine ⟨p.budget,t, ?_, K+1,fun i => ?_⟩
  · have eq (i : I) : List.replicate (s i).count (l i)=(s i).tab (fun _ => l i) := by
      unfold Series.tab Series.count; simp -- map_const
    apply e.conform
    · simp [size,t,tally_length, show send (X:=Tree)=id from rfl]
    · simp [show send (X:=Tree)=id from rfl]
    simp [tally_length,stackRun,stripe_eq,eq]
  dsimp only [t]; push_cast; specialize u i; have := p.budget i; linarith
end Strip

end IntegerMultiplication
end Computability
end OAI
