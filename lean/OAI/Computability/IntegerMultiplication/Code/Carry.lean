import OAI.Computability.IntegerMultiplication.Code.Bound

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
variable {X Y Z : Type*}
def Volume (a : X → ℝ) (p : X → Tree) :=
  ∃ D : ℕ, ∀ x, ((p x).count:ℝ) ≤ (D:ℝ)*a x
variable {a d : X → ℝ} {p q r s t : X → Tree}
namespace Volume
theorem along (h : Volume a p) (f : Y → X) : Volume (a ∘ f) (p ∘ f) := by
  obtain ⟨n,u⟩ := h; exact ⟨n,fun _ => u _⟩
theorem fork (h : Volume a p) (e : Volume a q) (ha : ∀x, 1≤a x) :
    Volume a (fun x => Tree.fork (p x) (q x)) := by
  obtain ⟨B,b⟩ := h; obtain ⟨C,c⟩ := e
  refine ⟨B+C+1,fun x => ?_⟩
  simp only [Tree.count, Nat.cast_add, Nat.cast_one]
  linarith [b x,c x,ha x]
theorem left (h : Volume a (fun x => Tree.fork (p x) (q x))) : Volume a p := by
  obtain ⟨B,b⟩ := h
  refine ⟨B,fun x => le_trans ?_ (b x)⟩
  exact_mod_cast (show (p x).count ≤ (p x).count+(q x).count+1 by omega)
theorem right (h : Volume a (fun x => Tree.fork (p x) (q x))) : Volume a q := by
  obtain ⟨B,b⟩ := h
  refine ⟨B,fun x => le_trans ?_ (b x)⟩
  dsimp only [Tree.count]
  exact_mod_cast Nat.le_add_left _ _ |>.trans (Nat.le_succ ..) -- orient
end Volume

/-- Allowance covers the whole packet as well as the update. -/
structure Carries (a : X → ℝ) (p q : X → Tree) : Prop where
  runs : Sized a p q
  small : Volume a p

namespace Carries
theorem budget (h : Carries a p q) : ∀ x,1 ≤ a x := h.runs.1
theorem out (h : Carries a p q) : Volume a q := h.runs.impact h.small
theorem sequence (h : Carries a p q) (e : Sized a q r) : Carries a p r :=
  ⟨h.runs.chain e,h.small⟩
theorem chain (h : Carries a p q) (e : Carries a q r) : Carries a p r :=
  h.sequence e.runs

theorem cheap (ha : ∀x,1≤a x) (h : Volume a p)
    (q : X → Tree) (d : Task (fun x => (p x).count) p q) : Carries a p q :=
  ⟨Sized.size_shield h ha d,h⟩

theorem idles (ha : ∀x,1≤a x) (h : Volume a p) : Carries a p p :=
  cheap ha h _ Task.self

theorem slide (h : Carries a p q) (g : Y→X) : Carries (a ∘ g) (p ∘ g) (q ∘ g) :=
  ⟨h.runs.along _,h.small.along _⟩

theorem larger (h : Carries a p q) (g : ∀x,a x≤d x) : Carries d p q := by
  refine ⟨h.runs.mono g,?_⟩
  obtain ⟨u,hh⟩ := h.small
  exact ⟨u,fun x => (hh x).trans (by gcongr; exact g _)⟩

theorem times (h : Carries a p q) (hd : ∀x,1≤d x) (n : ℕ)
    (g : ∀x,a x≤ (n:ℝ)*d x) : Carries d p q := by
  refine ⟨h.runs.adapts hd n g,?_⟩
  obtain ⟨u,hh⟩ := h.small
  exact ⟨u*n,fun x => (hh x).trans (by push_cast; rw [mul_assoc]; gcongr; exact g _)⟩

-- constructors and projections
theorem first (h : Carries a p q) (e : Volume a r) :
    Carries a (fun x => Tree.fork (p x) (r x)) (fun x => Tree.fork (q x) (r x)) := by
  obtain ⟨i,u,d,K,D⟩ := h.runs
  exact ⟨⟨i,u,d.left _,K,D⟩, h.small.fork e h.budget⟩

theorem swap (ha : ∀ x,1≤a x) (h : Volume a p) (e : Volume a r) :
    Carries a (fun x => Tree.fork (p x) (r x)) (fun x => Tree.fork (r x) (p x)) := by
  apply cheap ha (h.fork e ha)
  exact (Task.exchange p r).mono (by simp [Tree.count])

theorem second (h : Carries a p q) (e : Volume a r) :
    Carries a (fun x => Tree.fork (r x) (p x)) (fun x => Tree.fork (r x) (q x)) :=
  ((swap h.budget e h.small).chain (h.first e)).chain (swap h.budget h.out e)

theorem twice (h : Carries a p q) (g : Carries a p r) :
    Carries a p (fun x => Tree.fork (q x) (r x)) :=
  (cheap h.budget h.small _ (Task.copy p)).chain
    ((h.first h.small).chain (g.second h.out))

theorem dropLeft (ha : ∀ x,1≤a x) (h : Volume a p) (e : Volume a r) :
    Carries a (fun x => Tree.fork (p x) (r x)) r :=
  cheap ha (h.fork e ha) _ ((Task.dropLeft p r).mono (fun x => by simp [Tree.count]; omega))
theorem dropRight (ha : ∀ x,1≤a x) (h : Volume a p) (e : Volume a r) :
    Carries a (fun x => Tree.fork (p x) (r x)) p :=
  cheap ha (h.fork e ha) _ ((Task.dropRight p r).mono (fun x => by simp [Tree.count]))

theorem func [Codec Y] [Codec Z] {y : X → Y} (ha : ∀ x,1≤a x) (h : Volume a (fun x => send (y x)))
    (f : Y→Z) (hf : Easy f) : Carries a (fun x => send (y x)) (fun x => send (f (y x))) :=
  cheap ha h _ (Task.on hf _)

end Carries
end Code

end IntegerMultiplication
end Computability
end OAI
