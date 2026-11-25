import OAI.Computability.IntegerMultiplication.Strip.Order
import OAI.Computability.IntegerMultiplication.Code.Train
import OAI.Computability.IntegerMultiplication.Code.Dup

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Finset IntegerMultiplication.Code IntegerMultiplication.Code.Task
variable {A B C X I : Type}
def stripe (s : Series A) (t : A→Tree) := forest id (s.tab t)
@[simp] theorem stripe_eq (s : Series A) (v : A→Tree) :
    stripe s v = send (s.tab v) := (forest_send _)

theorem stripe_eq' (s : Series A) [Codec B] (v : A→B) :
    stripe s (fun i => send (v i)) = send (s.tab v) := by
  rw [stripe_eq, ← forest_send, ← forest_send,
    show s.tab (fun i => send (v i)) = List.map send (s.tab v) from (s.map_tab ..).symm,
    forest_map]
  rfl

theorem stripe_simple (s : Series A) (v : A→Tree) :
    stripe s v = forest v s.explore := by simp [stripe,Series.tab]

theorem cart_eq (s : Series A) (t : Series B) (v : A×B→Tree) :
    stripe (s.cart t) v =
      send ((s.tab (fun a => t.tab (fun b => v (a,b)))).flatten) := by rw [stripe_eq,Series.grouped]

theorem many (l : List (List X)) (L n : ℕ) (h : l.length=L)
    (hb : ∀ x∈l,x.length=n) :
    (l.map (tally ∘ List.length))=List.replicate L (tally n) := by
  subst L
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨x,y⟩ := List.forall_mem_cons.mp hb
    rw [List.map_cons, List.length_cons, List.replicate_succ,ih y, Function.comp_apply,x]

-- physical grouping via two Tally counts (can have affine included cost)
abbrev Hut := List Tree
def brick (x : List Tally × Hut) :=
  (Piecework.segment x.1 x.2).1
@[fun_prop]
theorem brick_task {X : Type*} [Codec X] {f : X→List Tally × Hut} (h : Easy f) :
    Easy (fun i => brick (f i)) := by unfold brick; fun_prop

-- Real query family:
theorem rows {P B : I→Type} (s : (i:I)→Series (P i)) (t : (i:I)→Series (B i))
    (v : (i:I)→P i × B i→Tree) {w : I→ℝ} {input : I→Tree}
    (h : Carries w input (fun i => Tree.fork
        (send (List.replicate ((s i).count) (tally (t i).count)))
        (stripe ((s i).cart (t i)) (v i)))) :
    Carries w input (fun i => stripe (s i)
      (fun p => stripe (t i) fun b => v i (p,b))) := by
  have e := Carries.func (Y:=List Tally × Hut) h.budget
    (y:=fun i => (List.replicate (s i).count (tally (t i).count), ((s i).cart (t i)).tab (v i)))
    (by simpa [send_prod, cart_eq,Series.grouped] using h.out) brick (by unfold brick; fun_prop)
  suffices g : (fun i => send (brick (List.replicate (s i).count (tally (t i).count),
      ((s i).cart (t i)).tab (v i)))) =
    fun i => stripe (s i) fun p => stripe (t i) fun b => v i (p,b) by
    rw [g] at e
    apply h.chain
    simpa [stripe_eq] using e
  funext i
  rw [Series.grouped,brick]
  let l := (s i).tab fun p => (t i).tab fun b => v i (p,b)
  have hh := many l (s i).count (t i).count (Series.card ..) (by
    intro x h; rcases ((s i).elements _ _).mp h with ⟨p,rfl⟩
    exact Series.card ..)
  change send (Piecework.segment _ l.flatten).1 = _
  rw [← hh,Piecework.prescribed]
  exact (by
    simp_rw [stripe_eq]
    rw [← forest_send, ← forest_send]
    change forest send l = forest id (List.map _ _)
    rw [forest_map]
    dsimp only [id]
    -- l.map of send nested
    simp only [l, Series.tab, forest_map])

theorem flatten {P B : I→Type} (s : (i:I)→Series (P i)) (t : (i:I)→Series (B i))
    (v : (i:I)→P i × B i→Tree) {w : I→ℝ} {input : I→Tree}
    (h : Carries w input (fun i => stripe (s i)
      (fun p => stripe (t i) fun b => v i (p,b)))) :
    Carries w input (fun i => stripe ((s i).cart (t i)) (v i)) := by
  let l := fun i => (s i).tab (fun p => (t i).tab fun b => v i (p,b))
  have eq : (fun i => stripe (s i) fun p => stripe (t i) fun b => v i (p,b)) =
      fun i => send (l i) := by
    funext i
    simp_rw [stripe_eq]
    simp only [l, Series.tab,← forest_send,forest_map]
    rfl
  rw [eq] at h
  simpa only [cart_eq,l] using h.chain (Carries.func h.budget h.out List.flatten Easy.flatten)
end Strip

end IntegerMultiplication
end Computability
end OAI
