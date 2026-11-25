import OAI.Computability.IntegerMultiplication.Adic.Mirror

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open IntegerMultiplication.Port Strip Strip.Dims Code
variable {p j : ℕ} [NeZero p]
noncomputable section
def no (x : Raw p) := add 0 0 0 (by decide) (x,x)
def ace (x : Raw p) := add 1 0 1 (by decide) (no x,x)
@[fun_prop] theorem easy_no {X : Type*} [Codec X] {k : X→Raw p} (h : Easy k) :
    Easy (fun i => no (k i)) := by unfold no; fun_prop
@[fun_prop] theorem easy_ace {X : Type*} [Codec X] {k : X→Raw p} (h : Easy k) :
    Easy (fun i => ace (k i)) := by unfold ace; fun_prop
theorem hold_no (x : Block p j) : Holds j (no (least x)) 0 := by
  simpa [no] using sum 0 0 0 (by decide) (Holds.std x) (Holds.std x)
theorem hold_ace (x : Block p j) : Holds j (ace (least x)) 1 := by
  simpa [ace] using sum 1 0 1 (by decide) (hold_no x) (Holds.std x)
variable {I : Type} {w : I→ℝ} {q : I→Tree}
-- easier seeds directly stripe (fun x => (f x, digit)).
theorem keyed (j : I→ℕ) (t : (i:I)→Tower p (j i)) (o : (i:I)→Block p (j i)→Raw p)
    (h : ∀ i x,Holds (j i) (o i x) (t i)) (v : (i:I)→Block p (j i)→Tree)
    (a b : Nug p)
    (l : Carries w q (stackRun (fun i => layout (field p (j i))) v))
    (g : Carries w q (stackRun (fun i => layout (field p (j i)))
      fun i x => send (o i x,least x))) :
    Carries w q (stackRun (fun i => layout (field p (j i))) fun i x => v i ((swift a b (t i)).symm x)) := by
  apply river a b j t (fun i => least ((index p (j i)).symm (t i))) (fun _ => Holds.stdRev _) v l
  have z i x := (h i x).single (Holds.stdRev _)
  simpa only [byword,z] using g

theorem keyed_const (j : I→ℕ) (t : (i:I)→Tower p (j i)) (seed : Raw p→Raw p)
    (hs : Easy seed) (h : ∀ i (x : Block p (j i)),Holds (j i) (seed (least x)) (t i))
    (v : (i:I)→Block p (j i)→Tree) (a b : Nug p)
    (l : Carries w q (stackRun (fun i => layout (field p (j i))) v))
    (g : Carries w q (stackRun (fun i => layout (field p (j i))) fun _ x => send (least x))) :
    Carries w q (stackRun (fun i => layout (field p (j i))) fun i x => v i ((swift a b (t i)).symm x)) := by
  apply keyed j t (fun _ x => seed (least x)) h v a b l
  unfold stackRun at g ⊢
  simp_rw [stripe_eq'] at g ⊢
  have hx := g.chain (Carries.func g.budget g.out (List.map (fun (x:Raw p) => (seed x,x)))
    ((hs.pair easy_id).mapping))
  simpa only [Series.map_tab,Function.comp_def] using hx

-- signed coefficient only, move entries at x to α*x
def sweep (a : Span p) (j : ℕ) : Block p j ≃ Block p j :=
  let g := swift a.top a.down (0:Tower p j)
  if a.neg then (g.trans mirror).trans
    (swift Nug.one Nug.one (1:Tower p j))
  else g
@[simp] theorem inj (a : Span p) (j : ℕ) (x : Block p j) :
    index p j (sweep a j x) = a.land j * index p j x := by
  unfold sweep
  dsimp only
  cases h : a.neg <;>
    simp only [h,ite_true,Bool.false_eq_true,ite_false,Equiv.trans_apply,arrive,reflects,slide,
      Span.land,Span.fold,Span.polarity,Nug.own_one]
  · simp
  simp
  ring

theorem signs (j : I→ℕ) (v : (i:I)→Block p (j i)→Tree)
    (a : Span p)
    (l : Carries w q (stackRun (fun i => layout (field p (j i))) v))
    (g : Carries w q (stackRun (fun i => layout (field p (j i))) fun _ x => send (least x))) :
    Carries w q (stackRun (fun i => layout (field p (j i))) fun i x => v i ((sweep a (j i)).symm x)) := by
  let Z := fun (i:I) => (0:Tower p (j i))
  have u := keyed_const j Z no (by unfold no; fun_prop) (fun _ x => hold_no x) _ a.top a.down l g
  cases h : a.neg
  · simpa only [sweep,h,Bool.false_eq_true,ite_false] using u
  have t := toss j _ u
  let E := fun (i:I) => (1:Tower p (j i))
  have k := keyed_const j E ace (by unfold ace; fun_prop) (fun _ x => hold_ace x) _ Nug.one Nug.one t g
  simpa only [sweep,h,ite_true,Equiv.symm_trans_apply, restored] using k
end
end Adic

end IntegerMultiplication
end Computability
end OAI
