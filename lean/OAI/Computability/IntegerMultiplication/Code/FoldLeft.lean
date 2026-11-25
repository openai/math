import OAI.Computability.IntegerMultiplication.Code.Fold
import Mathlib.Data.List.Infix

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code.Task
variable {X Y Z W : Type*}

/-- Left-to-right fold; for the outer wrapper start with a pair (forest, seed), expose
and move the forest once to stack 1. Then consume from 1, folding into top of stack 0
(seed). -/
def sweepBody (cmd : Cmd) : Cmd :=
  splitRoot 1 (fun _ => .pass)
    ((move 1 0 2).join ((pack 0).join (cmd.join (.again 0))))

theorem sweep {p : Y → X → Tree} {w : List X → Y → Tree}
    {a : X → List X → Y → ℕ} {D : List X → Y → Prop}
    (hclosure : ∀ x l y, D (x::l) y → D l y)
    (h : Task (fun i : {s : X × List X × Y // D (s.1::s.2.1) s.2.2} => a i.val.1 i.val.2.1 i.val.2.2)
      (fun i => .fork (p i.val.2.2 i.val.1) (w (i.val.1::i.val.2.1) i.val.2.2))
      (fun i => w i.val.2.1 i.val.2.2)) :
    Task (fun i : {s : List X × Y // D s.1 s.2} =>
      foldCost (fun x l => a x l i.val.2+(p i.val.2 x).count) i.val.1)
      (fun i => .fork (forest (p i.val.2) i.val.1) (w i.val.1 i.val.2))
      (fun i => w [] i.val.2) := by
  obtain ⟨c,C,h⟩ := h
  let m := sweepBody c
  refine ⟨splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (.tie m)),100+C,fun ⟨⟨s,y⟩,hs⟩ E r => ?_⟩
  let g := fun x l => a x l y+(p y x).count
  let Γ := m::E
  have hm : ∀ l, D l y →
    Fits Γ m (pile 1 (forest (p y) l) (pile 0 (w l y) r)) (pile 0 (w [] y) r)
      ((58+C)*foldCost g l) := by
    intro l e
    induction l with
    | nil => exact (fits_bit (b := false) (c := fun _ => Prog.pass) (Fits.pass _)).mono (by simp [foldCost]; omega)
    | cons x l ih =>
      have h₁ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide)
        (p y x) Γ (pile 1 (forest (p y) l) (pile 0 (w (x::l) y) r))
      rw [pile_comm 1 (forest (p y) l) r 0 _ (by decide)] at h₁
      have h₂ := h ⟨(x,l,y),e⟩ Γ (pile 1 (forest (p y) l) r)
      have h₃ := Fits.again0 (ih (hclosure _ _ _ e))
      rw [pile_comm 1 _ r 0 _ (by decide)] at h₃
      -- h₁ input also changed to stack0 outer below x at stack1; reorder back
      have ht := h₁.join ((fits_pack _ _ _ _ _).join (h₂.join h₃))
      rw [← pile_comm 1 _ r 0 (w (x::l) y) (by decide)] at ht
      refine (fits_pair ht).mono ?_
      dsimp only [foldCost,g]
      simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
      omega
  change Fits _ _ (pile 0 (.fork _ _) _) _ ((100+C)*(foldCost g s+1))
  refine (fits_pair ((fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) _ E _).join
    ((hm s hs).tie))).mono ?_
  suffices hh : (forest (p y) s).count ≤ foldCost g s by
    rw [Nat.add_mul 100, Nat.add_mul 58]
    have h : C * foldCost g s ≤ C*(foldCost g s+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hz : ∀ l : List X, (forest (p y) l).count ≤ foldCost g l := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [forest_cons,Tree.count,foldCost,g]
      dsimp only [g] at ih
      omega
  exact hz s

-- Corollary with arbitrary folds. Charge moving each input just once.
theorem foldLeft (p : Y → X → Tree) (u : Y → Z → Tree)
    (next : Y → Z → X → Z) (a : Y → X → ℕ) {D : Y → X → Prop}
    (h : Task (fun i : {s : X × Z × Y // D s.2.2 s.1} => a i.val.2.2 i.val.1)
      (fun i => .fork (p i.val.2.2 i.val.1) (u i.val.2.2 i.val.2.1))
      (fun i => u i.val.2.2 (next i.val.2.2 i.val.2.1 i.val.1))) :
    Task (fun x : {s : List X × Z × Y // ∀ v∈s.1, D s.2.2 v} =>
      costSum (a x.val.2.2) x.val.1+(forest (p x.val.2.2) x.val.1).count)
      (fun i => .fork (forest (p i.val.2.2) i.val.1)
        (u i.val.2.2 i.val.2.1))
      (fun i => u i.val.2.2 (i.val.1.foldl (next i.val.2.2) i.val.2.1)) := by
  -- ghost Y' contains original list and seed.
  let Y' := {s : List X × Z × Y // ∀ v∈s.1, D s.2.2 v}
  let z (s : List X) (i : Y') :=
    (i.val.1.take (i.val.1.length - s.length)).foldl (next i.val.2.2) i.val.2.1
  let w (s) (i : Y') := u i.val.2.2 (z s i)
  let f (i : Y') := p i.val.2.2
  let D' (s) (i : Y') := s <:+ i.val.1
  have hm := sweep (p := f) (w := w) (a := fun x _ y => a y.val.2.2 x) (D := D')
    (fun x l y ⟨q,hq⟩ => ⟨q++[x], by simpa using hq⟩)
    (show Task _ _ _ from ?_)
  refine (hm.on (fun i : Y' => ⟨(i.val.1,i), List.suffix_rfl⟩)).conform
    (fun i => Task.foldCost_add (f i) (a i.val.2.2) _)
    (fun i => by simp [w,z,f]) (fun i => by simp [w,z])
  -- prove the step
  let iso : {s : X × List X × Y' // D' (s.1::s.2.1) s.2.2} → {s : X × Z × Y // D s.2.2 s.1} :=
    fun i => ⟨(i.val.1,z (i.val.1::i.val.2.1) i.val.2.2,i.val.2.2.val.2.2),
      i.val.2.2.property _ (i.property.subset List.mem_cons_self)⟩
  refine (h.on iso).conform (by simp [iso]) (by simp [w,iso,f]) ?_
  intro ⟨⟨x,l,i⟩,hee⟩
  change u _ (next _ (z (x::l) i) x) = u _ (z l i)
  congr 1
  obtain ⟨head,hq⟩ := hee
  dsimp at hq
  simp only [z, ← hq, List.length_append, List.length_cons, Nat.add_sub_cancel]
  rw [show head.length+(l.length+1)-l.length=head.length+1 by omega]
  have hh : (head ++ x::l).take (head.length+1) = head ++ [x] := by
    rw [List.take_append]
    simp
  simp [iso, hh, List.foldl_append]

end Code.Task

end IntegerMultiplication
end Computability
end OAI
