import Mathlib.Algebra.Order.Ring.Nat
import OAI.Computability.IntegerMultiplication.Code.List
import OAI.Computability.IntegerMultiplication.Code.Repeat

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code.Task
variable {X : Type*}

/-- Call again on each child (de Bruijn index 1 because of map recursion).
Input and output trees for the child need not share a Codec; their encodings
are the query and reply of the task. -/
private def listBody : Cmd :=
  splitRoot 0 (give 0)
    (.join (.again 1)
      (.join (move 0 1 2)
        (.join (.again 0)
          (.join (move 1 0 2) (pack 0)))))

private def node (start end_ : Cmd) : Cmd :=
  start.join (splitRoot 0 (fun _ => .pass) <|
    (.join (.tie listBody) (.join (pack 0) end_)))

-- exact-ish cost for child ingestion on nodes. Separate D (cost factor) to keep
-- the recursive contribution normalized.
private theorem fits_row {a : X → ℕ} {p q : X → Tree}
    {b E} (l : List X) (r : Deck) (D : ℕ)
    (h : ∀ i ∈ l, Fits.value (b::E) b 0 (p i) (q i) (D*a i)) :
    Fits (listBody::b::E) listBody (pile 0 (forest p l) r) (pile 0 (forest q l) r)
      (D*costSum a l+100*(forest q l).count) := by
  induction l generalizing r with
  | nil => exact (fits_bit (b:=false) (c:=give 0) (fits_give false ..)).mono (by simp [Tree.count])
  | cons x l ih =>
    have hx := Fits.again (i:=1) (env := listBody::b::E) (b:=b) (by simp) rfl
      (h x List.mem_cons_self (pile 0 (forest p l) r))
    let G := listBody :: b :: E
    have h₁ := fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide)
      (q x) G (pile 0 (forest p l) r)
    have hl := Fits.again0 (ih (pile 1 (q x) r)
      (fun i e => h i (List.mem_cons_of_mem _ e)))
    rw [pile_comm 1 _ _ 0 _ (by decide)] at h₁
    rw [pile_comm 0 (forest q l) r 1 (q x) (by decide)] at hl
    have h₂ := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide)
      (q x) G (pile 0 (forest q l) r)
    refine (fits_pair (hx.join (h₁.join (hl.join (h₂.join (fits_pack _ _ r 0 G)))))).mono ?_
    simp only [costSum_cons,forest_cons,Tree.count,Nat.mul_add]
    omega

/-- Nonadaptive divide-and-conquer; a side tree may be stored with the children at
each node. `gen` generates child queries and side tree (even at a base case this might
compute and serialize scalar output into the side tree). `recov` uses all child replies
and the untouched side tree. Need budget at each node for these procedures and also
traversing the replies once, and a strictly fuel-decreasing recurrence. -/
theorem children {p q : X → Tree} {a g h : X → ℕ}
    (l : X → List X) (side : X → Tree)
    (gen : Task g p (fun i => .fork (forest p (l i)) (side i)))
    (recov : Task h (fun i => .fork (forest q (l i)) (side i)) q)
    (budget : ∀ x, g x+h x+1+(forest q (l x)).count+costSum a (l x) ≤ a x) :
    Task a p q := by
  obtain ⟨c,C,hc⟩ := gen
  obtain ⟨d,F,hd⟩ := recov
  let D := C+F+120
  let b := node c d
  refine ⟨.tie b,D, fun x E r => ?_⟩
  have he (n) : ∀ i, a i=n → Fits.value (b::E) b 0 (p i) (q i) (D*n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i e r
      subst n
      specialize budget i
      let G := b::E
      have hi (j) (h : j∈l i) : Fits.value G b 0 (p j) (q j) (D*a j) := by
        apply ih (a j) _ j rfl
        have hh : a j ≤ costSum a (l i) := List.single_le_sum (l := List.map a (l i)) (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem h)
        have hu := Tree.count_pos (forest q (l i))
        omega
      have hl := fits_row (l i) (pile 0 (side i) r) D hi
      refine ((hc i G r).join (fits_pair (hl.tie.join ((fits_pack _ _ _ _ _).join (hd i G r))))).mono ?_
      have hz := Nat.mul_le_mul_left D budget
      simp only [D,Nat.mul_add,Nat.add_mul,Nat.mul_one] at *
      omega
  exact ((he _ x rfl r).tie).mono (by simp only [D,Nat.mul_add,Nat.mul_one]; omega)

end Code.Task

end IntegerMultiplication
end Computability
end OAI
