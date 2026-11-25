import OAI.Computability.IntegerMultiplication.Port.Span
import OAI.Computability.IntegerMultiplication.Strip.Order

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Port
open Matrix Finset
noncomputable section
variable (p : ℕ) {J R : Type}

abbrev Duplex (J R : Type) := (J→R) × (J→R)
-- phase of address coordinates
abbrev Wing := Bool -- false = H (first)
abbrev Spot (J : Type) := Wing × J
def hear (x : Duplex J R) (s : Spot J) := if s.1 then x.2 s.2 else x.1 s.2
def place [DecidableEq J] (x : Duplex J R) (s : Spot J) (r : R) : Duplex J R :=
  if s.1 then (x.1,Function.update x.2 s.2 r) else (Function.update x.1 s.2 r,x.2)
@[simp] theorem placed [DecidableEq J] (x : Duplex J R) (s t : Spot J) (r : R) :
    hear (place x s r) t = if t=s then r else hear x t := by
  rcases s with ⟨_ | _, j⟩; all_goals rcases t with ⟨_ | _, i⟩
  all_goals by_cases e : i=j <;> simp [place, hear, e]

theorem hear_all {x y : Duplex J R} (h : ∀ s,hear x s=hear y s) : x=y :=
  Prod.ext (funext fun j => h (false,j)) (funext fun j => h (true,j))

inductive Lag (J : Type) (p : ℕ)
| width (at_ : Spot J) (alpha : Span p)
| gather (at_ ctrl : Spot J) (beta : Pinpoint p)
| pivot (h d : J)
namespace Lag
variable {p} [DecidableEq J]
def early (rank : J→ℕ) (i s : Spot J) : Prop :=
  (i.1 = false ∧ s.1 = true) ∨ (i.1=s.1 ∧ rank i.2 < rank s.2)
def legal (rank : J→ℕ) : Lag J p → Prop
| .width .. | .pivot .. => True
| .gather a k _ => early rank k a
def prices : Lag J p → ℕ
| .pivot .. => 1
| _ => 0

def fire (j : ℕ) (x : Duplex J (Tower p j)) : Lag J p → Duplex J (Tower p j)
| .width at_ a => place x at_ (a.land j * hear x at_)
| .gather at_ k b => place x at_ (hear x at_ + b.stamp j * hear x k)
| .pivot h d =>
  place (place x (false,h) (hear x (true,d))) (true,d) (hear x (false,h))

-- usable semantic inversion (gather only if k earlier)
def rewind : Lag J p → Lag J p
| .width at_ a => .width at_ a.reciprocal
| .gather at_ k b => .gather at_ k b.opposite
| .pivot h d => .pivot h d

theorem loop (j : ℕ) (x : Duplex J (Tower p j)) (r : Lag J p) (rank : J→ℕ) (safe : r.legal rank) :
    fire j (fire j x r) r.rewind = x := by
  apply hear_all; intro k
  cases r with
  | width s a =>
    by_cases e : k=s
    · simp [fire,rewind,placed,e, mul_comm (a.reciprocal.land j)]
      rw [mul_right_comm,Span.land_rec,one_mul]
    simp [fire,rewind,placed,e]
  | gather s t b =>
    have hv : t≠s := by intro e; simp [legal,early,e] at safe
    by_cases e : k=s <;> simp [fire,rewind,e,hv]
  | pivot a b =>
    rcases k with ⟨_|_,i⟩
    all_goals by_cases x : i=a <;> by_cases y:i=b <;> simp_all [fire,rewind]

omit [DecidableEq J] in
theorem rewind_legal (rank : J→ℕ) (v : Lag J p) (h : v.legal rank) : v.rewind.legal rank := by
  cases v <;> exact h

theorem backlist (j : ℕ) (x : Duplex J (Tower p j)) (v : List (Lag J p)) (rank : J→ℕ)
    (h : ∀ r∈v,r.legal rank) :
    (v.reverse.map rewind).foldl (fire j) (v.foldl (fire j) x) = x := by
  induction v generalizing x with
  | nil => rfl
  | cons r v ih =>
    simp only [List.reverse_cons, List.map_append,List.map_cons,List.map_nil,List.foldl_append,
      List.foldl_cons,List.foldl_nil]
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),loop _ _ _ rank (h _ (by simp))]

end Lag
end
end Port

end IntegerMultiplication
end Computability
end OAI
