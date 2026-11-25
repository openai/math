import OAI.Computability.IntegerMultiplication.Strip.Order
import OAI.Computability.IntegerMultiplication.Strip.Lens

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
namespace Dims
abbrev Tape := List ℕ

def Pin : Tape → Type
| [] => Unit
| n::l => Fin n × Pin l

-- wrapper to enter and exit a lens by heading dimension
abbrev node {n l} : Fin n × Pin l → Pin (n::l) := id
abbrev look {n l} : Pin (n::l) → Fin n × Pin l := id
def hinge (n l) : Fin n × Pin l ≃ Pin (n::l) := Equiv.refl _

def layout : (s:Tape) → Series (Pin s)
| [] => Series.one
| a::t => ((Series.natural a).cart (layout t)).via (hinge a t)

def room (s:Tape) := s.prod
@[simp] theorem room_nil : room [] = 1 := rfl
@[simp] theorem room_cons (i : ℕ) (s : Tape) : room (i::s)=i*room s := rfl
@[simp] theorem space (s:Tape) : (layout s).count = room s := by
  induction s with
  | nil => rfl
  | cons a s ih => rw [layout,Series.count_via,Series.count_cart, Series.count_natural, room_cons,ih]

theorem room_cat (s t : Tape) : room (s++t)=room s*room t := by simp [room]

def solid (s : Tape) := ∀ n∈s, 2≤n
@[simp] theorem solid_cat (s t : Tape) : solid (s++t) ↔ solid s ∧ solid t := List.forall_mem_append
@[simp] theorem solid_cons (a : ℕ) (s : Tape) : solid (a::s) ↔ 2≤a ∧ solid s := List.forall_mem_cons
theorem wide (s : Tape) (h : solid s) : 0<room s := by
  induction s with
  | nil => decide
  | cons a s ih => rw [room_cons, solid_cons] at *; exact Nat.mul_pos (by omega) (ih h.2)

instance instDPin : (s : Tape) → DecidableEq (Pin s)
| [] => inferInstanceAs (DecidableEq Unit)
| i::l =>
  haveI : DecidableEq (Pin l) := instDPin l
  inferInstanceAs (DecidableEq (Fin i × Pin l))
instance instFPin : (s : Tape) → Fintype (Pin s)
| [] => inferInstanceAs (Fintype Unit)
| a::l =>
  haveI : Fintype (Pin l) := instFPin l
  inferInstanceAs (Fintype (Fin a × Pin l))
@[simp] theorem population (s : Tape) : Fintype.card (Pin s)=room s := by simpa using space s

-- split/join
def Union (s t : Tape) : Pin s × Pin t ≃ Pin (s++t) :=
  match s with
  | [] => {
    toFun := fun i => i.2
    invFun := fun i => ((),i)
    left_inv := by rintro ⟨_,_⟩; rfl
    right_inv := fun _ => rfl }
  | a::s =>
    -- app cons reduces
    ((Equiv.prodAssoc (Fin a) _ _).trans
      ((Equiv.refl (Fin a)).prodCongr (Union s t))).trans (hinge a (s++t))
@[simp] theorem app_cons {a} {s t : Tape} (b : Fin a) (p : Pin s) (q : Pin t) :
    Union (a::s) t (node (b,p),q)=node (b,Union s t (p,q)) := rfl

variable {X : Type}
theorem tab_cons {a s} (f : Pin (a::s) → X) :
    (layout (a::s)).tab f = ((Series.natural a).tab
      (fun b : Fin a => (layout s).tab (fun i => f (node (b,i))))).flatten := by
  rw [layout,Series.tab_via,Series.grouped]
  rfl

theorem tab_cat (s t : Tape) (f : Pin (s++t) → X) :
    (layout (s++t)).tab f = ((layout s).cart (layout t)).tab (f ∘ Union s t) := by
  rw [Series.grouped]
  induction s with
  | nil =>
    change (layout t).tab f = ((layout t).tab (fun b => _) ++ [].flatten)
    simp only [List.flatten_nil,List.append_nil]
    rfl
  | cons a s ih =>
    change (layout (a::(s++t))).tab f = _
    rw [tab_cons,tab_cons]
    -- RHS List.flatten of List (List (List X)) flattened. induction over Fin walk easier.
    unfold Series.tab
    induction (Series.natural a).explore with
    | nil => rfl
    | cons c l jh =>
      simp only [List.map_cons,List.flatten_cons,List.flatten_append]
      rw [jh]
      congr 1
      exact ih _ -- defeq Union invokes app_cons
end Dims
end Strip

end IntegerMultiplication
end Computability
end OAI
