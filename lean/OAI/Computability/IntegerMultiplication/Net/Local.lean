import OAI.Computability.IntegerMultiplication.Net.NetworkBasic

/-! Cancellation motif at a single stage plane. T are triple indices (vary current
tensor factor), C labels central scratch. Side scratch for all pairs of triples,
though only neighbors will be touched between terminals. -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net
open Finset
namespace Motif
variable (T C : Type)
abbrev Aux := (T×T) ⊕ C
abbrev Local := T ⊕ (T ⊕ (Aux T C))
def repr {T C R : Type} (x y : T → R) (q : T → T → R) (a : C → R) : Local T C → R
| .inl t => x t
| .inr (.inl t) => y t
| .inr (.inr (.inl (t,u))) => q t u
| .inr (.inr (.inr i)) => a i
variable {T C} {R : Type}

-- Only data bank and one scratch class interact at one step
inductive PhysicalBank
| x
| y
deriving DecidableEq

instance : Fintype PhysicalBank where
  elems := {.x, .y}
  complete := by
    intro bank
    cases bank <;> simp

abbrev lx (t : T) : Local T C := Sum.inl t
abbrev ly (t : T) : Local T C := Sum.inr (.inl t)
abbrev side (t u : T) : Local T C := Sum.inr (.inr (.inl (t,u)))
abbrev center (i : C) : Local T C := Sum.inr (.inr (.inr i))
abbrev aux (r : Aux T C) : Local T C := Sum.inr (.inr r)
def role : PhysicalBank → T → Local T C
| .x, t => lx t
| .y, t => ly t

-- routing view of a stage
structure View (T C R : Type) where
  x : T → R
  y : T → R
  scratch : Aux T C → R

namespace View
def val (w : View T C R) : Local T C → R
| .inl t => w.x t
| .inr (.inl t) => w.y t
| .inr (.inr r) => w.scratch r
def load (z : Local T C → R) : View T C R where
  x := fun t => z (lx t)
  y := fun t => z (ly t)
  scratch := fun r => z (aux r)

@[simp] theorem val_load (z : Local T C → R) : (load z).val = z := by
  funext w
  rcases w with _|_|_ <;> rfl
@[simp] theorem load_val (z : View T C R) : load z.val = z := rfl
@[simp] theorem val_scratch (z : View T C R) (a : Aux T C) : z.val (aux a) = z.scratch a := rfl
@[simp] theorem val_x (z : View T C R) (a : T) : z.val (lx a) = z.x a := rfl
@[simp] theorem val_y (z : View T C R) (a : T) : z.val (ly a) = z.y a := rfl
def bank : PhysicalBank → View T C R → T → R
| .x, z => z.x
| .y, z => z.y
@[simp] theorem val_role (p : PhysicalBank) (z : View T C R) (a : T) : z.val (role p a) = bank p z a := by
  cases p <;> rfl

def store (p : PhysicalBank) (w : View T C R) (b : T → R) : View T C R :=
  match p with
  | .x => { w with x := b }
  | .y => { w with y := b }

end View

/-- Q t a describes additive bank/scratch interaction. 'in' means bank←scratch. -/
def quadrant (p : PhysicalBank) (receive : Bool) (Q : T → Aux T C → Amount) :
    Local T C → Local T C → Amount :=
  let on : Local T C → Local T C → Amount := fun r s =>
    match p, r, s with
    | .x, .inl t, .inr (.inr a) => Q t a
    | .y, .inr (.inl t), .inr (.inr a) => Q t a
    | _, _, _ => .none
  if receive then on else (fun w v => on v w)

/-- Gate compatibility lifted from the data/scratch contact set. -/
theorem quadrant_ok {L} (p : PhysicalBank) (receive : Bool) (Q : T → Aux T C → Amount)
    (l : Local T C → L)
    (hc : ∀ t a, Q t a ≠ .none → l (role p t) = l (aux a)) :
    Hop.ok { label := l, coeff := quadrant p receive Q } := by
  rintro (xt|yt|a) (xu|yu|b) hv
  all_goals
    cases p <;> cases receive <;> try contradiction
  -- simplify nongoals
  all_goals first | contradiction | exact hc _ _ hv | exact (hc _ _ hv).symm

variable [Fintype T] [Fintype C] [Ring R]
/-- View interpreter -/
def localCalc (h : R) (p : PhysicalBank) (receive : Bool) (Q : T → Aux T C → Amount)
    (z : View T C R) : View T C R :=
  let b := View.bank p z
  if receive then View.store p z
    (b + fun t => ∑ a, Amount.read h (Q t a) * z.scratch a)
  else { z with scratch := z.scratch + fun a => ∑ t, Amount.read h (Q t a) * b t }

theorem quadrant_view {L : Type} (p : PhysicalBank) (receive : Bool)
    (Q : T → Aux T C → Amount) (l : Local T C → L) (z : View T C R) (h : R) :
    Hop.run ⟨l, quadrant p receive Q⟩ h z.val = (localCalc h p receive Q z).val := by
  funext w
  rcases w with _|_|_
  all_goals
    cases p <;> cases receive <;>
      simp [Hop.run, Fintype.sum_sum_type, quadrant, localCalc, View.bank, View.store, View.val]

end Motif
end Net

end IntegerMultiplication
end Computability
end OAI
