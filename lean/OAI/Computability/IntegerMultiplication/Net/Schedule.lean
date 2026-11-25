import OAI.Computability.IntegerMultiplication.Net.Local

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
open Finset
-- local operation script (labels supplied separately)
structure Touch (T C : Type) where
  which : PhysicalBank
  receive : Bool
  weight : T → Aux T C → Amount

namespace Touch
variable {T C R : Type}
def hop {L} (e : Touch T C) (l : Local T C → L) : Hop (Local T C) L :=
  ⟨l, quadrant e.which e.receive e.weight⟩

theorem ok {L} (e : Touch T C) (l : Local T C → L)
    (h : ∀ t a, e.weight t a ≠ .none → l (role e.which t) = l (aux a)) : (e.hop l).ok :=
  quadrant_ok _ _ _ _ h

def invert (q : T → Aux T C → Amount) (b : Bool) : T → Aux T C → Amount :=
  fun t a => if b then (q t a).flip else q t a

@[simp] theorem invert_false (q : T → Aux T C → Amount) : invert q false = q := rfl
@[simp] theorem invert_none (q : T → Aux T C → Amount) (b t a) :
    invert q b t a = .none ↔ q t a = .none := by cases b <;> simp [invert]

variable [Fintype T] [Fintype C] [Ring R]
def readSrc (h : R) (q : T → Aux T C → Amount) (b : T → R)
    (a : Aux T C) : R := ∑ t, Amount.read h (q t a) * b t
def readAux (h : R) (q : T → Aux T C → Amount) (x : Aux T C → R)
    (t : T) : R := ∑ a, Amount.read h (q t a) * x a

def step (e : Touch T C) (h : R) : View T C R → View T C R := localCalc h e.which e.receive e.weight

theorem run_hop {L : Type} (e : Touch T C) (l : Local T C → L) (z : View T C R) (h : R) :
    (e.hop l).run h z.val = (e.step h z).val := quadrant_view .. -- hmm

theorem readAux_add (h : R) (q : T → Aux T C → Amount) (x y : Aux T C → R) :
    readAux h q (x+y)= readAux h q x + readAux h q y := by
  funext t
  simp [readAux, mul_add, Finset.sum_add_distrib]

@[simp] theorem readAux_neg (h : R) (q : T → Aux T C → Amount) (x : Aux T C → R) :
    readAux h (invert q true) x= -readAux h q x := by
  funext t
  simp [readAux, Finset.sum_neg_distrib, invert]

theorem readAux_negative (h : R) (q : T → Aux T C → Amount) (x : Aux T C → R) :
    readAux h q (-x)= -readAux h q x := by
  funext t
  simp [readAux, Finset.sum_neg_distrib]

omit [Fintype C] in
@[simp] theorem readSrc_neg (h : R) (q : T → Aux T C → Amount) (x : T → R) :
    readSrc h (invert q true) x= -readSrc h q x := by
  funext t
  simp [readSrc, Finset.sum_neg_distrib, invert]

theorem step_io (p : PhysicalBank) (b : Bool) (q : T → Aux T C → Amount) (z : View T C R) (h : R) :
    step ⟨p,b,q⟩ h z =
    if b then View.store p z (View.bank p z + readAux h q z.scratch)
    else { z with scratch := z.scratch + readSrc h q (View.bank p z) } := rfl

end Touch

/-- weights for one source/target pair of banks -/
structure Pairing (T C : Type) where
  copy : T → Aux T C → Amount
  gather : T → Aux T C → Amount
  inj : T → Aux T C → Amount
  scatter : T → Aux T C → Amount

namespace Pairing
variable {T C : Type}
open PhysicalBank (x y)
open Touch

-- rows in actual time order
def fwd (q : Pairing T C) : List (Touch T C) :=
  [⟨y,true,invert q.inj true⟩,
   ⟨y,true,invert q.scatter true⟩,
   ⟨x,false,q.copy⟩,
   ⟨x,false,q.gather⟩,
   ⟨y,true,q.scatter⟩,
   ⟨y,true,q.inj⟩,
   ⟨x,false,invert q.gather true⟩,
   ⟨x,false,invert q.copy true⟩]
def back (q : Pairing T C) : List (Touch T C) :=
  [⟨y,false,q.copy⟩,
   ⟨y,false,q.gather⟩,
   ⟨x,true,invert q.inj true⟩,
   ⟨x,true,invert q.scatter true⟩,
   ⟨y,false,invert q.gather true⟩,
   ⟨y,false,invert q.copy true⟩,
   ⟨x,true,q.scatter⟩,
   ⟨x,true,q.inj⟩]
variable [Fintype T] [Fintype C] {R : Type} [Ring R]

-- goal property for bank data
def acts (q : Pairing T C) (h : R) :=
  ∀ v : T → R, let hits := readSrc h q.copy v + readSrc h q.gather v
    readAux h q.scatter hits + readAux h q.inj hits = v

def evalStep (h : R) (z : View T C R) (e : Touch T C) := e.step h z

set_option maxRecDepth 1500 in
theorem fwd_run (q : Pairing T C) (h : R) (neat : q.acts h) (z : View T C R) :
    q.fwd.foldl (evalStep h) z = { z with y := z.y + z.x } := by
  have ch : readAux h q.scatter (readSrc h q.copy z.x) +
      readAux h q.scatter (readSrc h q.gather z.x) +
      (readAux h q.inj (readSrc h q.copy z.x) +
        readAux h q.inj (readSrc h q.gather z.x)) = z.x := by
    simpa only [readAux_add] using (neat z.x)
  simp only [fwd, List.foldl_cons, List.foldl_nil, evalStep, step_io, ite_true,
    Bool.false_eq_true, ite_false, View.store, View.bank, readAux_neg, readSrc_neg, readAux_add]
  -- structure with two differing fields
  congr 1
  · conv_rhs => rw [← ch]
    abel
  abel

set_option maxRecDepth 1500 in
theorem back_run (q : Pairing T C) (h : R) (neat : q.acts h) (z : View T C R) :
    q.back.foldl (evalStep h) z = { z with x := z.x - z.y } := by
  have ch : readAux h q.scatter (readSrc h q.copy z.y) +
      readAux h q.scatter (readSrc h q.gather z.y) +
      (readAux h q.inj (readSrc h q.copy z.y) +
        readAux h q.inj (readSrc h q.gather z.y)) = z.y := by
    simpa only [readAux_add] using (neat z.y)
  simp only [back, List.foldl_cons, List.foldl_nil, evalStep, step_io, ite_true,
    Bool.false_eq_true, ite_false, View.store, View.bank, readAux_neg, readSrc_neg, readAux_add,
    readAux_negative]
  congr 1
  · conv_rhs => rw [← ch]
    abel
  abel

end Pairing
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
