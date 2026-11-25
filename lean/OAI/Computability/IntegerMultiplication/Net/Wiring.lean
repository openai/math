import OAI.Computability.IntegerMultiplication.Net.Schedule

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
open Finset
/-- Fixed maps on an *ordered* set of triples.
near : which side links are active (symmetric wrt application). S argument first=T
control, second=T target.
center maps specified at a triple (types arbitrary here; use h vs h+1 centers). -/
structure Loom (T C : Type) where
  near : T → T → Bool
  sideCoef : T → T → Amount
  getCoef : T → C → Amount
  putCoef : T → C → Amount

def position {T : Type} (rev : Bool) (ctrl dst : T) : T × T :=
  if rev then (dst,ctrl) else (ctrl,dst)
namespace Loom
variable {T C : Type}
def copy [DecidableEq T] (z : Loom T C) (rev : Bool) (ctrl : T) : Aux T C → Amount
| .inr _ => .none
| .inl (x,y) =>
  if rev then (if y=ctrl && z.near y x then .unit false else .none)
  else if x=ctrl && z.near x y then .unit false else .none

def inj [DecidableEq T] (z : Loom T C) (rev : Bool) (dst : T) : Aux T C → Amount
| .inr _ => .none
| .inl (x,y) =>
  if rev then (if x=dst && z.near y x then z.sideCoef y x else .none)
  else if y=dst && z.near x y then z.sideCoef x y else .none

def pairs [DecidableEq T] (z : Loom T C) (rev : Bool) : Pairing T C where
  copy := z.copy rev
  gather := fun t a => match a with
    | .inl _ => .none
    | .inr c => z.getCoef t c
  inj := z.inj rev
  scatter := fun t a => match a with
    | .inl _ => .none
    | .inr c => z.putCoef t c

@[simp] theorem copy_pos [DecidableEq T] (z : Loom T C) (b : Bool) (t u v : T) :
    (z.pairs b).copy t (.inl (position b u v)) =
      if u=t && z.near u v then .unit false else .none := by cases b <;> rfl
@[simp] theorem inj_pos [DecidableEq T] (z : Loom T C) (b : Bool) (t u v : T) :
    (z.pairs b).inj t (.inl (position b u v)) =
      if v=t && z.near u v then z.sideCoef u v else .none := by cases b <;> rfl
@[simp] theorem copy_inr [DecidableEq T] (z : Loom T C) (b : Bool) (t : T) (c : C) :
    (z.pairs b).copy t (.inr c) = .none := rfl
@[simp] theorem inj_inr [DecidableEq T] (z : Loom T C) (b : Bool) (t : T) (c : C) :
    (z.pairs b).inj t (.inr c) = .none := rfl

variable [DecidableEq T] [Fintype T] [Fintype C] {R : Type} [Ring R]
open Touch
def good (z : Loom T C) (h : R) :=
  ∀ e g : T, (∑ c, Amount.read h (z.putCoef g c) * Amount.read h (z.getCoef e c)) +
    (if z.near e g then Amount.read h (z.sideCoef e g) else 0) =
      if e=g then 1 else 0

def hits (z : Loom T C) (h : R) (b : Bool) (v : T → R) : Aux T C → R :=
  readSrc h (z.pairs b).copy v + readSrc h (z.pairs b).gather v

omit [Fintype C] in
theorem hits_center (z : Loom T C) (h : R) (b : Bool) (v : T → R) (c : C) :
    z.hits h b v (.inr c) = ∑ t, Amount.read h (z.getCoef t c) * v t := by
  simp [hits, readSrc, pairs, copy]

omit [Fintype C] in
theorem hits_link (z : Loom T C) (h : R) (b : Bool) (v : T → R) (x y : T) :
    z.hits h b v (.inl (position b x y)) = if z.near x y then v x else 0 := by
  simp only [hits, Pi.add_apply, readSrc, copy_pos]
  cases n : z.near x y <;> simp [pairs, Amount.read, eq_comm]
  rw [Finset.sum_eq_single x]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  simp

omit [Fintype C] [DecidableEq T] in
theorem sum_positions (b : Bool) (g : T × T → R) :
    ∑ r, g r = ∑ x : T, ∑ y : T, g (position b x y) := by
  cases b
  · simp [Fintype.sum_prod_type, position]
  simp [Fintype.sum_prod_type, position]
  rw [Finset.sum_comm]

theorem center_effect (z : Loom T C) (h : R) (b : Bool) (v : T → R) (dst : T) :
    readAux h (z.pairs b).scatter (z.hits h b v) dst =
    ∑ t, (∑ c, Amount.read h (z.putCoef dst c) * Amount.read h (z.getCoef t c)) * v t := by
  rw [readAux, Fintype.sum_sum_type]
  change _ + (∑ c : C, Amount.read h (z.putCoef dst c) * z.hits h b v (.inr c)) = _
  simp_rw [hits_center, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  rw [Finset.sum_comm (s:= (univ : Finset C))]
  simp [pairs]

theorem link_effect (z : Loom T C) (h : R) (b : Bool) (v : T → R) (dst : T) :
    readAux h (z.pairs b).inj (z.hits h b v) dst =
    ∑ t, (if z.near t dst then Amount.read h (z.sideCoef t dst) else 0) * v t := by
  rw [readAux, Fintype.sum_sum_type, sum_positions b]
  change _ + (∑ c : C, Amount.read h .none * z.hits h b v (.inr c)) = _
  simp only [Amount.read_none, zero_mul, sum_const_zero, add_zero]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single dst]
  · cases n : z.near i dst <;> simp [inj_pos, hits_link, n]
  · intro j _ hj
    simp [inj_pos, hj]
  simp

theorem pairs_act (z : Loom T C) (h : R) (b : Bool) (hz : z.good h) :
    (z.pairs b).acts h := by
  unfold good at hz
  intro v
  funext dst
  change readAux h (z.pairs b).scatter (z.hits h b v) dst +
    readAux h (z.pairs b).inj (z.hits h b v) dst = v dst
  rw [center_effect, link_effect, ← Finset.sum_add_distrib]
  simp_rw [← add_mul, hz]
  simp

end Loom
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
