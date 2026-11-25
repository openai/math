import OAI.ThreeFlat.Diagonal.TraceCircuitArray

namespace OAI
/-! # Dense network for the product of guarded collapse evaluations

Each block has one copy of the collapse trace and one equality row per
preserved active bit. The shared input wires address the intermediate block
states and auxiliary fixings. Private trace wires occupy separate consecutive
regions for the different copies.
-/

namespace ThreeFlat.Diagonal.GuardedNetwork

open TraceCircuit

variable {F : Type*} [CommSemiring F] {p q b t : ℕ}

def widen (extra : ℕ) {n : ℕ} : BitSource n q → BitSource n (q+extra)
  | .pin i => .pin (i.castAdd extra)
  | .hidden i => .hidden i
  | .constant v => .constant v

theorem widen_read (extra : ℕ) {n : ℕ} (a : BitSource n q) (x : Fin (q+extra) → Bool) (h : Fin n → Bool) :
    (widen extra a).read h x = a.read h (fun i => x (i.castAdd extra)) := by cases a <;> rfl

/-- The old external pins precede a left guard array and a right guard array. -/
def row (N : BitNetwork F q) (e : ℕ) : Fin (N.cells+e) → Cell F N.internal (q+(e+e)) :=
  Fin.append
    (fun i => ⟨fun j => widen (e+e) (N.source i j), N.table i⟩)
    (fun i => ⟨![.pin (Fin.natAdd q (i.castAdd e)), .pin (Fin.natAdd q (Fin.natAdd e i)),
      .constant false], fun v => if v 0 = v 1 then 1 else 0⟩)

theorem row_weight (N : BitNetwork F q) (e : ℕ) (x : Fin (q+(e+e)) → Bool) (h : Fin N.internal → Bool) :
    (∏ i, (row N e i).eval x h) =
      if ∀ i : Fin e, x (Fin.natAdd q (i.castAdd e)) = x (Fin.natAdd q (Fin.natAdd e i)) then
        N.weight (fun i => x (i.castAdd (e+e))) h else 0 := by
  rw [Fin.prod_univ_add]
  simp only [row, Fin.append_left, Fin.append_right, Cell.eval, widen_read]
  change N.weight _ h * (∏ i : Fin e, if x (Fin.natAdd q (i.castAdd e)) = x (Fin.natAdd q (Fin.natAdd e i)) then (1 : F) else 0) = _
  rw [Fintype.prod_boole]
  split_ifs <;> simp_all

/-- Supply the fields of the trace and both sides of the guard constraints by translation
of their addresses into the public wire or shared guess arrays. -/
def ports (input : Fin t → Fin q → BitSource b p) {e : ℕ}
    (left right : Fin t → Fin e → BitSource b p) (i : Fin t) :=
  Fin.append (input i) (Fin.append (left i) (right i))

def network (N : BitNetwork F q) {e : ℕ} (input : Fin t → Fin q → BitSource b p)
    (left right : Fin t → Fin e → BitSource b p) : BitNetwork F p :=
  assemble (fun _ => row N e) (ports input left right)

@[simp] theorem cells (N : BitNetwork F q) {e : ℕ} (input : Fin t → Fin q → BitSource b p)
    (left right : Fin t → Fin e → BitSource b p) :
    (network N input left right).cells = t*(N.cells+e) := rfl

@[simp] theorem hidden (N : BitNetwork F q) {e : ℕ} (input : Fin t → Fin q → BitSource b p)
    (left right : Fin t → Fin e → BitSource b p) :
    (network N input left right).internal = b+t*N.internal := rfl

theorem eval (N : BitNetwork F q) {e : ℕ} (input : Fin t → Fin q → BitSource b p)
    (left right : Fin t → Fin e → BitSource b p) (x : Fin p → Bool) :
    (network N input left right).eval x =
      ∑ h : Fin b → Bool, ∏ i : Fin t,
        if ∀ j, (left i j).read h x = (right i j).read h x then
          N.eval (fun j => (input i j).read h x) else 0 := by
  classical
  rw [network, assemble_eval]
  simp_rw [row_weight]
  simp only [ports, Fin.append_left, Fin.append_right]
  refine Finset.sum_congr rfl fun h _ => Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp_all [BitNetwork.eval]

end ThreeFlat.Diagonal.GuardedNetwork

end OAI
