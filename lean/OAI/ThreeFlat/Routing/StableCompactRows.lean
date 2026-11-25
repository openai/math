import OAI.ThreeFlat.BitNetwork
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Site-fast physical templates for stable compaction -/

open scoped BigOperators
namespace ThreeFlat.Routing.StableCompactRows

/-- A source is uniform across sites. Public shifts index hidden wires by bitwise xor. -/
inductive Source (m h : ℕ)
  | constant (b : Bool)
  | siteBit (j : ℕ)
  | pin (stream : Fin 3)
  | hidden (reg : Fin h) (mask : Fin (2^m))
  deriving DecidableEq

def bankPin (m : ℕ) (stream : Fin 3) (v : Fin (2^m)) : Fin (2^m + (2^m + 2^m)) :=
  ![v.castAdd (2^m + 2^m), Fin.natAdd (2^m) (v.castAdd (2^m)),
    Fin.natAdd (2^m) (Fin.natAdd (2^m) v)] stream

@[simp] theorem bankPin_val (m : ℕ) (stream : Fin 3) (v : Fin (2^m)) :
    (bankPin m stream v).val = stream.val * 2^m + v.val := by
  fin_cases stream <;> simp [bankPin,Fin.natAdd,Fin.castAdd,Nat.succ_mul,Nat.add_assoc]

/-- The three contiguous public banks contain the mask, input, and output bits. -/
def pins {m : ℕ} (M X Y : Fin (2^m) → Bool) : Fin (2^m + (2^m+2^m)) → Bool :=
  Fin.append M (Fin.append X Y)

@[simp] theorem pins_bankPin {m : ℕ} (M X Y : Fin (2^m) → Bool) (j : Fin 3) (v : Fin (2^m)) :
    pins M X Y (bankPin m j v) = ![M v,X v,Y v] j := by
  fin_cases j <;> simp [pins,bankPin,-Fin.natAdd_eq_addNat]

def Source.read {m h : ℕ} (s : Source m h) (M X Y : Fin (2^m) → Bool)
    (hidden : Fin h → Fin (2^m) → Bool) (v : Fin (2^m)) : Bool :=
  match s with
  | .constant b => b
  | .siteBit j => v.val.testBit j
  | .pin stream => ![M v,X v,Y v] stream
  | .hidden reg mask => hidden reg (v ^^^ mask)

def Source.physical {m h : ℕ} (s : Source m h) (v : Fin (2^m)) :
    BitSource (h*2^m) (2^m + (2^m+2^m)) :=
  match s with
  | .constant b => .constant b
  | .siteBit j => .constant (v.val.testBit j)
  | .pin stream => .pin (bankPin m stream v)
  | .hidden reg mask => .hidden (finProdFinEquiv (reg,v ^^^ mask))

/-- The tables and wirings of a single site determine all the physical rows. -/
structure Template (F : Type*) (m h : ℕ) where
  cells : ℕ
  source : Fin cells → Fin 3 → Source m h
  table : Fin cells → (Fin 3 → Bool) → F

namespace Template
variable {F : Type*} {m h : ℕ} (T : Template F m h)

def network : BitNetwork F (2^m + (2^m+2^m)) where
  internal := h*2^m
  cells := T.cells*2^m
  source k j := (T.source (finProdFinEquiv.symm k).1 j).physical (finProdFinEquiv.symm k).2
  table k := T.table (finProdFinEquiv.symm k).1

@[simp] theorem network_source (t : Fin T.cells) (v : Fin (2^m)) (j : Fin 3) :
    T.network.source (finProdFinEquiv (t,v)) j = (T.source t j).physical v := by simp [network]
@[simp] theorem network_table (t : Fin T.cells) (v : Fin (2^m)) :
    T.network.table (finProdFinEquiv (t,v)) = T.table t := by simp [network]
@[simp] theorem network_cells : T.network.cells = T.cells * 2^m := rfl
@[simp] theorem network_internal : T.network.internal = h * 2^m := rfl

private def group : (Fin h → Fin (2^m) → Bool) ≃ (Fin (h*2^m) → Bool) where
  toFun g k := g (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun g r v := g (finProdFinEquiv (r,v))
  left_inv g := by funext r v; simp
  right_inv g := by funext k; exact congrArg g (finProdFinEquiv.apply_symm_apply k)

private theorem group_apply (H : Fin h → Fin (2^m) → Bool) (r : Fin h) (v : Fin (2^m)) :
    group H (finProdFinEquiv (r,v)) = H r v := by
  change H ((finProdFinEquiv.symm (finProdFinEquiv (r,v))).1)
    ((finProdFinEquiv.symm (finProdFinEquiv (r,v))).2) = _
  rw [Equiv.symm_apply_apply]

private theorem projected (s : Source m h) (M X Y : Fin (2^m) → Bool)
    (H : Fin h → Fin (2^m) → Bool) (v : Fin (2^m)) :
    (s.physical v).read (group H) (pins M X Y) = s.read M X Y H v := by
  cases s <;> simp only [Source.physical,Source.read,BitSource.read,group_apply,pins_bankPin]

/-- Evaluating the flattened physical network is exactly the product of the
site factors, summed over all the shared, xor-addressed hidden wires. -/
theorem network_eval [CommSemiring F] (M X Y : Fin (2^m) → Bool) :
    T.network.eval (pins M X Y) =
      ∑ H : Fin h → Fin (2^m) → Bool, ∏ v : Fin (2^m), ∏ t : Fin T.cells,
        T.table t (fun j => (T.source t j).read M X Y H v) := by
  classical
  let f : (Fin (h*2^m) → Bool) → F := T.network.weight (pins M X Y)
  change (∑ flat : Fin (h*2^m) → Bool, f flat) = _
  rw [← (group (h := h) (m := m)).sum_comp f]
  refine Finset.sum_congr rfl fun H _ => ?_
  let g : Fin (T.cells*2^m) → F := T.network.factor (pins M X Y) (group H)
  change (∏ k : Fin (T.cells*2^m),g k) = _
  rw [← finProdFinEquiv.prod_comp g,Fintype.prod_prod_type,Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun t _ => ?_
  simp [g,BitNetwork.factor,projected]

end Template
end ThreeFlat.Routing.StableCompactRows

end OAI
