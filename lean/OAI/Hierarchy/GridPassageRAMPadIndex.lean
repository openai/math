import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Padding ordinals for cells, directions, and catalyst ranks -/

namespace Hierarchy.GridPassageRAMPadIndex

variable {g k B : ℕ}

def key (x : Fin k → Fin g) (j : Fin k) : ℕ :=
  (finFunctionFinEquiv x).val*k+j.val

def ordinal (x : Fin k → Fin g) (j : Fin k) (r : Fin B) : ℕ :=
  key x j*B+r.val

/-- The low digit is the padded rank, followed by the direction and the cell ordinal. -/
def indexEquiv (k g B : ℕ) : (((Fin k → Fin g) × Fin k) × Fin B) ≃ Fin (g^k*k*B) :=
  (Equiv.prodCongr ((Equiv.prodCongr finFunctionFinEquiv (Equiv.refl _)).trans finProdFinEquiv)
    (Equiv.refl _)).trans finProdFinEquiv

@[simp] theorem indexEquiv_val (x : Fin k → Fin g) (j : Fin k) (r : Fin B) :
    (indexEquiv k g B ((x,j),r)).val = ordinal x j r := by
  change r.val + B*(j.val+k*(finFunctionFinEquiv x).val) =
    ((finFunctionFinEquiv x).val*k+j.val)*B+r.val
  ac_rfl

theorem ordinal_lt (x : Fin k → Fin g) (j : Fin k) (r : Fin B) :
    ordinal x j r < g^k*k*B := by
  simpa only [indexEquiv_val] using (indexEquiv k g B ((x,j),r)).isLt

/-- Every row in the sweep names one and only one triple, including at the
boundary of any row or cell. -/
theorem decode (a : ℕ) (ha : a < g^k*k*B) :
    ∃! u : ((Fin k → Fin g) × Fin k) × Fin B, ordinal u.1.1 u.1.2 u.2 = a := by
  let e := indexEquiv k g B
  let u := e.symm ⟨a,ha⟩
  have val (z : ((Fin k → Fin g) × Fin k) × Fin B) :
      (e z).val = ordinal z.1.1 z.1.2 z.2 := indexEquiv_val ..
  have hu : e u = ⟨a,ha⟩ := e.apply_symm_apply _
  refine ⟨u, (val u).symm.trans (congrArg Fin.val hu), ?_⟩
  intro z hz
  apply e.injective
  rw [hu]
  exact Fin.ext ((val z).trans hz)

private theorem div_digit (a b r : ℕ) (hr : r<b) : (a*b+r)/b = a := by
  rw [Nat.mul_comm a b,Nat.mul_add_div (Nat.zero_lt_of_lt hr),Nat.div_eq_of_lt hr,Nat.add_zero]

@[simp] theorem div_slot (x : Fin k → Fin g) (j : Fin k) (r : Fin B) :
    ordinal x j r / B = key x j := div_digit _ _ _ r.isLt

@[simp] theorem mod_slot (x : Fin k → Fin g) (j : Fin k) (r : Fin B) :
    ordinal x j r % B = r.val := by simp [ordinal,Nat.mod_eq_of_lt r.isLt]

@[simp] theorem div_axis (x : Fin k → Fin g) (j : Fin k) :
    key x j / k = (finFunctionFinEquiv x).val := div_digit _ _ _ j.isLt

@[simp] theorem mod_axis (x : Fin k → Fin g) (j : Fin k) :
    key x j % k = j.val := by simp [key,Nat.mod_eq_of_lt j.isLt]

@[simp] theorem coordinate (x : Fin k → Fin g) (j : Fin k) :
    (finFunctionFinEquiv x).val / g^j.val % g = (x j).val :=
  congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply x) j)

end Hierarchy.GridPassageRAMPadIndex

end OAI
