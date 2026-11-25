import OAI.Computability.VPVNP.VerifierMachineNetwork

/-!
# Adding a fixed table entry to a binary rank

The include-or-exclude ranking table has fixed integer entries. Each output bit of
addition by such a constant has a formula of linear size in its position. The ripple
carry through a constant bit uses either a single AND or a single OR.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.StateIndex

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

variable {σ : Type*}

/-- Carry from all lower-order positions in a binary addition by the constant `a`. -/
def carryExpr (wire : ℕ → Expr σ) (a : ℕ) : ℕ → Expr σ
  | 0 => .const false
  | j+1 => if a.testBit j then .or (wire j) (carryExpr wire a j)
           else .and (wire j) (carryExpr wire a j)

/-- Output bit `j` after adding the fixed natural number `a`. -/
def addConstBit (wire : ℕ → Expr σ) (a j : ℕ) : Expr σ :=
  let c := carryExpr wire a j
  let v := Expr.mux (wire j) (.not c) c
  if a.testBit j then .not v else v

private theorem carryExpr_eval (wire : ℕ → Expr σ) (input : σ → Bool) (a x w j : ℕ) (hj : j ≤ w)
    (h : ∀ i < j, (wire i).eval input = x.testBit i) :
    (carryExpr wire a j).eval input = BitVec.carry j (BitVec.ofNat w x) (BitVec.ofNat w a) false := by
  induction j with
  | zero => simp [carryExpr, Expr.eval]
  | succ j ih =>
    have hjw : j < w := by omega
    have prev := ih (by omega) (fun i hi => h i (by omega))
    rw [BitVec.carry_succ]
    simp only [BitVec.getLsbD_ofNat, hjw, decide_true, Bool.true_and]
    cases ha : a.testBit j <;> cases hx : x.testBit j <;>
      simp [carryExpr, ha, Expr.eval, h j (by omega), hx, prev, Bool.atLeastTwo]

/-- The formula computes the requested bit of the ordinary natural-number sum. -/
theorem addConstBit_eval (wire : ℕ → Expr σ) (input : σ → Bool) (a x j : ℕ)
    (h : ∀ i ≤ j, (wire i).eval input = x.testBit i) :
    (addConstBit wire a j).eval input = (a+x).testBit j := by
  let w := j+1
  have hj : j < w := by dsimp [w]; omega
  have hc := carryExpr_eval wire input a x w j hj.le (fun i hi => h i hi.le)
  have hsum := BitVec.getLsbD_add hj (BitVec.ofNat w x) (BitVec.ofNat w a)
  rw [BitVec.ofNat_add_ofNat, Nat.add_comm x a] at hsum
  simp only [BitVec.getLsbD_ofNat, hj, decide_true, Bool.true_and] at hsum
  rw [hsum, ← hc]
  cases ha : a.testBit j <;> cases hx : x.testBit j <;>
    simp [addConstBit, ha, hx, Expr.eval, h j le_rfl]

private theorem carryExpr_size (wire : ℕ → Expr σ) (a j : ℕ) (h : ∀ i, (wire i).size ≤ 1) :
    (carryExpr wire a j).size ≤ 2*j+1 := by
  induction j with
  | zero => simp [carryExpr, Expr.size]
  | succ j ih =>
    have := h j
    cases ha : a.testBit j <;> simp only [carryExpr, ha, Bool.false_eq_true, ↓reduceIte, Expr.size] <;> omega

/-- At most four formula nodes per lower bit and ten further nodes for the selected bit. -/
theorem addConstBit_size (wire : ℕ → Expr σ) (a j : ℕ) (h : ∀ i, (wire i).size ≤ 1) :
    (addConstBit wire a j).size ≤ 4*j+10 := by
  have hc := carryExpr_size wire a j h
  have hw := h j
  cases ha : a.testBit j <;>
    simp only [addConstBit, ha, Bool.false_eq_true, ↓reduceIte, Expr.mux, Expr.size] <;> omega

end Crossing.StateIndex

end BorderVNP
end Computability
end OAI
