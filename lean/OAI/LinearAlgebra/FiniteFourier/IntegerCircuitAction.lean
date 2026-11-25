import OAI.LinearAlgebra.FiniteFourier.Circuit

/-! # Executing integer linear circuits on abelian groups

Each weighted binary gate expands to two prescribed integer scalings and an
addition. A scaled readout uses one further scaling. Expressions at a gate
refer to available wires, so using an earlier register again is free.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- A linear expression in available wires using the charged group operations. -/
inductive IntegerLinearExpr (I : Type*) where
  | zero
  | wire (i : I)
  | add (a b : IntegerLinearExpr I)
  | sub (a b : IntegerLinearExpr I)
  | scale (c : ℤ) (a : IntegerLinearExpr I)

namespace IntegerLinearExpr

/-- Evaluate using the additive group operations and fixed integer action. -/
def eval {I G : Type*} [AddCommGroup G] (x : I → G) : IntegerLinearExpr I → G
  | .zero => 0
  | .wire i => x i
  | .add a b => a.eval x + b.eval x
  | .sub a b => a.eval x - b.eval x
  | .scale c a => c • a.eval x

/-- Count one gate per addition, subtraction or prescribed integer scaling. -/
def cost {I : Type*} : IntegerLinearExpr I → ℕ
  | .zero | .wire _ => 0
  | .add a b | .sub a b => a.cost + b.cost + 1
  | .scale _ a => a.cost + 1

end IntegerLinearExpr

def BinaryGate.integerExpr {I : Type*} (g : BinaryGate ℤ I) : IntegerLinearExpr I :=
  .add (.scale g.leftCoeff (.wire g.left)) (.scale g.rightCoeff (.wire g.right))

def Readout.integerExpr {I : Type*} : Readout ℤ I → IntegerLinearExpr I
  | .zero => .zero
  | .scaled c w => .scale c (.wire w)

/-- Store the values of the same registers when running the expanded gates on
group elements. -/
def Program.groupValue {I G : Type*} [AddCommGroup G] :
    {s : ℕ} → Program ℤ I s → (I → G) → Fin s → G
  | _, .nil, _ => Fin.elim0
  | _, .step p g, x =>
    Fin.cases (g.integerExpr.eval (Sum.elim x (p.groupValue x))) (p.groupValue x)

def Program.integerCost {I : Type*} : {s : ℕ} → Program ℤ I s → ℕ
  | _, .nil => 0
  | _, .step p g => p.integerCost + g.integerExpr.cost

theorem Program.integerCost_eq {I : Type*} {s : ℕ} (p : Program ℤ I s) :
    p.integerCost = 3*s := by
  induction p with
  | nil => rfl
  | step p g ih =>
    change p.integerCost + 3 = _
    rw [ih, Nat.mul_add]

namespace Circuit

def evalGroup {I O G : Type*} [AddCommGroup G] {s : ℕ} (p : Circuit ℤ I O s)
    (x : I → G) (o : O) : G :=
  (p.output o).integerExpr.eval (Sum.elim x (p.program.groupValue x))

/-- Cost of running the shared program once and then evaluating all readouts. -/
def integerCost {I O : Type*} [Fintype O] {s : ℕ} (p : Circuit ℤ I O s) : ℕ :=
  p.program.integerCost + ∑ o, (p.output o).integerExpr.cost

theorem integerCost_le {I O : Type*} [Fintype O] {s : ℕ} (p : Circuit ℤ I O s) :
    p.integerCost ≤ 3*s + Fintype.card O := by
  unfold integerCost
  rw [Program.integerCost_eq]
  apply Nat.add_le_add_left
  calc
    ∑ o, (p.output o).integerExpr.cost ≤ ∑ _ : O, 1 := Finset.sum_le_sum fun o _ => by
      cases p.output o <;> simp [Readout.integerExpr, IntegerLinearExpr.cost]
    _ = _ := by simp

private theorem groupWire_eq_sum {I G : Type*} [AddCommGroup G] [Fintype I] [DecidableEq I]
    {s : ℕ} (p : Program ℤ I s) (x : I → G) (w : I ⊕ Fin s) :
    Sum.elim x (p.groupValue x) w =
      ∑ i, Sum.elim (Pi.single i 1) (p.value (Pi.single i 1)) w • x i := by
  classical
  induction p with
  | nil =>
    cases w with
    | inl j => simp [Pi.single_apply, ite_smul]
    | inr j => exact j.elim0
  | step p g ih =>
    cases w with
    | inl j => simp [Pi.single_apply, ite_smul]
    | inr j =>
      refine Fin.cases ?_ (fun k => ih (.inr k)) j
      change g.leftCoeff • Sum.elim x (p.groupValue x) g.left +
        g.rightCoeff • Sum.elim x (p.groupValue x) g.right =
        ∑ i, g.eval _ • x i
      rw [ih g.left, ih g.right]
      simp only [BinaryGate.eval, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

/-- The gate-by-gate evaluation acts by the circuit's integer matrix on
every abelian group. -/
theorem evalGroup_eq_sum {I O G : Type*} [Fintype I] [AddCommGroup G] {s : ℕ}
    (p : Circuit ℤ I O s) (x : I → G) (o : O) :
    p.evalGroup x o = ∑ i, p.matrix o i • x i := by
  classical
  simp only [evalGroup, matrix_apply, eval]
  cases p.output o with
  | zero => simp [Readout.integerExpr, IntegerLinearExpr.eval, Readout.eval]
  | scaled c w =>
    change c • Sum.elim x (p.program.groupValue x) w =
      ∑ i, (c * Sum.elim (Pi.single i 1) (p.program.value (Pi.single i 1)) w) • x i
    rw [groupWire_eq_sum]
    simp only [mul_smul, Finset.smul_sum]

end Circuit

end FiniteFourier
end LinearAlgebra
end OAI
