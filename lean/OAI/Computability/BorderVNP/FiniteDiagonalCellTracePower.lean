import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceNative
import OAI.Computability.BorderVNP.FiniteCellCopiesScan

/-! # A terminal field return for the cell multiplicity scanner

The scanner multiplies field factors along its deterministic count-bit loop.
The compiled finite control carries this accumulator into its sole possible
successful native terminal. At a nonzero output the consumed choice tape is empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace

open VPVNP.RAMTape CellMacro.StackTape TeamPrivateTape

private theorem deterministicLeaves {K Q : Type} [DecidableEq K] {V : Type*}
    (C : StackCode K Q) (weight : Q → V) (hd : ∀ q l r, C q ≠ .choose l r) (fuel : ℕ) (q : Q) (s : Stacks K) :
    FieldReplay.leaves C weight fuel q s = ∅ ∨ ∃ v, FieldReplay.leaves C weight fuel q s = {([],v)} := by
  classical
  induction fuel generalizing q s with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rw [FieldReplay.leaves]
    cases h : C q with
    | push | pop | goto => exact ih _ _
    | choose l r => exact (hd q l r h).elim
    | halt b => cases b <;> simp

private theorem nonzero_deterministic_return {K Q : Type} [DecidableEq K] {F : Type*} [Field F]
    (C : StackCode K Q) (weight : Q → F) (hd : ∀ q l r, C q ≠ .choose l r) (fuel : ℕ) (q : Q) (s : Stacks K)
    (bs : List Bool) {z : F} (hz : z ≠ 0) :
    (bs,z) ∈ FieldReplay.leaves C weight fuel q s ↔ bs = [] ∧ z = FieldStack.paths C weight fuel q s := by
  rw [FieldReplay.paths_eq_sum]
  rcases deterministicLeaves C weight hd fuel q s with h | ⟨v,h⟩ <;> simp [h,hz]

variable {F : Type*} [Field F] [Fintype F] {k : ℕ}

/-- The weighted scanner becomes a finite, deterministic program with an actual field ID
in its terminal state. The accumulator starts at the ID of one. -/
noncomputable def powerCode (v : Fin k → F) :=
  FieldStack.productCode (FieldPowers.program v) FieldPowers.factor

/-- Scalar emitted on the private machine's accepting terminal. -/
noncomputable def powerOutput (q : FieldStack.ProductState (FieldPowers.State k (Fintype.card F)) F) :=
  FieldStack.productOutput FieldPowers.factor (fun _ => 1) q

private theorem powerDeterministic (v : Fin k → F) (q l r) : powerCode v q ≠ .choose l r := by
  rcases q with ⟨q,a⟩
  cases q with
  | visit left => by_cases h : left.val = 0 <;> simp [powerCode,FieldStack.productCode,FieldPowers.program,h,StackOp.rename]
  | read | useBit => simp [powerCode,FieldStack.productCode,FieldPowers.program,StackOp.rename]

/-- At the physical two-tick compilation clock and fixed scalar table, exactly the empty
private tape can return a nonzero product, and the product equals the decoded field powers. -/
theorem power_native_return (v : Fin k → F) (t : Fin k → SymbolTape (Option Bool)) (bs : List Bool)
    {z : F} (hz : z ≠ 0) :
    let counts := values (Equiv.refl (Fin k)) t
    let fuel := 1 + ∑ i, (2*(counts i).length+2)
    let start : FieldStack.ProductState (FieldPowers.State k (Fintype.card F)) F :=
      (.visit (Fin.last k),Fintype.equivFin F 1)
    FieldSelect.nativeReturn (table (Equiv.refl (Fin k)) (powerCode v) (fun _ => false)) none
      (terminalOutput powerOutput) (2*fuel) (.ready start) t bs = some z ↔
      bs = [] ∧ z = ∏ i, v i ^ FieldPowers.digits (counts i) := by
  intro counts fuel start
  rw [nativeReturn_iff,nonzero_deterministic_return _ _ (powerDeterministic v) _ _ _ _ hz]
  have h := FieldStack.productCode_value (FieldPowers.program v) FieldPowers.factor (fun _ => 1)
    fuel (.visit (Fin.last k)) counts (1 : F)
  change FieldStack.paths (powerCode v) powerOutput fuel start counts = _ at h
  rw [one_mul, FieldPowers.evaluate] at h
  rw [h]

end FiniteDiagonal.CellTrace

end BorderVNP
end Computability
end OAI
