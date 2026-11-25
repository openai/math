import OAI.Computability.BorderVNP.StackFrameMachine
import OAI.Computability.BinPacking.CookLevin.MachineCircuit
import OAI.Computability.VPVNP.VerifierMachineNetwork

/-!
# Shared Boolean frames for deterministic binary stack computations

A finite stack program is restricted to its actual finite control support.
Each clock tick appends one layer of the checked Cook–Levin Boolean
expressions. A completed execution sticks at its output, so the same frame
works for every word of bounded length and every running time below the
chosen horizon.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackFrame

open RationalHitting.StackLanguage Turing
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity
open CookLevin CookLevin.StatementCircuit

/-- Three wires per slot distinguish an absent bit, false, and true. -/
abbrev Slots (W : ℕ) := Fin W × Option Bool

/-- The one-hot, zero-extended encoding of a variable-length stack word. -/
def padded (W : ℕ) (w : List Bool) (i : Slots W) : Bool := decide (w[i.1.val]? = i.2)

variable {K : Type} [DecidableEq K] [Fintype K]

private abbrev Bits (p : Program K) (S : ℕ) :=
  ConfigBit (fun _ : K => Bool) ↥(support p) (Option Bool) S

private def initialExpr (p : Program K) (ki ko : K) (W S : ℕ) : Bits p S → StatementCircuit.Expr (Slots W)
  | .inl l => .const (decide (some (finiteMachine p ki ko).main = l))
  | .inr (.inl v) => .const (decide ((none : Option Bool) = v))
  | .inr (.inr ⟨k,j,b⟩) =>
    if k = ki then
      if h : j.val < W then .input (⟨j.val,h⟩,b) else .const (decide ((none : Option Bool) = b))
    else .const (decide ((none : Option Bool) = b))

private theorem initialExpr_eval (p : Program K) (ki ko : K) {W S : ℕ} (w : List Bool)
    (hw : w.length ≤ W) (i : Bits p S) :
    (initialExpr p ki ko W S i).eval (padded W w) =
      configEncoding S (initList (finiteMachine p ki ko) w) i := by
  rcases i with l | v | ⟨k,j,b⟩
  · rfl
  · rfl
  · by_cases hk : k = ki
    · subst k
      by_cases hj : j.val < W
      · simp [initialExpr, configEncoding, inputEncoding, initList, finiteMachine,
          StatementCircuit.Expr.eval, hj, padded]
      · have he : w[j.val]? = none := List.getElem?_eq_none (by omega)
        simp [initialExpr, configEncoding, inputEncoding, initList, finiteMachine, StatementCircuit.Expr.eval,
          hj, he]
    · simp [initialExpr, configEncoding, inputEncoding, initList, finiteMachine, hk, StatementCircuit.Expr.eval]

private theorem initialExpr_size (p : Program K) (ki ko : K) (W S : ℕ) (i : Bits p S) :
    (initialExpr p ki ko W S i).size ≤ 1 := by
  rcases i with l | v | ⟨k,j,b⟩
  · rfl
  · rfl
  · simp only [initialExpr]
    split_ifs <;> rfl

private noncomputable def capacity (p : Program K) (ki ko : K) (W T : ℕ) : ℕ :=
  W+(T+2)*Runtime.programPushBound (finiteMachine p ki ko)

private noncomputable def layers (p : Program K) (ki ko : K) (W S t : ℕ) :
    Frame (Slots W) (Bits p S) :=
  ((Frame.initial id).step (initialExpr p ki ko W S)).steps
    (fun _ => MachineCircuit.stickyExpr S (finiteMachine p ki ko).m) t

private theorem layers_correct (p : Program K) (ki ko : K) {W T : ℕ}
    (w : List Bool) (hw : w.length ≤ W) (t : ℕ) (ht : t ≤ T+2) :
    (layers p ki ko W (capacity p ki ko W T) t).eval (padded W w) =
      configEncoding (capacity p ki ko W T) (BoundedExecution.run (finiteMachine p ki ko) w t) := by
  let tm := finiteMachine p ki ko
  let S := capacity p ki ko W T
  induction t with
  | zero =>
    funext i
    change ((Frame.initial id).step _).eval _ _ = _
    rw [Frame.step_eval]
    have h0 : (Frame.initial id).eval (padded W w) = padded W w := funext (fun j => by simp)
    rw [h0]
    exact initialExpr_eval p ki ko w hw i
  | succ t ih =>
    funext i
    change ((layers p ki ko W S t).step (MachineCircuit.stickyExpr S tm.m)).eval _ i = _
    rw [Frame.step_eval,ih (by omega)]
    rw [BoundedExecution.run_succ]
    refine MachineCircuit.stickyExpr_eval S tm.m (BoundedExecution.run tm w t) ?_ i
    intro label _
    apply (BoundedExecution.run_statement_safe tm w (T+2) t (by omega) label).mono
    exact Nat.add_le_add_right hw _

/-- The Boolean frame for a fixed stack program. It simulates two extra steps
for entry and halt, and outputs `W` positions of the designated stack. -/
noncomputable def programFrame (p : Program K) (ki ko : K) (W T : ℕ) : Frame (Slots W) (Slots W) :=
  let S := capacity p ki ko W T
  (layers p ki ko W S (T+2)).select fun ⟨j,b⟩ =>
    .inr (.inr ⟨ko, j.castLE (Nat.le_add_right _ _), b⟩)

/-- On every stack word of length at most `W`, every genuine evaluation
completed within `T` ticks yields the correct output in each of the `W` slots. -/
theorem programFrame_correct (p : Program K) (ki ko : K) {W T : ℕ} {w y : List Bool} {t : ℕ}
    (h : Eval p (single ki w) (single ko y) t) (hw : w.length ≤ W) (ht : t ≤ T) :
    (programFrame p ki ko W T).eval (padded W w) = padded W y := by
  funext ⟨j,b⟩
  rw [programFrame,Frame.select_eval,layers_correct p ki ko w hw (T+2) le_rfl,run_of_eval p ki ko h ht]
  simp [configEncoding,inputEncoding,haltList,finiteMachine,padded,Fin.castLE]

/-- The gate count is quadratic in the combined time and word-width budget.
The constant depends only on the finite control and register set of the program. -/
theorem programFrame_size (p : Program K) (ki ko : K) :
    ∃ C : ℕ, ∀ W T, (programFrame p ki ko W T).size ≤ C*(W+T+3)^2 := by
  let tm := finiteMachine p ki ko
  let k := Fintype.card K
  let l := Fintype.card ↥(support p)
  let b := Runtime.programPushBound tm
  let e := MachineCircuit.expressionCost tm.m
  refine ⟨(l+4+3*k)*(b+1)*(e+1),?_⟩
  intro W T
  let S := capacity p ki ko W T
  let n := W+T+3
  let first := (Frame.initial id).step (initialExpr p ki ko W S)
  have hinit : first.size ≤ Fintype.card (Bits p S) := by
    simpa [first] using Frame.step_size_le (Frame.initial id) (initialExpr p ki ko W S) 1
      (initialExpr_size p ki ko W S)
  have hsim := Frame.steps_size_le first (fun _ => MachineCircuit.stickyExpr S tm.m) (T+2) e
    (fun _ _ i => MachineCircuit.stickyExpr_size_le S tm.m i)
  have hwidth : Fintype.card (Bits p S) = l+4 + k*(S*3) := by
    simp [Bits,ConfigBit,InputBit,l,k,add_assoc,add_comm,add_left_comm]
    omega
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hs : S ≤ n*(b+1) := by
    change W+(T+2)*b ≤ _
    have ht' : T+2 ≤ n := by dsimp [n]; omega
    calc
      _ ≤ n+n*b := Nat.add_le_add (by dsimp [n]; omega) (Nat.mul_le_mul_right _ ht')
      _ = _ := by ring
  have hw : Fintype.card (Bits p S) ≤ (l+4+3*k)*(b+1)*n := by
    rw [hwidth]
    have hn' : 1 ≤ n*(b+1) := Nat.mul_pos hn (by omega)
    calc
      _ ≤ (l+4)*(n*(b+1)) + k*((n*(b+1))*3) :=
        Nat.add_le_add (Nat.le_mul_of_pos_right _ hn') (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 3 hs))
      _ = _ := by ring
  have ht' : T+2 ≤ n := by dsimp [n]; omega
  rw [programFrame,Frame.select_size]
  calc
    _ ≤ Fintype.card (Bits p S) + (T+2)*(Fintype.card (Bits p S)*e) :=
      hsim.trans (Nat.add_le_add_right hinit _)
    _ ≤ ((l+4+3*k)*(b+1)*n)*n + n*(((l+4+3*k)*(b+1)*n)*e) :=
      Nat.add_le_add (hw.trans (Nat.le_mul_of_pos_right _ hn)) (Nat.mul_le_mul ht' (Nat.mul_le_mul_right _ hw))
    _ = _ := by dsimp [n]; ring

end StackFrame

end BorderVNP
end Computability
end OAI
