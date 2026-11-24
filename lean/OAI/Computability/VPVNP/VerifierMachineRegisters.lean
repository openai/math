import OAI.Computability.VPVNP.VerifierMachineSelector
import OAI.Computability.VPVNP.VerifierMachineCell

/-!
# Boolean register transitions for the coefficient machine

Each register tests one state or one symbol in a cell of one of the two tapes.
The decoder supplies one bit per transition record. A Boolean choice selects the
branch of the current row, including its write and motion fields. A missing
branch rejects, except for canonical zero padding after an accepting halt.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierMachineDecode

variable {ι : Type*} {n r : ℕ}

private def fallbackState (accept choice : Expr ι) (q : Fin (n + 2)) : Expr ι :=
  Expr.mux (.and accept (.not choice)) (.const (decide (1 = q.val))) (.const (decide (0 = q.val)))

private theorem fallbackState_eval (input : ι → Bool) {e : ℕ} (c : WindowConfig e r) (bit : Bool)
    (accept choice : Expr ι) (ha : accept.eval input = decide (c.state.val = 1))
    (hb : choice.eval input = bit) (q : Fin (n + 2)) :
    (fallbackState accept choice q).eval input =
      decide ((if c.state.val = 1 ∧ bit = false then (1 : Fin (e + 2)) else 0).val = q.val) := by
  by_cases h : c.state.val = 1 <;> cases bit <;>
    simp [fallbackState, Expr.eval_mux, Expr.eval, ha, hb, h]

private def keyWrite (tape : Bool) (k : InstructionKey n) : Symbol :=
  if tape then k.2.2.2.1 else k.2.1

private def keyMove (tape : Bool) (k : InstructionKey n) : Fin 3 :=
  if tape then k.2.2.2.2 else k.2.2.1

/-- Formula for one output register, using shared input wires for the decoded table
and the previous configuration. -/
noncomputable def registerStepExpr
    (slots : Fin (9 * n) → Bool → InstructionKey n → Expr ι)
    (reg : WindowRegister n r → Expr ι) (choice : Expr ι) :
    WindowRegister n r → Expr ι
  | .inl q =>
    let sel := selectedExpr slots reg choice
    Expr.mux (sel fun _ => true) (sel fun k => decide (k.1 = q))
      (fallbackState (reg (.inl ⟨1, by omega⟩)) choice q)
  | .inr (t, i, s) =>
    let sel := selectedExpr slots reg choice
    cellNext (fun j a => reg (.inr (t, j, a))) (sel fun _ => true)
      (fun a => sel fun k => decide (keyWrite t k = a))
      (fun d => sel fun k => decide (keyMove t k = d)) i s

/-- Evaluating the next Boolean register gives the corresponding bit of the machine step. -/
theorem registerStepExpr_eval (slots : Fin (9 * n) → Bool → InstructionKey n → Expr ι)
    (reg : WindowRegister n r → Expr ι) (choice : Expr ι) (input : ι → Bool)
    (p : Program) (h : p.extra ≤ n) (c : WindowConfig p.extra r) (bit : Bool)
    (hs : ∀ i b k, (slots i b k).eval input = true ↔ wireHolds p (.slot i b k))
    (hr : ∀ i, (reg i).eval input = registerEncoding c i)
    (hb : choice.eval input = bit) (j : WindowRegister n r) :
    (registerStepExpr slots reg choice j).eval input = registerEncoding (windowStep p c bit) j := by
  have sel (f : InstructionKey n → Bool) :=
    eval_selectedExpr slots reg choice f input p h c bit hs hr hb
  rcases j with q | ⟨t, i, s⟩
  · cases ha : windowInstruction p c bit with
    | none =>
      simp only [registerStepExpr, Expr.eval_mux, sel, ha, Option.any_none, Bool.false_eq_true,
        ite_false, windowStep, registerEncoding]
      exact fallbackState_eval input c bit _ _ (hr _) hb q
    | some a =>
      simp only [registerStepExpr, Expr.eval_mux, sel, ha, Option.any_some, ite_true, windowStep,
        windowAdvance, registerEncoding]
      simp [Fin.ext_iff, instructionKey]
  · cases ha : windowInstruction p c bit with
    | none =>
      rw [registerStepExpr, cellNext_eval_none _ _ _ _ _ _ _ (by simp [sel, ha]), hr]
      cases t <;> simp [windowStep, ha, registerEncoding]
    | some a =>
      cases t <;>
        simp only [registerStepExpr, windowStep, ha, windowAdvance, registerEncoding] <;>
        apply cellNext_eval_some <;> first
          | exact fun j b => hr _
          | intro k; rw [sel, ha]; rfl
          | simp only [sel, ha, Option.any_some]

/-- One step has quadratic formula size per register in the bound on the number of
states. Its cost is independent of the tape radius, since each destination uses at most
three neighboring cells. -/
theorem registerStepExpr_size_le (slots : Fin (9 * n) → Bool → InstructionKey n → Expr ι)
    (reg : WindowRegister n r → Expr ι) (choice : Expr ι) (C : ℕ)
    (hs : ∀ i b k, (slots i b k).size ≤ C) (hr : ∀ j, (reg j).size ≤ C)
    (hb : choice.size ≤ C) (j : WindowRegister n r) :
    (registerStepExpr slots reg choice j).size ≤ 500000 * (n + 2) ^ 2 * (C + 1) := by
  let B := 20000 * (n + 2) ^ 2 * (C + 1)
  have sel (f : InstructionKey n → Bool) : (selectedExpr slots reg choice f).size ≤ B :=
    size_selectedExpr slots reg choice f C hs hr hb
  have hbase : C + 1 ≤ (n + 2) ^ 2 * (C + 1) := by
    have hn : 0 < (n + 2) ^ 2 := by positivity
    simpa using Nat.mul_le_mul_right (C + 1) hn
  have hlarge : C ≤ B := by
    dsimp [B]
    rw [Nat.mul_assoc]
    omega
  rcases j with q | ⟨t, i, s⟩
  · have h₁ := sel fun _ => true
    have h₂ := sel fun k => decide (k.1 = q)
    have h₃ := hr (.inl ⟨1, by omega⟩)
    simp only [registerStepExpr, Expr.mux, fallbackState, Expr.size]
    dsimp [B] at h₁ h₂
    rw [Nat.mul_assoc] at h₁ h₂ ⊢
    omega
  · have hc := cellNext_size_le (fun j a => reg (.inr (t, j, a))) _ _ _ i s B
        (fun j a => (hr _).trans hlarge) (sel fun _ => true)
        (fun a => sel fun k => decide (keyWrite t k = a))
        (fun d => sel fun k => decide (keyMove t k = d))
    apply hc.trans
    dsimp [B]
    rw [Nat.mul_assoc, Nat.mul_assoc 500000]
    omega

end UniversalMachine

end VPVNP
end Computability
end OAI
