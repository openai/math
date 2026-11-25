import OAI.ThreeFlat.Diagonal.TracePairInputs
import OAI.ThreeFlat.Diagonal.TraceIssue

namespace OAI
/-! # Size of the circuit checking two packed RAM rows -/

namespace ThreeFlat.Diagonal.TracePair

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM TraceBanks TraceRows TraceWords TraceIssue
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

/-- The arithmetic network has cubic size. The remaining ports only parse
headers, compare words, or select the snapshot following a halt. -/
def portBudget (w : ℕ) := 216 * (w+1)^3 + 400 * (w+1)

theorem port_card (w p r : ℕ) :
    Fintype.card (Port w p r ⊕ Bool) = 3*p + 4*w + 2*r*w + p*w + 11 := by
  rw [Fintype.card_sum, ← Fintype.card_congr (Port.proxyTypeEquiv w p r)]
  have tags : Fintype.card Tag = 7 := by decide
  simp [Fintype.card_sigma, tags]
  ring

private theorem wordIs_size (side : Bool) (i : Fin 5) (v : Word (w+1)) :
    (wordIs (r:=r) side i v).size ≤ 10 * (w+1) + 1 := by
  apply (sameWord_size_le (headerWire (r:=r) side i) (fun j => .const (bits v j))
    (s:=1) (t:=1) (fun _ => le_rfl) (fun _ => le_rfl)).trans
  omega

private theorem next_size (e : Bool → Expr (Raw w r))
    (h : ∀ b, (e b).size ≤ 10*(w+1)+1) : (next e).size ≤ 100*(w+1) := by
  have h₁ := wordIs_size (w:=w) (r:=r) false 0 (Fin.ofNat _ (6 : Fin 8).val)
  have h₂ := wordIs_size (w:=w) (r:=r) false 0 (Fin.ofNat _ (7 : Fin 8).val)
  have hf := h false
  have ht := h true
  simp only [next, terminal, tagIs, Expr.mux, Expr.size]
  omega

private theorem smallPacket (e : Expr (Raw w r)) (h : e.size ≤ 100*(w+1)) :
    (formulaPacket e).1 ≤ portBudget w := by
  have size := formulaPacket_size_le e
  unfold portBudget
  omega

private theorem cmp_size (op : Instr w p r k) :
    (cmpExpr op).size ≤ 100*(w+1) := by
  cases op <;> simp only [cmpExpr, Expr.size]
  case jumpEq a b _ _ =>
    have h := sameWord_size_le (registerWire (w:=w) false a) (registerWire false b)
      (s:=1) (t:=1) (fun _ => le_rfl) (fun _ => le_rfl)
    omega
  case jumpLt a b _ _ =>
    have h := lessWord_size (registerWire (w:=w) false a) (registerWire false b)
      (s:=1) (fun _ => le_rfl) (fun _ => le_rfl)
    omega
  all_goals omega

private theorem aluPacket_size (pub : Fin k → Word w) (j : Fin w) (op : Instr w p r k) :
    (aluPacket pub j op).1 ≤ portBudget w := by
  cases op <;> simp only [aluPacket]
  case binary op _ _ _ _ =>
    exact (TraceBinaryOps.network_count op w).trans (Nat.le_add_right ..)
  all_goals
    apply smallPacket
    simp only [Expr.size]
    omega

theorem packet_size_le (M : Machine w p r k) (a : Port w p r ⊕ Bool) :
    (packet M a).1 ≤ portBudget w := by
  rcases a with a | side
  · cases a <;> simp only [packet]
    case alu i j => exact aluPacket_size M.publicData j (M.code i)
    all_goals apply smallPacket
    case cmp i => exact cmp_size (M.code i)
    case tag t => exact (wordIs_size ..).trans (by omega)
    case pc i => exact (wordIs_size ..).trans (by omega)
    case nextPC i => exact next_size _ (fun _ => wordIs_size ..)
    case nextReg i j =>
      apply next_size
      intro side
      simp only [registerWire, Expr.size]
      omega
    case nextState j =>
      apply next_size
      intro side
      simp only [headerWire, Expr.size]
      omega
    all_goals simp only [headerWire, registerWire, Expr.size]; omega
  · exact smallPacket _ ((wordIs_size ..).trans (by omega))

theorem checkPacket_size_le (M : Machine w p r k) :
    (formulaPacket (checkExpr M)).1 ≤ 4 * (p*(instructionBudget w r + 3) + 32) := by
  apply (formulaPacket_size_le _).trans
  apply Nat.mul_le_mul_left
  have h := issue_size_le M
  simp only [checkExpr, Expr.mux, Expr.size, same_size, Expr.size_rename]
  omega

/-- Polynomial gate count for the fully substituted circuit on two rows. -/
theorem pairCircuit_size_le (M : Machine w p r k) :
    (pairCircuit M).1 ≤
      (3*p + 4*w + 2*r*w + p*w + 11) * portBudget w +
        4 * (p*(instructionBudget w r + 3) + 32) := by
  rw [pairCircuit, TraceCompose.substituteFintype_size]
  refine Nat.add_le_add ?_ (checkPacket_size_le M)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => packet_size_le M a)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, port_card] using hs

end ThreeFlat.Diagonal.TracePair

end OAI
