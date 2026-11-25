import OAI.ThreeFlat.Diagonal.TracePairCorrect
import OAI.ThreeFlat.Diagonal.TracePairCost

namespace OAI
/-! # Sharing CPU flags and word results across all addressed register bits -/

noncomputable section
namespace Hierarchy.TaggedShorterCPURead
open ThreeFlat Diagonal TracePair TraceIssue TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open scoped Classical BigOperators

variable {w p r k : ℕ}

inductive Flag (p : ℕ)
  | pad (side : Bool)
  | tag (t : Tag)
  | pc (side : Bool) (i : Fin p)
  | cmp (i : Fin p)
  | isTerminal
  deriving DecidableEq, Fintype

def predicate (M : Machine w p r k) : Flag p → Expr (Raw w r)
  | .pad s => tagIs s 0
  | .tag t => tagIs false (tagNumber t)
  | .pc s i => pcIs s i
  | .cmp i => cmpExpr (M.code i)
  | .isTerminal => terminal

abbrev Pins (w p r : ℕ) := Raw w r ⊕ (Flag p ⊕ (Fin p × Fin w))

private def flag (f : Flag p) : Expr (Pins w p r) := .input (.inr (.inl f))
private def raw (s : Bool) (i : Fin (5+r)) (j : Fin (w+1)) : Expr (Pins w p r) :=
  .input (.inl (s,i,j))

private def select (e : Bool → Expr (Pins w p r)) : Expr (Pins w p r) :=
  Expr.mux (flag .isTerminal) (e false) (e true)

def localBit : Port w p r ⊕ Bool → Expr (Pins w p r)
  | .inr s => flag (.pad s)
  | .inl (.tag t) => flag (.tag t)
  | .inl (.pc i) => flag (.pc false i)
  | .inl (.nextPC i) => select (fun s => flag (.pc s i))
  | .inl (.cmp i) => flag (.cmp i)
  | .inl (.alu i j) => .input (.inr (.inr (i,j)))
  | .inl (.reg i j) => raw false (Fin.natAdd 5 i) j.castSucc
  | .inl (.nextReg i j) => select (fun s => raw s (Fin.natAdd 5 i) j.castSucc)
  | .inl (.state j) => raw false ((2 : Fin 5).castAdd r) j.castSucc
  | .inl (.nextState j) => select (fun s => raw s ((2 : Fin 5).castAdd r) j.castSucc)
  | .inl (.address j) => raw false ((3 : Fin 5).castAdd r) j
  | .inl (.data j) => raw false ((4 : Fin 5).castAdd r) j

def assigned (M : Machine w p r k) (x : Raw w r → Bool) : Pins w p r → Bool :=
  Sum.elim x (Sum.elim (fun f => (predicate M f).eval x)
    (fun b => ((aluPacket M.publicData b.2 (M.code b.1)).2.eval x)))

theorem bit_eval (M : Machine w p r k) (x : Raw w r → Bool) (s : Port w p r ⊕ Bool) :
    (localBit s).eval (assigned M x) = (packet M s).2.eval x := by
  cases s with
  | inr b => simp [localBit,assigned,predicate,flag,packet,formulaPacket_eval,Expr.eval]
  | inl s =>
    cases s <;> simp [localBit,assigned,predicate,raw,flag,select,packet,next,registerWire,
      headerWire,Expr.eval_mux,formulaPacket_eval,Expr.eval]
    all_goals by_cases ht : (terminal (w:=w) (r:=r)).eval x = true <;> simp [ht]

def residual (M : Machine w p r k) : TraceCompose.Packet (Pins w p r) :=
  TraceCompose.substituteFintype (fun i => formulaPacket (localBit i)) (formulaPacket (checkExpr M)).2

theorem residual_eval (M : Machine w p r k) (x : Raw w r → Bool) :
    (residual M).2.eval (assigned M x)=(pairCircuit M).2.eval x := by
  simp only [residual,TraceCompose.substituteFintype_eval,formulaPacket_eval,pairCircuit_eval,bit_eval]

private theorem local_size (i : Port w p r ⊕ Bool) : (localBit i).size≤20 := by
  cases i with
  | inr b => simp [localBit,flag,Expr.size]
  | inl i => cases i <;> simp [localBit,select,flag,raw,Expr.size,Expr.mux]

theorem residual_size (M : Machine w p r k) :
    (residual M).1 ≤ 80*(3*p+4*w+2*r*w+p*w+11) +
      4*(p*(instructionBudget w r+3)+32) := by
  rw [residual,TraceCompose.substituteFintype_size]
  apply Nat.add_le_add _ (checkPacket_size_le M)
  have bound (i : Port w p r ⊕ Bool) : (formulaPacket (localBit i)).1≤80 :=
    (formulaPacket_size_le _).trans (Nat.mul_le_mul_left 4 (local_size i))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,port_card,Nat.cast_id,Nat.mul_comm]
    using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => bound i)

/-- Only constantly many flags per program counter have word-length
formulas. A flag used by all register columns is certified only once. -/
theorem predicate_size (M : Machine w p r k) (f : Flag p) : (predicate M f).size≤100*(w+1) := by
  have word (side : Bool) (i : Fin 5) (v : Word (w+1)) : (wordIs (r:=r) side i v).size ≤ 10*(w+1)+1 :=
    (sameWord_size_le _ _ (s:=1) (t:=1) (fun _ => le_rfl) (fun _ => le_rfl)).trans (by omega)
  cases f with
  | pad s => exact (word ..).trans (by omega)
  | tag t => exact (word ..).trans (by omega)
  | pc s i => exact (word ..).trans (by omega)
  | isTerminal =>
    have a := word false 0 (Fin.ofNat _ (6:Fin 8).val)
    have b := word false 0 (Fin.ofNat _ (7:Fin 8).val)
    simp only [predicate,terminal,tagIs,Expr.size]
    omega
  | cmp i =>
    cases hi : M.code i <;> simp only [predicate,hi,cmpExpr,Expr.size]
    case jumpEq a b yes no =>
      exact (sameWord_size_le (registerWire false a) (registerWire false b)
        (s:=1) (t:=1) (fun _=>le_rfl) (fun _=>le_rfl)).trans (by omega)
    case jumpLt a b yes no =>
      exact (lessWord_size (registerWire false a) (registerWire false b)
        (s:=1) (fun _=>le_rfl) (fun _=>le_rfl)).trans (by omega)
    all_goals omega

end Hierarchy.TaggedShorterCPURead

end
end OAI
