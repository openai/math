import OAI.ThreeFlat.RAM.TickTerminalPrimitive

namespace OAI
/-! # Register count after mounting the true operand reader -/

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

private def substitutedOpCost {w k n : ℕ} : Op w k n → ℕ
  | .parameter _ => 2
  | _ => 1

private def substitutedCost {w k : ℕ} : {n : ℕ} → Term w k n → ℕ
  | _, .result _ => 0
  | _, .bind op body => substitutedCost body + substitutedOpCost op

private theorem sub_rename {w k n s : ℕ} (e : Term w k n) (f : Fin n → Fin s) :
    substitutedCost (e.rename f) = substitutedCost e := by
  induction e generalizing s with
  | result _ => rfl
  | bind op body ih =>
    cases op <;> simp only [Term.rename,Op.rename,substitutedCost,ih,substitutedOpCost]

private theorem sub_then {w k n : ℕ} (e : Term w k n) (body : Term w k (n+1)) :
    substitutedCost (e.letThen body) = substitutedCost e + substitutedCost body := by
  induction e with
  | result i => simp [Term.letThen,substitutedCost,sub_rename]
  | bind op tail ih =>
    simp only [Term.letThen,substitutedCost,ih,sub_rename]
    omega

private theorem sub_binds {w k n : ℕ} (e : Term w k n) :
    (HistoryCommandParameter.replace (fun _ : Fin k =>
      ((Term.parameter (0 : Fin 1)).load : Term w 1 0)) e).binds = substitutedCost e := by
  induction e with
  | result _ => rfl
  | bind op tail ih =>
    cases op <;> simp only [HistoryCommandParameter.replace,Term.binds,Term.binds_letThen,
      Term.binds_rename,ih,substitutedCost,substitutedOpCost]
    change 2 + substitutedCost tail = substitutedCost tail + 2
    omega

private theorem sub_literal {w k n : ℕ} (x : Word w) :
    substitutedCost (Term.literal x : Term w k n) = 1 := rfl

private theorem sub_load {w k n : ℕ} (x : Term w k n) :
    substitutedCost x.load = substitutedCost x + 1 := by
  simp [Term.load,sub_then,substitutedCost,substitutedOpCost]

private theorem sub_binary {w k n : ℕ} (op : BinaryOp) (x y : Term w k n) :
    substitutedCost (Term.binary op x y) = substitutedCost x + substitutedCost y + 1 := by
  simp [Term.binary,sub_then,sub_rename,substitutedCost,substitutedOpCost,Nat.add_assoc]

private theorem sub_select {w k n : ℕ} (cmp : Comparison) (x y yes no : Term w k n) :
    substitutedCost (Term.select cmp x y yes no) =
      substitutedCost x + substitutedCost y + substitutedCost yes + substitutedCost no + 1 := by
  simp [Term.select,sub_then,sub_rename,substitutedCost,substitutedOpCost,Nat.add_assoc]

private theorem join_uniform (W : ℕ) :
    (HistoryCommandParameter.replace (fun _ : Fin 1 =>
      ((Term.parameter (0 : Fin 1)).load : Term W 1 0)) (HistoryJoinScan.term (0 : Fin 1))).binds =
    (HistoryCommandParameter.replace (fun _ : Fin 1 =>
      ((Term.parameter (0 : Fin 1)).load : Term 1 1 0)) (HistoryJoinScan.term (0 : Fin 1))).binds := by
  refine (sub_binds (w:=W) (HistoryJoinScan.term (0 : Fin 1))).trans
    (Eq.trans ?_ (sub_binds (w:=1) (HistoryJoinScan.term (0 : Fin 1))).symm)
  simp only [HistoryJoinScan.term,sub_select,sub_binary,sub_load,sub_literal]; rfl

private theorem selectBinds {w k n : ℕ} (cmp : Comparison) (x y yes no : Term w k n) :
    (Term.select cmp x y yes no).binds = x.binds + y.binds + yes.binds + no.binds + 1 := by
  simp [Term.select,Term.binds_letThen,Term.binds_rename,Term.binds,Nat.add_assoc]

private theorem select_cost_eq {w W k n : ℕ} {x y yes no : Term w k n}
    {x' y' yes' no' : Term W k n} {cmp : Comparison}
    (h₁ : x.binds=x'.binds) (h₂ : y.binds=y'.binds) (h₃ : yes.binds=yes'.binds)
    (h₄ : no.binds=no'.binds) :
    (Term.select cmp x y yes no).binds=(Term.select cmp x' y' yes' no').binds := by
  rw [selectBinds,selectBinds,h₁,h₂,h₃,h₄]

open TickTerminalPrimitive
open private cmd rd source from OAI.ThreeFlat.RAM.TickTerminalPrimitive

private theorem endpoint_size (w : ℕ) : (source (w:=w)).binds=14 := by
  simp only [source,rd,cmd,Term.binary,Term.load,Term.literal,Term.parameter,Term.binds_letThen,
    Term.binds_rename,Term.binds]

private theorem loaded_endpoint_size (w : ℕ) : (source (w:=w)).load.binds=15 := by
  simp only [Term.load,Term.binds_letThen,endpoint_size,Term.binds]

/-- The native join, endpoint and wire opcodes use the same number of registers at every word width. -/
theorem expression_uniform (W : ℕ) :
    (TickTerminalPrimitive.expression W).binds = (TickTerminalPrimitive.expression 1).binds := by
  unfold TickTerminalPrimitive.expression
  apply select_cost_eq
  · rfl
  · rfl
  · exact join_uniform W
  · apply select_cost_eq
    · rfl
    · rfl
    · exact (loaded_endpoint_size W).trans (loaded_endpoint_size 1).symm
    · exact (endpoint_size W).trans (endpoint_size 1).symm


end ThreeFlat.RAM.TickTerminalRoot

end OAI
