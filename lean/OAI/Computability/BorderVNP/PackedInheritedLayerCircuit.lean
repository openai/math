import OAI.Computability.BorderVNP.PackedInheritedRowNames
import OAI.Computability.BorderVNP.PackedInheritedAddress
import OAI.Computability.BorderVNP.PackedInheritedWordCircuit
import OAI.Computability.BorderVNP.ShortenStaticRowHoles
import OAI.Computability.BorderVNP.PackedLiveCuts

/-! # Public source fields of every inherited equality row

Two static successor hook candidates and the retained candidate are available
at known slots. The live hook flag chooses which address to read. The old
source and destination pointer comparison suppresses the second row of a loop.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows CellAddressCircuit
open VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame
open scoped Classical

/-- Six numeric operands needed by an inherited equality command. -/
inductive Arg where | work | extent | oldBase | clip | newBase | width
  deriving DecidableEq

instance : Fintype Arg := ⟨{.work,.extent,.oldBase,.clip,.newBase,.width},by intro x; cases x <;> simp⟩

/-- A public row carries its enable bit, the owning site pointer, and six scalar operands. -/
abbrev Column (d w : ℕ) := Unit ⊕ (Fin d ⊕ (Arg × Fin w))

variable {D m old np seeds d w : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Pointers to the actual preceding and successor sparse circuit fields. -/
structure Fields (σ : Type*) where
  /-- Presence of an old cable row, including live cables of width zero. -/
  occupied : Fin old → σ
  /-- Static occupancy of the exterior argument directory. -/
  portUsed : Fin np → Bool
  /-- Presence of each sewn successor row. -/
  successor : Fin (edgeCapacity e old seeds) → σ
  /-- Old source, destination and attachment names. -/
  pointer : End old np → Fin d → σ
  /-- Old canonical incidence starts, from the singleton-cell view pass. -/
  oldView : End old np → Fin w → σ
  /-- New canonical incidence starts, from the successor view pass. -/
  newView : End (edgeCapacity e old seeds) np → Fin w → σ
  /-- Actual clipped old starts and spans from the band cutting circuit. -/
  cut : Fin old × Band D → CutCircuit.Result → Fin w → σ
  /-- Current exterior word widths, unchanged by the cut pass. -/
  portWidth : Fin np → Fin w → σ
  /-- Lookup of the owning site's old private work prefix. -/
  work : End old np → Fin w → σ
  /-- Lookup of the owning site's full old extent (work plus old incoming). -/
  extent : End old np → Fin w → σ

/-- Select source or destination of an old endpoint row. -/
def edgeEnd {M n : ℕ} (r : Fin M) (side : Bool) : End M n :=
  .inl (if side then .inl r else .inr r)

/-- The endpoint supplying a public row's pointer and old local address. -/
def endpoint : Row old D np → End old np
  | .inl ((r,_),side) => edgeEnd r side
  | .inr p => .inr p

variable {σ : Type*} [Fintype σ] (F : Fields (old := old) (np := np) (seeds := seeds) (d := d) (w := w) e σ)

private def chosen (r : Fin old) (b : Band D) : Expr σ :=
  .input (F.successor (bandCandidate e seeds 0 r b))

private def distinctEnds (r : Fin old) : Expr σ :=
  .not (eqWord (fun j => .input (F.pointer (.inl (.inl r)) j)) (fun j => .input (F.pointer (.inl (.inr r)) j)))

private def enabled : Row old D np → Expr σ
  | .inr p => .const (F.portUsed p)
  | .inl ((r,_),true) => .input (F.occupied r)
  | .inl ((r,_),false) => .and (.input (F.occupied r)) (distinctEnds e F r)

private def next (r : Fin old) (b : Band D) (side : Bool) (j : Fin w) : Expr σ :=
  mux (chosen e F r b) (.input (F.newView (edgeEnd (bandCandidate e seeds (if side then 0 else 1) r b) true) j))
    (.input (F.newView (edgeEnd (bandCandidate e seeds 2 r b) side) j))

private def operand (row : Row old D np) (j : Fin w) : Arg → Expr σ
  | .work => .input (F.work (endpoint row) j)
  | .extent => .input (F.extent (endpoint row) j)
  | .oldBase => .input (F.oldView (endpoint row) j)
  | .clip => row.elim (fun u => .input (F.cut u.1 .start j)) (fun _ => .const false)
  | .newBase => row.elim (fun u => next e F u.1.1 u.1.2 u.2 j) (fun p => .input (F.newView (.inr p) j))
  | .width => row.elim (fun u => .input (F.cut u.1 .span j)) (fun p => .input (F.portWidth p j))

private def expression : Row old D np × Column d w → Expr σ
  | (r,.inl ()) => enabled e F r
  | (r,.inr (.inl j)) => .input (F.pointer (endpoint r) j)
  | (r,.inr (.inr (a,j))) => operand e F r j a

/-- A single fixed sparse pass supplying the fields of every possible old endpoint/port tie. -/
noncomputable def source : Frame σ (Row old D np × Column d w) := (Frame.initial id).step (expression e F)

/-- Gate bound of the source/retained mux pass, allowing arbitrary endpoint and width word sizes. -/
theorem source_size : (source e F).size ≤ Fintype.card (Row old D np) * (1+d+6*w)*(30*d+16) := by
  have he (r : Fin old) : (distinctEnds e F r).size ≤ 30*d+4 := by
    have h := eqWord_size (fun j => (StatementCircuit.Expr.input (F.pointer (.inl (.inl r)) j)))
      (fun j => (StatementCircuit.Expr.input (F.pointer (.inl (.inr r)) j))) (fun _ => le_rfl) (fun _ => le_rfl)
    simp only [distinctEnds,StatementCircuit.Expr.size]
    omega
  have bound (i : Row old D np × Column d w) : (expression e F i).size ≤ 30*d+16 := by
    rcases i with ⟨row,col⟩
    rcases row with ⟨⟨r,b⟩,side⟩ | p
    all_goals rcases col with u | j | ⟨a,j⟩
    all_goals try cases u
    all_goals first | cases side <;> cases a | cases side | cases a | skip
    all_goals simp only [expression,enabled,operand,Sum.elim_inl,Sum.elim_inr,next,
      mux,chosen,StatementCircuit.Expr.size]
    all_goals first | omega | exact (by have := he r; omega)
  have h := Frame.step_size_le (Frame.initial (id : σ → σ)) (expression e F) (30*d+16) bound
  have hA : Fintype.card Arg = 6 := by decide
  simpa [source,Fintype.card_prod,Fintype.card_sum,hA,Nat.add_assoc] using h

/-- The source flag reads old row presence and suppresses precisely the duplicated destination of a loop. -/
theorem source_live (x : σ → Bool) (r : Fin old) (b : Band D) (side : Bool) :
    (source e F).eval x (.inl ((r,b),side),.inl ()) = true ↔ x (F.occupied r) = true ∧
    (side = true ∨ value (x ∘ F.pointer (.inl (.inl r))) ≠ value (x ∘ F.pointer (.inl (.inr r)))) := by
  cases side
  · simp only [source,Frame.step_eval,expression,enabled,distinctEnds,StatementCircuit.Expr.eval,
      Bool.and_eq_true,Bool.not_eq_true',Bool.false_eq_true,false_or]
    have h := eqWord_eval (fun j => StatementCircuit.Expr.input (F.pointer (.inl (.inl r)) j))
      (fun j => StatementCircuit.Expr.input (F.pointer (.inl (.inr r)) j)) ((Frame.initial id).eval x)
    simp only [wordValue,StatementCircuit.Expr.eval,Frame.initial_eval,id_eq] at *
    rw [Bool.eq_false_iff]
    exact and_congr_right' (not_congr h)
  · simp [source,expression,enabled,StatementCircuit.Expr.eval]

/-- Exterior row presence comes directly from the fixed argument layout. -/
theorem source_port_live (x : σ → Bool) (p : Fin np) :
    (source e F).eval x (.inr p,.inl ()) = F.portUsed p := by
  simp [source,expression,enabled,StatementCircuit.Expr.eval]

/-- The stored owner is the actual pointer of this endpoint or argument. -/
theorem source_owner (x : σ → Bool) (r : Row old D np) (j : Fin d) :
    (source e F).eval x (r,.inr (.inl j)) = x (F.pointer (endpoint r) j) := by
  simp [source,expression,StatementCircuit.Expr.eval]

/-- Values selected from the previously computed old and new physical directory columns. -/
def argValue (x : σ → Bool) (row : Row old D np) : Arg → ℕ
  | .work => value (x ∘ F.work (endpoint row))
  | .extent => value (x ∘ F.extent (endpoint row))
  | .oldBase => value (x ∘ F.oldView (endpoint row))
  | .clip => row.elim (fun u => value (x ∘ F.cut u.1 .start)) (fun _ => 0)
  | .newBase => row.elim (fun u =>
      if x (F.successor (bandCandidate e seeds 0 u.1.1 u.1.2)) then
        value (x ∘ F.newView (edgeEnd (bandCandidate e seeds (if u.2 then 0 else 1) u.1.1 u.1.2) true))
      else value (x ∘ F.newView (edgeEnd (bandCandidate e seeds 2 u.1.1 u.1.2) u.2)))
    (fun p => value (x ∘ F.newView (.inr p)))
  | .width => row.elim (fun u => value (x ∘ F.cut u.1 .span)) (fun p => value (x ∘ F.portWidth p))

open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit

/-- Each returned field has its prescribed scalar value on every actual assignment. -/
theorem source_value (x : σ → Bool) (row : Row old D np) (a : Arg) :
    value (fun j => (source e F).eval x (row,.inr (.inr (a,j)))) = argValue e F x row a := by
  cases row with
  | inl u =>
    cases hx : x (F.successor (bandCandidate e seeds 0 u.1.1 u.1.2)) <;> cases a <;>
      simp [source,expression,operand,argValue,chosen,next,mux_eval,StatementCircuit.Expr.eval,hx,Function.comp_def]
  | inr p => cases a <;>
      simp [source,expression,operand,argValue,StatementCircuit.Expr.eval,Function.comp_def,zero_value]

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
