import OAI.Computability.BorderVNP.PackedSubdivisionGateRows
import OAI.Computability.BorderVNP.PackedInheritedLayerEmit
import OAI.Computability.BorderVNP.PackedInheritedEndpointViews

/-! # Sparse final incidence bindings from the physical cell and site directories

The site prefix lookup reads the output of the same cell allocation scan that
provides the wire and port starts. Each live endpoint has one fixed record
slot, independently of the number of lanes in its word. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing CellAddressCircuit PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame

/-- Endpoint candidates, with the exterior ports following both sides of each cable. -/
abbrev Row (m np : ℕ) := Subdivision.Gates.Old m np

/-- Shared virtual starts, physical starts, and looked-up private work widths. -/
abbrev Front (σ : Type*) (s m np C w : ℕ) :=
  σ ⊕ ((CellAddressViews.View s m np s × Fin w) ⊕
    ((CellAddressViews.View s m np C × Fin w) ⊕ (End m np × Fin w)))

/-- The shared geometry and the physical site prefix selected by each endpoint. -/
abbrev Pins (σ : Type*) (s m np C w : ℕ) := Front σ s m np C w ⊕ (End m np × Fin w)

variable {s m np C d k w : ℕ} {σ : Type*} [Fintype σ]
    (F : Fields s m np C d k w σ) (work : Fin s → Fin w → σ)

/-- The two allocation scans and the endpoint lookup of the private work width. -/
noncomputable def front : Frame σ (Front σ s m np C w) :=
  (parallelFrame (Views.frame F) (parallelFrame (CellAddressViews.frame F) (Layer.prefixFrame F work))).withInput

/-- Read each endpoint's site prefix from the physical allocation scan. -/
noncomputable def sitePrefixes : Frame (Front σ s m np C w) (End m np × Fin w) :=
  PackedLookup.lookup (layout (Fin s) (End m np)) F.sites
    (fun v j => .input (.inr (.inr (.inl (.inr (.inl v),j))))) (fun u j => .input (.inl (F.ptr u j)))

/-- Raw and computed pins consumed by the row selector. -/
noncomputable def pins : Frame σ (Pins σ s m np C w) := (sitePrefixes F).withInput.subst (front F work)

variable (occupied : Fin m → σ) (portUsed : Fin np → Bool)

private def ptr (u : End m np) (j : Fin d) : Expr (Pins σ s m np C w) := .input (.inl (.inl (F.ptr u j)))

private def different (i : Fin m) : Expr (Pins σ s m np C w) :=
  .not (eqWord (ptr F (Layer.edgeEnd i true)) (ptr F (Layer.edgeEnd i false)))

private def active : Row m np → Expr (Pins σ s m np C w)
  | .inl (i,true) => .input (.inl (.inl (occupied i)))
  | .inl (i,false) => .and (.input (.inl (.inl (occupied i)))) (different F i)
  | .inr p => .const (portUsed p)

/-- Source wires of the nine scalar field expressions. The cell prefix belongs
to the staged site side only. The canonical endpoint already has a cell address. -/
private def operand (r : Row m np) (j : Fin w) : Layer.Arg → Expr (Pins σ s m np C w)
  | .work => .input (.inr (Subdivision.Gates.oldEnd r,j))
  | .oldBase => .input (.inl (.inr (.inr (.inr (Subdivision.Gates.oldEnd r,j)))))
  | .clip => .input (.inl (.inr (.inl (.inl (Subdivision.Gates.oldEnd r),j))))
  | .extent => .const false
  | .newBase => .input (.inl (.inr (.inr (.inl (.inl (Subdivision.Gates.oldEnd r),j)))))
  | .width => .input (.inl (.inl (r.elim (fun t => F.edgeWidth t.1 j) (fun p => F.portWidth p j))))

private def select : Row m np × Layer.Column d w → Expr (Pins σ s m np C w)
  | (r,.inl ()) => active F occupied portUsed r
  | (r,.inr (.inl j)) => ptr F (Subdivision.Gates.oldEnd r) j
  | (r,.inr (.inr (a,j))) => operand F r j a

/-- Fixed final binding rows on the raw geometry, including actual live zero-width words. -/
noncomputable def inputs : Frame σ (Row m np × Layer.Column d w) :=
  (pins F work).step (select F occupied portUsed)

/-- Number of gates charged to the row selectors after computing both scans and lookups. -/
theorem inputs_size : (inputs F work occupied portUsed).size ≤
    (Views.frame F).size+((CellAddressViews.frame F).size+(Layer.prefixFrame F work).size)+
      (sitePrefixes F).size + (2*m+np)*(1+d+6*w)*(30*d+8) := by
  have hd (i : Fin m) : (different F i).size ≤ 30*d+4 := by
    have h := eqWord_size (ptr F (Layer.edgeEnd i true)) (ptr F (Layer.edgeEnd i false))
      (fun _ => le_rfl) (fun _ => le_rfl)
    simp only [different,StatementCircuit.Expr.size]; omega
  have hs (a : Row m np × Layer.Column d w) : (select F occupied portUsed a).size ≤ 30*d+8 := by
    rcases a with ⟨⟨i,side⟩ | p,c⟩
    all_goals rcases c with u | j | ⟨a,j⟩
    all_goals try cases u
    all_goals first | cases side <;> cases a | cases side | cases a | skip
    all_goals simp only [select,active,operand,ptr,StatementCircuit.Expr.size]
    all_goals first | omega | have h := hd i; omega
  have h := Frame.step_size_le (pins F work) (select F occupied portUsed) (30*d+8) hs
  have ha : Fintype.card Layer.Arg = 6 := by decide
  simp only [inputs,pins,Frame.subst_size,Frame.withInput_size,front,parallelFrame_size,Row,
    Subdivision.Gates.Old,Layer.Column,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,
    Fintype.card_bool,Fintype.card_unit,ha] at *
  simpa only [Nat.mul_comm m 2,Nat.add_assoc] using h

/-- The native enable test uses the true live flag and suppresses only a second endpoint of a loop. -/
theorem input_flag (x : σ → Bool) (r : Row m np) :
    (inputs F work occupied portUsed).eval x (r,.inl ()) = true ↔
    r.elim (fun p => x (occupied p.1) = true ∧ (p.2 = true ∨
      value (x ∘ F.ptr (Layer.edgeEnd p.1 true)) ≠ value (x ∘ F.ptr (Layer.edgeEnd p.1 false))))
      (fun p => portUsed p = true) := by
  have diff (i : Fin m) : (different F i).eval ((pins F work).eval x) = true ↔
      value (x ∘ F.ptr (Layer.edgeEnd i true)) ≠ value (x ∘ F.ptr (Layer.edgeEnd i false)) := by
    simp only [different,StatementCircuit.Expr.eval,Bool.not_eq_true',Bool.eq_false_iff,ne_eq]
    apply not_congr
    rw [eqWord_eval]; simp [wordValue,ptr,pins,front,StatementCircuit.Expr.eval,Function.comp_def]
  rcases r with ⟨i,side⟩ | p
  · have read : (pins F work).eval x (.inl (.inl (occupied i))) = x (occupied i) := by simp [pins,front]
    cases side <;> simp [inputs,select,active,StatementCircuit.Expr.eval,diff,read]
  · simp [inputs,select,active,StatementCircuit.Expr.eval]

/-- The owner field is the actual site pointer, retained for stable site-major ordering. -/
theorem input_owner (x : σ → Bool) (r : Row m np) :
    value (fun j => (inputs F work occupied portUsed).eval x (r,.inr (.inl j))) =
      value (x ∘ F.ptr (Subdivision.Gates.oldEnd r)) := by
  simp [inputs,select,ptr,pins,front,StatementCircuit.Expr.eval,Function.comp_def]

/-- Scalar operands before the final address additions. -/
noncomputable def args (x : σ → Bool) (r : Row m np) (a : Layer.Arg) : ℕ :=
  value (fun j => (inputs F work occupied portUsed).eval x (r,.inr (.inr (a,j))))

/-- The computed site prefix at a real endpoint reads the same physical scan as its canonical word. -/
theorem stage_read (x : σ → Bool) (r : Row m np) (v : Fin s)
    (hv : value (x ∘ F.ptr (Subdivision.Gates.oldEnd r)) = (F.sites v).val) :
    args F work occupied portUsed x r .work =
      value (fun j => (CellAddressViews.frame F).eval x (.inr (.inl v),j)) := by
  let u := Subdivision.Gates.oldEnd r
  have h := PackedLookup.lookup_value (layout (Fin s) (End m np)) F.sites
    (fun (v : Fin s) (j : Fin w) => StatementCircuit.Expr.input (.inr (.inr (.inl (.inr (.inl v),j)))))
    (fun u j => .input (.inl (F.ptr u j))) ((front F work).eval x) (Subdivision.Gates.oldEnd r) v
  have hp : wordValue ((front F work).eval x) (fun j => .input (.inl (F.ptr u j))) = (F.sites v).val := by
    simpa [front,wordValue,StatementCircuit.Expr.eval,Function.comp_def,u] using hv
  simpa only [args,inputs,Frame.step_eval,select,operand,StatementCircuit.Expr.eval,pins,Frame.subst_eval,
    Frame.withInput_eval_inr,sitePrefixes,wordValue,front,parallelFrame_eval_inr,parallelFrame_eval_inl] using h hp

/-- Reading the five remaining inputs uses the work lookup and the two shared
scans. No per-lane circuit appears in this row. -/
theorem other_reads (x : σ → Bool) (r : Row m np) :
    let a := args F work occupied portUsed x r
    let u := Subdivision.Gates.oldEnd r
    a .oldBase = value (fun j => (Layer.prefixFrame F work).eval x (u,j)) ∧
    a .clip = value (fun j => (Views.frame F).eval x (.inl u,j)) ∧
    a .extent = 0 ∧
    a .newBase = value (fun j => (CellAddressViews.frame F).eval x (.inl u,j)) ∧
    a .width = value (fun j => x (r.elim (fun t => F.edgeWidth t.1 j) (fun p => F.portWidth p j))) := by
  simp only [args,inputs,select,operand,pins,front,Frame.step_eval,Frame.subst_eval,
    StatementCircuit.Expr.eval,Frame.withInput_eval_inl,Frame.withInput_eval_inr,parallelFrame_eval_inl,
    parallelFrame_eval_inr,zero_value,true_and]

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
