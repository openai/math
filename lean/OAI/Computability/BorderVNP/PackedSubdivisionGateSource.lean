import OAI.Computability.BorderVNP.PackedSubdivisionGateRows
import OAI.Computability.BorderVNP.PackedInheritedLayerEmit

/-! # Boolean source operands for the actual sparse subdivision commands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit

/-- Physical widths, endpoint pointers, live flags and retained work-prefix lookups. -/
structure Fields (m np extra d d' w : ℕ) (σ : Type*) where
  /-- Cable widths, with zero in every unoccupied slot. -/
  edgeWidth : Fin m → Fin w → σ
  /-- Exterior widths, with zero in every unoccupied slot. -/
  portWidth : Fin np → Fin w → σ
  /-- Old endpoint owners, used to suppress the second record of a loop. -/
  oldPtr : End m np → Fin d → σ
  /-- Successor endpoint owners in the new site directory. -/
  newPtr : End ((extra+1)*m) np → Fin d' → σ
  /-- Actual old incidence starts, including the loop prefix. -/
  oldView : End m np → Fin w → σ
  /-- Actual new incidence starts. -/
  newView : End ((extra+1)*m) np → Fin w → σ
  /-- Live successor cable rows, including zero-width cables. -/
  present : Fin ((extra+1)*m) → σ
  /-- Work prefix returned by batched lookup on the old endpoint's site. -/
  work : End m np → Fin w → σ
  /-- Full old site extent returned by the same lookup. -/
  extent : End m np → Fin w → σ

variable {m np extra d d' w : ℕ} {σ : Type*} [Fintype σ] (F : Fields m np extra d d' w σ)

/-- Width wires of the old argument supplied by one retained candidate. -/
def widthPins : Old m np → Fin w → σ := Sum.elim (F.edgeWidth ∘ Prod.fst) F.portWidth

private def positive (r : Old m np) : Expr σ :=
  .not (eqWord (fun j => .input (widthPins F r j)) (fun _ => .const false))

private def distinct (i : Fin m) : Expr σ := .not (eqWord
  (fun j => .input (F.oldPtr (Layer.edgeEnd i true) j))
  (fun j => .input (F.oldPtr (Layer.edgeEnd i false) j)))

private def enable : Row m np extra → Expr σ
  | .inl (.inl (i,false)) => .and (positive F (.inl (i,false))) (distinct F i)
  | .inl r => positive F r
  | .inr (e,j) => .input (F.present (hop e j.succ))

/-- The old cable's actual last reserved hop exists on a long route. -/
def long (x : σ → Bool) : Old m np → Bool
  | .inl (i,_) => x (F.present (hop i (Fin.last extra)))
  | .inr _ => false

private def fetch {b : ℕ} (pins : End ((extra+1)*m) np → Fin b → σ)
    (r : Old m np) (j : Fin b) : Expr σ :=
  match r with
  | .inl (i,false) => mux (.input (F.present (hop i (Fin.last extra))))
      (.input (pins (oldTarget (.inl (i,false)) true) j)) (.input (pins (oldTarget (.inl (i,false)) false) j))
  | _ => .input (pins (oldTarget r false) j)

omit [Fintype σ] in
private theorem fetch_eval {b : ℕ} (pins : End ((extra+1)*m) np → Fin b → σ)
    (r : Old m np) (j : Fin b) (x : σ → Bool) :
    (fetch F pins r j).eval x = x (pins (oldTarget r (long F x r)) j) := by
  rcases r with ⟨i,side⟩ | p
  · cases side <;> cases h : x (F.present (hop i (Fin.last extra))) <;>
      simp [fetch,long,oldTarget,mux_eval,StatementCircuit.Expr.eval,h]
  · rfl

private def args (row : Row m np extra) (j : Fin w) : Layer.Arg → Expr σ :=
  match row with
  | .inl r => fun
    | .work => .input (F.work (oldEnd r) j)
    | .extent => .input (F.extent (oldEnd r) j)
    | .clip => .const false
    | .oldBase => .input (F.oldView (oldEnd r) j)
    | .newBase => fetch F F.newView r j
    | .width => .input (widthPins F r j)
  | .inr (e,k) => fun
    | .work | .extent | .clip => .const false
    | .oldBase => .input (F.newView (relayLeft e k) j)
    | .newBase => .input (F.newView (relayRight e k) j)
    | .width => .input (F.edgeWidth e j)

private def expr : Row m np extra × Layer.Column d' w → Expr σ
  | (r,.inl ()) => enable F r
  | (.inl r,.inr (.inl j)) => fetch F F.newPtr r j
  | (.inr (e,k),.inr (.inl j)) => .input (F.newPtr (relayLeft e k) j)
  | (r,.inr (.inr (a,j))) => args F r j a

/-- One sparse endpoint/relay operand row for each public rectangle position. -/
noncomputable def source : Frame σ (Row m np extra × Layer.Column d' w) := (Frame.initial id).step (expr F)

/-- The fixed rowwise selectors and width tests have linear word cost per output pin. -/
theorem source_size : (source F).size ≤
    Fintype.card (Row m np extra)*(1+d'+6*w)*(30*(d+w)+18) := by
  have hp (r : Old m np) : (positive F r).size ≤ 30*w+4 := by
    have h := eqWord_size (fun j => StatementCircuit.Expr.input (widthPins F r j))
      (fun _ => .const false) (fun _ => le_rfl) (fun _ => le_rfl)
    simp only [positive,StatementCircuit.Expr.size]; omega
  have hd (i : Fin m) : (distinct F i).size ≤ 30*d+4 := by
    have h := eqWord_size (fun j => StatementCircuit.Expr.input (F.oldPtr (Layer.edgeEnd i true) j))
      (fun j => .input (F.oldPtr (Layer.edgeEnd i false) j)) (fun _ => le_rfl) (fun _ => le_rfl)
    simp only [distinct,StatementCircuit.Expr.size]; omega
  have bound (i : Row m np extra × Layer.Column d' w) : (expr F i).size ≤ 30*(d+w)+18 := by
    rcases i with ⟨(⟨e,side⟩ | p) | ⟨e,k⟩,c⟩
    all_goals rcases c with u | j | ⟨a,j⟩
    all_goals try cases u
    all_goals first | cases side <;> cases a | cases side | cases a | skip
    all_goals simp only [expr,enable,args,fetch,mux,StatementCircuit.Expr.size]
    all_goals try (have hf := hp (.inl (e,false)); have ht := hp (.inl (e,true)); have he := hd e; omega)
    all_goals try (have hh := hp (.inr p); omega)
  have h := Frame.step_size_le (Frame.initial (id : σ → σ)) (expr F) (30*(d+w)+18) bound
  have ha : Fintype.card Layer.Arg = 6 := by decide
  simpa only [source,Frame.initial_size,Nat.zero_add,Layer.Column,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_unit,Fintype.card_fin,ha,Nat.add_assoc] using h

omit [Fintype σ] in
private theorem positive_eval (r : Old m np) (x : σ → Bool) :
    (positive F r).eval x = true ↔ 0 < value (x ∘ widthPins F r) := by
  have h := eqWord_eval (fun j => StatementCircuit.Expr.input (widthPins F r j)) (fun _ => .const false) x
  simp only [wordValue,StatementCircuit.Expr.eval,zero_value] at h
  simpa only [positive,StatementCircuit.Expr.eval,Bool.not_eq_true',Bool.eq_false_iff,Nat.pos_iff_ne_zero,Function.comp_def] using not_congr h

omit [Fintype σ] in
private theorem distinct_eval (e : Fin m) (x : σ → Bool) :
    (distinct F e).eval x = true ↔
      value (x ∘ F.oldPtr (Layer.edgeEnd e true)) ≠ value (x ∘ F.oldPtr (Layer.edgeEnd e false)) := by
  have h := eqWord_eval (fun j => StatementCircuit.Expr.input (F.oldPtr (Layer.edgeEnd e true) j))
    (fun j => .input (F.oldPtr (Layer.edgeEnd e false) j)) x
  simpa only [distinct,StatementCircuit.Expr.eval,Bool.not_eq_true',Bool.eq_false_iff,wordValue,
    Function.comp_def] using not_congr h

/-- Exact sparse row acceptance for any input bit assignment. -/
theorem source_enable (r : Row m np extra) (x : σ → Bool) :
    (source F).eval x (r,.inl ()) = true ↔ r.elim (fun z => 0 < value (x ∘ widthPins F z) ∧
      z.elim (fun p => p.2 = true ∨ value (x ∘ F.oldPtr (Layer.edgeEnd p.1 true)) ≠
        value (x ∘ F.oldPtr (Layer.edgeEnd p.1 false))) (fun _ => True))
      (fun p => x (F.present (hop p.1 p.2.succ)) = true) := by
  have ini : (Frame.initial (id : σ → σ)).eval x = x := funext fun i => Frame.initial_eval _ _ _
  rcases r with (⟨e,side⟩ | p) | ⟨e,k⟩
  · cases side <;> simp [source,expr,ini,enable,StatementCircuit.Expr.eval,positive_eval,distinct_eval]
  · simp [source,expr,ini,enable,positive_eval]
  · simp [source,expr,enable,StatementCircuit.Expr.eval]

/-- Pointer of the newly selected endpoint, or the true predecessor's relay destination. -/
def owner (x : σ → Bool) (r : Row m np extra) : ℕ :=
  value (x ∘ F.newPtr (r.elim (fun a => oldTarget a (long F x a)) (fun p => relayLeft p.1 p.2)))

/-- The actual returned ownership field agrees with the successor endpoint table. -/
theorem source_owner (r : Row m np extra) (x : σ → Bool) :
    value (fun j => (source F).eval x (r,.inr (.inl j))) = owner F x r := by
  have ini : (Frame.initial (id : σ → σ)).eval x = x := funext fun i => Frame.initial_eval _ _ _
  cases r with
  | inl r => simp [source,expr,ini,owner,fetch_eval,Function.comp_def]
  | inr z => rcases z with ⟨e,k⟩; simp [source,expr,owner,StatementCircuit.Expr.eval,Function.comp_def]

/-- The scalar operands of the actual equality command. Relays have zero work
and both words are already in their one-copy physical incidence array. -/
def values (x : σ → Bool) : Row m np extra → Layer.Arg → ℕ
  | .inl r,.work => value (x ∘ F.work (oldEnd r))
  | .inl r,.extent => value (x ∘ F.extent (oldEnd r))
  | .inl r,.oldBase => value (x ∘ F.oldView (oldEnd r))
  | .inl r,.newBase => value (x ∘ F.newView (oldTarget r (long F x r)))
  | .inl r,.width => value (x ∘ widthPins F r)
  | .inr (e,j),.oldBase => value (x ∘ F.newView (relayLeft e j))
  | .inr (e,j),.newBase => value (x ∘ F.newView (relayRight e j))
  | .inr (e,_),.width => value (x ∘ F.edgeWidth e)
  | _,_ => 0

/-- Every output operand bit belongs to its selected field, including the dynamic last hop. -/
theorem source_value (r : Row m np extra) (a : Layer.Arg) (x : σ → Bool) :
    value (fun j => (source F).eval x (r,.inr (.inr (a,j)))) = values F x r a := by
  have ini : (Frame.initial (id : σ → σ)).eval x = x := funext fun i => Frame.initial_eval _ _ _
  rcases r with r | ⟨e,k⟩ <;> cases a <;>
    simp [source,expr,ini,args,values,fetch_eval,StatementCircuit.Expr.eval,Function.comp_def,zero_value]

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
