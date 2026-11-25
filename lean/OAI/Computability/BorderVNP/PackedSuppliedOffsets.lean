import OAI.Computability.BorderVNP.PackedCellAddressScatter
import OAI.Computability.BorderVNP.PackedWordCircuit

/-! # Actual supplied offsets and sizes for the routing directory

A second batched lookup resolves each endpoint's private-region end from its
current cell label. Subtraction computes a relative supplied-slot address for
every cable end and every grouped external port. The per-cell count is the
difference of the supplied and private end markers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SuppliedOffsets

open Crossing PackedHistogram ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressViews
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private formula eval_formula formula_size from OAI.Computability.BorderVNP.PackedWordCircuit
open scoped Classical

variable {s m n C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

private abbrev Joint (s m n C k w : ℕ) := (View s m n C × Fin w) ⊕ (End m n × Fin k)
private abbrev Pins (s m n C k w : ℕ) := Joint s m n C k w ⊕ (End m n × Fin w)

private noncomputable def joint : Frame σ (Joint s m n C k w) := parallelFrame (CellAddressViews.frame F) (labels F)

private def marker (r : Fin 3) (c : Fin C) (j : Fin w) : Expr (Joint s m n C k w) :=
  .input (.inl (.inr (.inr (r,c)),j))

private def query (e : End m n) (j : Fin k) : Expr (Joint s m n C k w) := .input (.inr (e,j))

private noncomputable def fetch (codes : Fin C ↪ Fin (2^k)) :
    Frame (Joint s m n C k w) (End m n × Fin w) :=
  PackedLookup.lookup (layout (Fin C) (End m n)) codes (marker 1) query

private noncomputable def prepared : Frame σ (Pins s m n C k w) :=
  ((fetch F.cells).withInput).subst (joint F)

/-- Output numbers are endpoint-relative slots followed by per-cell supplied sizes. -/
abbrev Result (m n C : ℕ) := End m n ⊕ Fin C

private def operand (i : Result m n C) : Fin w ⊕ Fin w → Expr (Pins s m n C k w)
  | .inl j => .input (.inl (.inl (i.elim Sum.inl (fun c => .inr (.inr (2,c))),j)))
  | .inr j => .input (i.elim (fun e => .inr (e,j)) (fun c => .inl (.inl (.inr (.inr (1,c)),j))))

private def relative (i : Result m n C × Fin w) : Expr (Pins s m n C k w) :=
  plugExpr (operand i.1) (formula w Word.Op.sub i.2)

/-- Fixed shared Boolean program for every requested supplied slot and cell size. -/
noncomputable def frame : Frame σ (Result m n C × Fin w) := (prepared F).step relative

private theorem difference (x : σ → Bool) (i : Result m n C) :
    let y := (prepared F).eval x
    let z (a : Fin w ⊕ Fin w) := (operand i a).eval y
    value (fun j => (frame F).eval x (i,j)) = value (z ∘ Sum.inl) - value (z ∘ Sum.inr) := by
  intro y z
  simp only [frame,Frame.step_eval,relative,plugExpr_eval]
  exact eval_formula w Word.Op.sub z ((Nat.sub_le ..).trans_lt (value_lt _))

/-- The public relative offset uses precisely the private-end marker of the
owner resolved by the physical site-pointer lookup. -/
theorem endpoint_value (x : σ → Bool) (e : End m n) (c : Fin C)
    (owner : (data F x).loc e = (F.cells c).val) :
    value (fun j => (frame F).eval x (.inl e,j)) = suppliedSlot F x c (.inl e) 0 := by
  have addr : wordValue ((joint F).eval x) (query e) = (F.cells c).val := by
    simpa [joint,query,wordValue,StatementCircuit.Expr.eval,data] using owner
  have selected := PackedLookup.lookup_value (layout (Fin C) (End m n)) F.cells
    (marker (s:=s) (w:=w) 1) query ((joint F).eval x) e c addr
  rw [difference]
  simp only [Function.comp_def,operand,Sum.elim_inl,StatementCircuit.Expr.eval,
    prepared,Frame.subst_eval,Frame.withInput_eval_inl,Frame.withInput_eval_inr,
    joint,parallelFrame_eval_inl,suppliedSlot,Nat.add_zero]
  apply congrArg (_ - ·)
  simpa only [fetch,wordValue,marker,StatementCircuit.Expr.eval,joint,parallelFrame_eval_inl] using selected

/-- The size of a cell's supplied bank uses its exact two exported markers. -/
theorem size_value (x : σ → Bool) (c : Fin C) :
    value (fun j => (frame F).eval x (.inr c,j)) =
      value (fun j => (CellAddressViews.frame F).eval x (.inr (.inr (2,c)),j)) -
      value (fun j => (CellAddressViews.frame F).eval x (.inr (.inr (1,c)),j)) := by
  rw [difference]
  simp [operand,StatementCircuit.Expr.eval,Function.comp_def,prepared,joint]

/-- Sparse lookup and fixed-width subtraction are linear in padded row count
times a polynomial in the encoded address and offset widths. -/
theorem frame_size :
    let z := Nat.clog 2 (C+((m+m)+n))
    (frame F).size ≤ (CellAddressViews.frame F).size+(labels F).size+
      2^z*((k+1+w)+((w+z)+1+k)+z^2*(24*((w+z)+1+k)+1)+w*(60*k+16*w+33)+z^2*(24*(w+z)+1))+
      (((m+m)+n)+C)*w*(100*(w+1)) := by
  intro z
  have sub (i : Result m n C × Fin w) : (relative (s:=s) (k:=k) i).size ≤ 100*(w+1) := by
    have tiny (j : Fin w ⊕ Fin w) : (operand (s:=s) (k:=k) i.1 j).size ≤ 1 := by cases j <;> exact le_rfl
    exact (plugExpr_size _ _ (by decide : 1 ≤ 1) tiny).trans (by simpa using formula_size w Word.Op.sub i.2)
  have q := queries_size (layout (Fin C) (End m n)) (fun u => fixed (F.cells u))
    (marker (s:=s) (w:=w) 1) (query (m:=m) (n:=n)) 1 (by decide)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have h := Frame.step_size_le (prepared F) relative _ sub
  simp only [Result,End,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,prepared,Frame.subst_size,
    Frame.withInput_size,joint,parallelFrame_size,fetch,PackedLookup.lookup] at h
  simp only [End,Fintype.card_fin,Fintype.card_sum,Nat.mul_one] at q
  change (frame F).size ≤ _ at h
  dsimp only [z]
  omega

end Packing.SuppliedOffsets

end BorderVNP
end Computability
end OAI
