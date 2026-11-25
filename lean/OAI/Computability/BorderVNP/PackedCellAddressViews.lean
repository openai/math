import OAI.Computability.BorderVNP.PackedCellAddressStarts
import OAI.Computability.BorderVNP.PackedCellAddressCost
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-! # Compiled site, port and wire views of the cell assignment bank

A private wire has a single start shared by both endpoints. A crossing wire
has one supplied start at each endpoint. The circuit chooses between these
cases from the resolved site cells, and exports the start in physical wire order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressViews

open Crossing ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame

/-- Wire and port starts, then staging slab starts and the three per-cell region ends. -/
abbrev View (s m n C : ℕ) := End m n ⊕ (Fin s ⊕ (Fin 3 × Fin C))

private abbrev Join (s m n C k w : ℕ) := (Row s m n C × Fin w) ⊕ (End m n × Fin k)

variable {s m n C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

private noncomputable def joined : Frame σ (Join s m n C k w) :=
  parallelFrame (CellAddressCircuit.frame F) (labels F)

private def equalCells (e : Fin m) : Expr (Join s m n C k w) :=
  eqWord (fun j => .input (.inr (.inl (.inl e),j))) (fun j => .input (.inr (.inl (.inr e),j)))

private def read (r : Row s m n C) (b : Fin w) : Expr (Join s m n C k w) := .input (.inl (r,b))

private def endpoint (e : Fin m) (side : Fin m ⊕ Fin m) (b : Fin w) : Expr (Join s m n C k w) :=
  mux (equalCells e) (read (.inl (.inl (.inl e))) b) (read (.inr (.inl (.inl side))) b)

private def select : View s m n C × Fin w → Expr (Join s m n C k w)
  | (.inl (.inl (.inl e)),b) => endpoint e (.inl e) b
  | (.inl (.inl (.inr e)),b) => endpoint e (.inr e) b
  | (.inl (.inr p),b) => read (.inr (.inl (.inr p))) b
  | (.inr (.inl v),b) => read (.inl (.inr (.inl v))) b
  | (.inr (.inr (region,c)),b) => read (marker region c) b

/-- The public output frame used to relocate the site-local sparse row records. -/
noncomputable def frame : Frame σ (View s m n C × Fin w) := (joined F).step select

/-- Actual scan row selected by the resolved endpoint labels. -/
def row (a : Data s m n) : View s m n C → Row s m n C
  | .inl (.inl (.inl e)) =>
    if a.loc (.inl (.inl e)) = a.loc (.inl (.inr e)) then .inl (.inl (.inl e)) else .inr (.inl (.inl (.inl e)))
  | .inl (.inl (.inr e)) =>
    if a.loc (.inl (.inl e)) = a.loc (.inl (.inr e)) then .inl (.inl (.inl e)) else .inr (.inl (.inl (.inr e)))
  | .inl (.inr p) => .inr (.inl (.inr p))
  | .inr (.inl v) => .inl (.inr (.inl v))
  | .inr (.inr (region,c)) => marker region c

/-- Every view returns the corresponding physical prefix, sharing internal addresses at both ends. -/
theorem frame_eval (x : σ → Bool) (v : View s m n C) (b : Fin w) :
    (frame F).eval x (v,b) = (CellAddressCircuit.frame F).eval x (row (data F x) v,b) := by
  have he (e : Fin m) :
      (equalCells e).eval ((joined F).eval x) = true ↔
        (data F x).loc (.inl (.inl e)) = (data F x).loc (.inl (.inr e)) := by
    rw [equalCells,eqWord_eval]
    simp only [wordValue,StatementCircuit.Expr.eval,joined,parallelFrame_eval_inr,data]
  rcases v with ((e|e)|p)|(v|⟨r,c⟩)
  all_goals try (simp [frame,select,read,joined,row,StatementCircuit.Expr.eval]; done)
  all_goals
    simp only [frame,Frame.step_eval,select,endpoint,mux_eval,he,row]
    split <;> simp [*,read,joined,StatementCircuit.Expr.eval]

/-- Both joint frames, and one local word comparator and multiplexer per returned bit. -/
theorem frame_size :
    (frame F).size ≤ gateBound s m n C d k w + labelBound s m n d k +
      Fintype.card (View s m n C)*w*(60*k+16) := by
  have he (e : Fin m) : (equalCells (s := s) (n := n) (C := C) (k := k) (w := w) e).size ≤ 30*k+3 :=
    eqWord_size _ _ (fun _ => le_rfl) (fun _ => le_rfl)
  have bound (ij : View s m n C × Fin w) : (select (k := k) ij).size ≤ 60*k+16 := by
    rcases ij with ⟨((e|e)|p)|(v|⟨r,c⟩),b⟩
    all_goals simp only [select,endpoint,mux,read,StatementCircuit.Expr.size]
    all_goals first | omega | exact (by have := he e; omega)
  have h := Frame.step_size_le (joined F) select _ bound
  simp only [joined,parallelFrame_size,Fintype.card_prod,Fintype.card_fin] at h
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add (CellAddressCircuit.frame_size F) (labels_size F)) _)

end Packing.CellAddressViews

end BorderVNP
end Computability
end OAI
