import OAI.Computability.BorderVNP.PackedCellAddressOutputs
import OAI.Computability.BorderVNP.PackedWordCircuit
import OAI.Computability.BorderVNP.CellPacketGeometryLiveTemplate
import OAI.Computability.BorderVNP.DiagonalTallyCellReports

/-! # Computing the scalar packet addresses of the actual gadget count bits

A shared cell-address frame already produces the two end markers of interest.
The added gates retain the private-region end and add each fixed bit ordinal
to the total-region end. The output order is gadget-major and then bit-major.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.FinalReports

open Crossing CellAddresses CellAddressViews CellAddressPhysical CellAddressCircuit ParseBatchSort
open VPVNP.VerifierNetwork CellPacketGeometry.LiveWords DiagonalTallyCellReports
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

/-- Per-cell private count and every scalar used by a gadget report word. -/
abbrev Pin (C g digits : ℕ) := Fin C ⊕ (Fin C × Fin g × Fin digits)

/-- Fixed gadget and bit ordinals encoded into the report portion of the template. -/
def countPins {C g digits : ℕ} (c : Fin C) : List (List (Pin C g digits)) :=
  List.ofFn fun i : Fin g => List.ofFn fun j : Fin digits => .inr (c,i,j)

variable {s m n C g digits w : ℕ}

private def marker (c : Fin C) (i : Fin 3) (j : Fin w) : Expr (View s m n C × Fin w) :=
  .input (.inr (.inr (i,c)),j)

private noncomputable def constant (v : ℕ) (j : Fin w) : Expr (View s m n C × Fin w) :=
  .const ((ParseBatchCounts.numberWords w).symm ⟨v % 2^w,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ j)

private noncomputable def emit (ij : Pin C g digits × Fin w) : Expr (View s m n C × Fin w) :=
  match ij.1 with
  | .inl c => marker c 1 ij.2
  | .inr (c,i,j) => addWord (marker c 2) (constant (i.val*digits+j.val)) ij.2

/-- A single Boolean step on the already shared owner/address outputs. -/
noncomputable def frame {σ : Type*} [Fintype σ] (base : Frame σ (View s m n C × Fin w)) :
    Frame σ (Pin C g digits × Fin w) := base.step emit

/-- The added gates are linear in the count-field list length and quadratic
in the arithmetic word width. The shared address program is charged once. -/
theorem frame_size {σ : Type*} [Fintype σ] (base : Frame σ (View s m n C × Fin w)) :
    (frame (g := g) (digits := digits) base).size ≤
      base.size + (C+C*g*digits)*w*(100*(w+1)) := by
  have h (ij : Pin C g digits × Fin w) : (emit (s := s) (m := m) (n := n) ij).size ≤ 100*(w+1) := by
    rcases ij with ⟨c|⟨c,i,j⟩,a⟩
    · change 1 ≤ _; omega
    · have t := sumWord_size_le false (marker (s := s) (m := m) (n := n) c 2) (constant (i.val*digits+j.val)) 1
        (fun _ => le_refl 1) (fun _ => le_refl 1) a
      exact t.trans (by omega)
  have bound := Frame.step_size_le base emit _ h
  simpa only [frame,Pin,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,Nat.mul_assoc] using bound

private theorem constant_value (x : View s m n C × Fin w → Bool) (v : ℕ) (hv : v < 2^w) :
    wordValue x (constant v) = v := by
  exact (ParseBatchCounts.value_encode (w := w) ⟨v % 2^w,Nat.mod_lt _ (Nat.two_pow_pos _)⟩).trans (Nat.mod_eq_of_lt hv)

variable {D d k : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
  (portID : P ↪ Fin n) {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)
  {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x)
  (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)

include h fit

/-- The compiled private-count column is the actual number of guessed bits. -/
theorem private_value (c : Fin C) :
    value (fun j => (frame (g := g) (digits := digits) (CellAddressViews.frame F)).eval x (.inl c,j)) =
      guessedSize N cell c + siteSize N cell c aux := by
  simpa only [frame,Frame.step_eval,emit,marker,StatementCircuit.Expr.eval,ite_false,Nat.add_zero,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide] using
    marker_value N cell aux siteID edgeID portID F h fit c 1

/-- The compiled bit-address column selects the exact supplied count bit of
this gadget at this cell. -/
theorem address_value (c : Fin C) (i : Fin g) (j : Fin digits)
    (room : guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c + i.val*digits+j.val < 2^w) :
    value (fun a => (frame (CellAddressViews.frame F)).eval x (.inr (c,i,j),a)) =
      guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c + i.val*digits+j.val := by
  let z := (CellAddressViews.frame F).eval x
  have base : wordValue z (marker c 2) = guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c := by
    simpa only [wordValue,marker,StatementCircuit.Expr.eval,ite_false,ite_true,
      show (2 : Fin 3) ≠ 0 by decide] using marker_value N cell aux siteID edgeID portID F h fit c 2
  have fixed := constant_value z (i.val*digits+j.val) (by omega)
  simp only [frame,Frame.step_eval,emit]
  change wordValue z (addWord (marker c 2) (constant (i.val*digits+j.val))) = _
  rw [addWord_value z _ _ (by rw [base,fixed]; omega),base,fixed]
  omega

/-- The nested lists of operands delivered by the actual shared word frame
are exactly the canonical report bank of the typed cell. -/
theorem countPins_value (c : Fin C)
    (room : guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c + g*digits ≤ 2^w) :
    (countPins (g := g) (digits := digits) c).map (List.map fun key =>
        value fun j => (frame (CellAddressViews.frame F)).eval x (key,j)) =
      countFields (guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c) g digits := by
  simp only [countPins,countFields,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  congr 1
  funext j
  apply address_value N cell aux siteID edgeID portID F h fit
  have hcap := Nat.mul_le_mul_right digits (show i.val+1 ≤ g from i.isLt)
  rw [Nat.add_mul,Nat.one_mul] at hcap
  have hj := j.isLt
  omega

end Packing.FinalReports

end BorderVNP
end Computability
end OAI
