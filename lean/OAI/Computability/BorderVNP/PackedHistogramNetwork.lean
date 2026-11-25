import OAI.Computability.BorderVNP.PackedHistogramWords
import OAI.Computability.BorderVNP.PackedHistogramSum
import OAI.Computability.BorderVNP.PackedScan

/-! # Two Batcher sorts and a shared segmented scan for weighted bucket queries -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram

open ParseBatchLookup ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

/-- An input row has an address, a query tag, and one weight word. -/
abbrev Raw (b k w : ℕ) := Fin (2^b) × (Fin k ⊕ (Unit ⊕ Fin w))

/-- Expanded physical bit record, including the hardwired original ordinal. -/
abbrev Expanded (b k w : ℕ) := Pins b (((w+b)+1)+k)

variable {b k w : ℕ}

/-- Numerical value at the address pins of the raw input. -/
def keyValue (x : Raw b k w → Bool) (i : Fin (2^b)) : ℕ := value fun j => x (i,.inl j)

/-- Query bit distinguishes zero-weight requests from source rows. -/
def isQuery (x : Raw b k w → Bool) (i : Fin (2^b)) : Bool := x (i,.inr (.inl ()))

/-- Numerical payload of a source or query row. -/
def weightValue (x : Raw b k w → Bool) (i : Fin (2^b)) : ℕ := value fun j => x (i,.inr (.inr j))

/-- The fully expanded word for a physical row. -/
noncomputable def rawWord (x : Raw b k w → Bool) (i : Fin (2^b)) : Fin (((w+b)+1)+k) → Bool :=
  record (fun j => x (i,.inl j)) (isQuery x i) ((numberWords b).symm i)
    (fun j => x (i,.inr (.inr j)))

private noncomputable def prepare (i : Fin (2^b)) : Fin (((w+b)+1)+k) → Expr (Raw b k w) :=
  record (fun j => .input (i,.inl j)) (.input (i,.inr (.inl ()))) (fun j => .const ((numberWords b).symm i j))
    (fun j => .input (i,.inr (.inr j)))

/-- Address sort input, with a hardwired ordinal accompanying each row. -/
noncomputable def expanded (b k w : ℕ) : Frame (Raw b k w) (Expanded b k w) :=
  (Frame.initial id).step fun ij => prepare ij.1 ij.2

theorem expanded_eval (x : Raw b k w → Bool) (i : Fin (2^b)) (j : Fin (((w+b)+1)+k)) :
    (expanded b k w).eval x (i,j) = rawWord x i j := by
  have hid : (Frame.initial (id : Raw b k w → Raw b k w)).eval x = x :=
    funext fun i => Frame.initial_eval id x i
  simp only [expanded, Frame.step_eval, hid]
  exact congrFun (record_map (StatementCircuit.Expr.eval x) ..) j

private theorem prepare_size (i : Fin (2^b)) (j : Fin (((w+b)+1)+k)) : (prepare i j).size = 1 := by
  let he := record_map StatementCircuit.Expr.size
    (fun l : Fin k => (StatementCircuit.Expr.input (i,.inl l) : Expr (Raw b k w)))
    (StatementCircuit.Expr.input (i,.inr (.inl ())))
    (fun l : Fin b => StatementCircuit.Expr.const ((numberWords b).symm i l))
    (fun l : Fin w => StatementCircuit.Expr.input (i,.inr (.inr l)))
  exact congrFun (he.trans (record_const 1)) j

/-- Width of the expanded input is charged once per row. -/
theorem expanded_size (b k w : ℕ) : (expanded b k w).size ≤ 2^b*((w+b)+1+k) := by
  have h := Frame.step_size_le (Frame.initial (id : Raw b k w → Raw b k w))
    (fun ij : Expanded b k w => prepare ij.1 ij.2) 1 (fun ij => (prepare_size ij.1 ij.2).le)
  simpa [expanded, Pins] using h

/-- Totalized physical row address for the scan. All accessed rows are in range. -/
def lane (b i : ℕ) : Fin (2^b) := ⟨i % 2^b, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

@[simp] theorem lane_val (i : Fin (2^b)) : lane b i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- Address pins fed into the segmented scan after sorting. -/
def addressWires (b k w : ℕ) (i : ℕ) (j : Fin k) : Expanded b k w := (lane b i, addressPin b w j)

/-- Weight pins fed into the segmented scan after sorting. -/
def weightWires (b k w : ℕ) (i : ℕ) (j : Fin w) : Expanded b k w := (lane b i, weightPin k b j)

/-- One shared scan on all sorted weights. -/
noncomputable def totals (b k w : ℕ) : Frame (Expanded b k w) (Pins b w) :=
  PackedScan.scan (addressWires b k w) (weightWires b k w) (2^b)

/-- Combine ordinal and computed total by rewiring alone. -/
noncomputable def returnBlock (b k w : ℕ) : Frame (Expanded b k w) (Pins b (w+b)) :=
  (totals b k w).withInput.select fun ij =>
    prepend (fun j => Sum.inl (ij.1, ordinalPin k w j)) (fun j => Sum.inr (ij.1,j)) ij.2

theorem returnBlock_eval (s : Expanded b k w → Bool) (i : Fin (2^b)) (j : Fin (w+b)) :
    (returnBlock b k w).eval s (i,j) =
      prepend (fun d => s (i,ordinalPin k w d)) (fun d => (totals b k w).eval s (i,d)) j := by
  simp only [returnBlock, Frame.select_eval]
  rw [show (totals b k w).withInput.eval s (prepend (fun d => Sum.inl (i,ordinalPin k w d))
    (fun d => Sum.inr (i,d)) j) = _ from congrFun (prepend_map ((totals b k w).withInput.eval s) ..) j]
  simp [Function.comp_def]

/-- The inputs for the second sort are the ordinals of the first sort and the computed totals. -/
noncomputable def returnRows (b k w : ℕ) : Frame (Raw b k w) (Pins b (w+b)) :=
  (returnBlock b k w).subst (phases b le_rfl (expanded b k w))

/-- The output row at the original physical ordinal holds its total at the first sort. -/
noncomputable def frame (b k w : ℕ) : Frame (Raw b k w) (Pins b w) :=
  (phases b le_rfl (returnRows b k w)).select fun ij => (ij.1,lowPin b ij.2)

/-- Gate count for both shared sorts, all additions, and both ordinal wiring layers. -/
theorem frame_size (b k w : ℕ) : (frame b k w).size ≤ 2^b *
    (((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) + w*(60*k+16*w+33) + b^2*(24*(w+b)+1)) := by
  have h₁ := expanded_size b k w
  have h₂ := phases_size b le_rfl (expanded b k w)
  have h₃ := PackedScan.scan_size (addressWires b k w) (weightWires b k w) (2^b)
  have h₄ := phases_size b le_rfl (returnRows b k w)
  change (totals b k w).size ≤ _ at h₃
  simp only [returnRows, Frame.subst_size, returnBlock, Frame.select_size, Frame.withInput_size] at h₄
  simp only [frame, Frame.select_size, returnRows, returnBlock]
  nlinarith only [h₁,h₂,h₃,h₄]

end PackedHistogram

end BorderVNP
end Computability
end OAI
