import OAI.Computability.BorderVNP.PackedBundleSort
import OAI.Computability.BorderVNP.CellPacketGeometryGateBudget

/-! # Constructing the scalar header fields from public placement and geometry words

One sparse lookup reads the receive pointer for each original site's actual final cell.
The address of its private description adds that pointer to its relative placement slot.
The work pointer remains the local base of the retained original box.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open PackedHistogram ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork Crossing RoutingISA
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private formula eval_formula formula_size from OAI.Computability.BorderVNP.PackedWordCircuit

/-- Per-site owner, private relative slot and staging address, per-cell receive pointer, and validity. -/
abbrev Operands (N C k w : ℕ) :=
  (Fin N × (Fin k ⊕ Bool × Fin w)) ⊕ ((Fin C × Fin w) ⊕ Unit)

/-- Public copy and bank sizes used by the private bundle scanner. -/
structure Shape where
  /-- Number of packed copies at this original site. -/
  copies : ℕ
  /-- One-copy internal bank and incoming port dimensions. -/
  fine : ℕ
  /-- Width of the incoming port bank. -/
  incoming : ℕ
  /-- Reserved report lanes per copy. -/
  cap : ℕ

/-- Construct the six fields after resolving the two independent pointer origins. -/
def Shape.header (h : Shape) (slot base : ℕ) : BundleHeader :=
  ⟨slot,h.copies,base,bottomStride (h.fine+h.incoming) h.cap,h.cap,h.fine+h.incoming⟩

variable {σ : Type*} [Fintype σ] {N C k w : ℕ}

private def recv (c : Fin C) (j : Fin w) : Expr (Operands N C k w) := .input (.inr (.inl (c,j)))
private def request (i : Fin N) (j : Fin k) : Expr (Operands N C k w) := .input (.inl (i,.inl j))

private noncomputable def pointers (codes : Fin C ↪ Fin (2^k)) :
    Frame (Operands N C k w) (Fin N × Fin w) :=
  PackedLookup.lookup (layout (Fin C) (Fin N)) codes recv request

private abbrev Prepared (N C k w : ℕ) := Operands N C k w ⊕ (Fin N × Fin w)

private def addPin (i : Fin N) : Fin w ⊕ Fin w → Expr (Prepared N C k w)
  | .inl j => .input (.inr (i,j))
  | .inr j => .input (.inl (.inl (i,.inr (false,j))))

private noncomputable def fixedField (w n : ℕ) : Fin w → Expr (Prepared N C k w) := fixed (Fin.ofNat (2^w) n)

private noncomputable def emit (shape : Fin N → Shape) : Pins N k w → Expr (Prepared N C k w)
  | .inl (i,.inl j) => .input (.inl (.inl (i,.inl j)))
  | .inl (i,.inr (f,j)) =>
    let h := shape i
    match f.val with
    | 0 => plugExpr (addPin i) (formula w Word.Op.add j)
    | 1 => fixedField w h.copies j
    | 2 => .input (.inl (.inl (i,.inr (true,j))))
    | 3 => fixedField w (bottomStride (h.fine+h.incoming) h.cap) j
    | 4 => fixedField w h.cap j
    | _ => fixedField w (h.fine+h.incoming) j
  | .inr _ => .input (.inl (.inr (.inr ())))

/-- Shared sparse pointer lookup followed by the six-word arithmetic and pin map. -/
noncomputable def headerFrame (codes : Fin C ↪ Fin (2^k)) (shape : Fin N → Shape)
    (up : Frame σ (Operands N C k w)) : Frame σ (Pins N k w) :=
  (((pointers codes).withInput.step (emit shape)).subst up)

/-- The final owner pin remains the original live geometry key. -/
theorem headerFrame_key (codes : Fin C ↪ Fin (2^k)) (shape : Fin N → Shape) (up : Frame σ (Operands N C k w))
    (x : σ → Bool) (i : Fin N) (j : Fin k) :
    (headerFrame codes shape up).eval x (.inl (i,.inl j)) = up.eval x (.inl (i,.inl j)) := by
  simp [headerFrame,emit,StatementCircuit.Expr.eval]

/-- Preserve the validity bit of the original geometry frame. -/
theorem headerFrame_valid (codes : Fin C ↪ Fin (2^k)) (shape : Fin N → Shape) (up : Frame σ (Operands N C k w))
    (x : σ → Bool) :
    (headerFrame codes shape up).eval x (.inr ()) = up.eval x (.inr (.inr ())) := by
  simp [headerFrame,emit,StatementCircuit.Expr.eval]

private theorem fixedField_value (v : Prepared N C k w → Bool) (n : ℕ) (fit : n < 2^w) :
    value (fun j => (fixedField w n j).eval v) = n :=
  (fixed_value v (Fin.ofNat (2^w) n)).trans (Nat.mod_eq_of_lt fit)

/-- A genuine addressed RAM input determines every header field. No completed header
table or sorted sections enter the source frame. -/
theorem headerFrame_value (codes : Fin C ↪ Fin (2^k)) (shape : Fin N → Shape) (up : Frame σ (Operands N C k w))
    (x : σ → Bool) (i : Fin N) (owner : Fin C)
    (key : value (fun j => up.eval x (.inl (i,.inl j))) = (codes owner).val)
    (slot base ptr : ℕ)
    (offset : value (fun j => up.eval x (.inl (i,.inr (false,j)))) = slot)
    (staging : value (fun j => up.eval x (.inl (i,.inr (true,j)))) = base)
    (receive : value (fun j => up.eval x (.inr (.inl (owner,j)))) = ptr)
    (room : ptr+slot < 2^w) (copies : (shape i).copies < 2^w)
    (bank : bottomStride ((shape i).fine+(shape i).incoming) (shape i).cap < 2^w)
    (f : Fin 6) :
    value (fun j => (headerFrame codes shape up).eval x (.inl (i,.inr (f,j)))) =
      scalar ((shape i).header (ptr+slot) base) f := by
  let y := up.eval x
  let z := (pointers codes).withInput.eval y
  have address : wordValue y (request i) = (codes owner).val := key
  have read : value (fun j => (pointers codes).eval y (i,j)) = ptr :=
    (PackedLookup.lookup_value (layout (Fin C) (Fin N)) codes recv request y i owner address).trans receive
  have a : value (fun j => (addPin i (.inl j)).eval z) = ptr := by
    simpa only [addPin,z,StatementCircuit.Expr.eval,Frame.withInput_eval_inr] using read
  have b : value (fun j => (addPin i (.inr j)).eval z) = slot := by
    simpa only [addPin,z,y,StatementCircuit.Expr.eval,Frame.withInput_eval_inl] using offset
  have add : value (fun j => (plugExpr (addPin i) (formula w Word.Op.add j)).eval z) = ptr+slot := by
    simp only [plugExpr_eval]
    let v := fun s => (addPin i s).eval z
    change value (fun j => (formula w Word.Op.add j).eval v) = _
    have av : value (v ∘ Sum.inl) = ptr := a
    have bv : value (v ∘ Sum.inr) = slot := b
    rw [eval_formula _ _ v (by simpa only [Word.Op.apply,av,bv] using room),Word.Op.apply,av,bv]
  have cap : (shape i).cap < 2^w := by unfold bottomStride at bank; omega
  have orig : (shape i).fine+(shape i).incoming < 2^w := by unfold bottomStride at bank; omega
  simp only [headerFrame,Frame.subst_eval,Frame.step_eval]
  change value (fun j => (emit shape (.inl (i,.inr (f,j)))).eval z) = _
  fin_cases f
  · exact add
  · exact fixedField_value z _ copies
  · change value (fun j => z (.inl (.inl (i,.inr (true,j))))) = base
    simpa only [z,y,Frame.withInput_eval_inl] using staging
  · exact fixedField_value z _ bank
  · exact fixedField_value z _ cap
  · exact fixedField_value z _ orig

/-- The word encoder is linear in the number of scalar bits up to the sparse sort and
the fixed-width addition circuit. -/
theorem headerFrame_size (codes : Fin C ↪ Fin (2^k)) (shape : Fin N → Shape) (up : Frame σ (Operands N C k w)) :
    (headerFrame codes shape up).size ≤ up.size +
      CellPacketGeometry.LiveWords.histogramBudget C N k w + (N*(k+6*w)+1)*(100*(w+1)) := by
  have hs := queries_size (layout (Fin C) (Fin N)) (fun c => fixed (codes c)) (recv (N := N) (w := w)) request
    1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have hp : (pointers (N:=N) (w:=w) codes).size ≤ CellPacketGeometry.LiveWords.histogramBudget C N k w := by
    simpa only [pointers,PackedLookup.lookup,CellPacketGeometry.LiveWords.histogramBudget,Fintype.card_fin,mul_one]
      using hs
  have bound (q : Pins N k w) : (emit (C:=C) shape q).size ≤ 100*(w+1) := by
    rcases q with ⟨i,j|⟨f,j⟩⟩ | u
    · change 1 ≤ _; omega
    · fin_cases f
      · have he := plugExpr_size (addPin (C:=C) (k:=k) i) (formula w Word.Op.add j) (D:=1) le_rfl
          (fun a => by cases a <;> rfl)
        exact he.trans (by simpa only [mul_one] using formula_size w Word.Op.add j)
      all_goals change 1 ≤ _; omega
    · change 1 ≤ _; omega
  have h := Frame.step_size_le (pointers (N:=N) (w:=w) codes).withInput (emit shape) (100*(w+1)) bound
  simp only [Pins,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,Frame.withInput_size] at h
  rw [headerFrame,Frame.subst_size]
  exact (Nat.add_le_add_left (h.trans (Nat.add_le_add_right hp _)) _).trans_eq (by omega)

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
