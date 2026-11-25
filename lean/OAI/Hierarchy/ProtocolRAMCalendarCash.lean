import OAI.Hierarchy.ProtocolRAMCalendarInventory

namespace OAI
/-! # Appending actual signed payments to the chronological calendar account -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators
noncomputable section
variable {w q d : ℕ} {I : Type*}

/-- A signed price is taken from the public price table indexed by the
actual printed label. Constant tables cover a fixed physical edge or fee. -/
structure ChargeWord where
  width : ℕ
  key : ℕ
  price : ℕ → ℝ

def ChargeWord.value (row : ChargeWord) (payload : ℕ) (m : Memory w) : ℝ :=
  (m row.width).val * row.price (m row.key).val / payload

def AccountColumns.row (A : AccountColumns I) (a : Attempt) (i : Fin (A.charges a)) : ChargeWord :=
  ⟨A.widthAt a i,A.priceKeyAt a i,A.unitPrice a i⟩

theorem AccountColumns.cash_words (A : AccountColumns I) (a : Attempt) (m : Memory w) :
    (A.read a m).paid = A.initialCharge + ∑ i, (A.row a i).value A.payloadWidth m := by
  simp only [read,ChargeWord.value,row,Finset.sum_div]

theorem ChargeWord.value_frame (row : ChargeWord) (payload : ℕ) (m out : Memory w)
    (width : out row.width=m row.width) (key : out row.key=m row.key) :
    row.value payload out=row.value payload m := by rw [ChargeWord.value,ChargeWord.value,width,key]

/-- The segment's issued physical receipt rows form the exact increment on the
signed account. Earlier rows are read in place on the same physical archive. -/
theorem AccountColumns.append_cash {R : Type*} [Fintype R] (A : AccountColumns I) (a b : Attempt)
    (m out : Memory w) (rows : R → ChargeWord) (enum : Fin (A.charges a) ⊕ R ≃ Fin (A.charges b))
    (old : ∀ i, A.row b (enum (.inl i))=A.row a i)
    (newRows : ∀ i, A.row b (enum (.inr i))=rows i)
    (frame : ∀ i, out (A.row a i).width=m (A.row a i).width ∧ out (A.row a i).key=m (A.row a i).key) :
    (A.read b out).paid = (A.read a m).paid + ∑ i, (rows i).value A.payloadWidth out := by
  rw [A.cash_words,A.cash_words,←enum.sum_comp (fun k => (A.row b k).value A.payloadWidth out),Fintype.sum_sum_type]
  simp only [old,newRows]
  have prior (i : Fin (A.charges a)) : (A.row a i).value A.payloadWidth out=(A.row a i).value A.payloadWidth m :=
    (A.row a i).value_frame A.payloadWidth m out (frame i).1 (frame i).2
  simp only [prior,add_assoc]

/-- Native address ordering and the calendar frame theorem supply preservation
of every old width and price key over the actual sequence of executed events. -/
theorem AccountColumns.append_executed {R : Type*} [Fintype R] (A : AccountColumns I)
    (C : Chart w q d) (es : List Event) (m : Memory w) (a b : Attempt)
    (rows : R → ChargeWord) (enum : Fin (A.charges a) ⊕ R ≃ Fin (A.charges b))
    (old : ∀ i, A.row b (enum (.inl i))=A.row a i)
    (newRows : ∀ i, A.row b (enum (.inr i))=rows i)
    (ready : mounted C es m)
    (safe : ∀ i e, e∈es → protected C (A.row a i).width e ∧ protected C (A.row a i).key e) :
    (A.read b (run C es m)).paid = (A.read a m).paid + ∑ i, (rows i).value A.payloadWidth (run C es m) :=
  A.append_cash a b m _ rows enum old newRows fun i =>
    ⟨run_frame C es m _ ready (fun e he => (safe i e he).1),
      run_frame C es m _ ready (fun e he => (safe i e he).2)⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
