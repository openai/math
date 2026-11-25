import OAI.Computability.BorderVNP.CellPacketGeometryCounts

/-! # Gate charges of both public sparse word and descriptor sorts

The complete assembler has near-linear cost in the number of live public words,
chunk slots and site records, up to the logarithmic word and sorting widths.
The bounds do not depend on private body lengths, multiplicities or field values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open VPVNP.VerifierNetwork PackedHistogram ParseBatchSort Packing.Word
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

namespace LiveWords

open private counts scalar prepare emit ownerBit atomBit from OAI.Computability.BorderVNP.CellPacketGeometryCounts

/-- Gate overhead of one batched histogram, including its padding and return sort. -/
def histogramBudget (s C k w : ℕ) :=
  let b := Nat.clog 2 (s+C)
  2^b * ((k+1+w) + ((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) +
    w*(60*k+16*w+33) + b^2*(24*(w+b)+1))

private theorem counts_size {E : Type*} [Fintype E] {s C k w : ℕ} (n : Fin s → ℕ) :
    (counts s C k w E n).size ≤ histogramBudget s C k w := by
  have h := queries_size (layout (Fin s) (Fin C)) (fun j i => (StatementCircuit.Expr.input (.inl (j,i)) : Expr (Input s k w E)))
    (fun j => scalar w (n j)) (fun c => scalar k c.val) 1 le_rfl
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [counts,histogramBudget,Fintype.card_fin,mul_one] using h

/-- The upstream geometry gates run once, both weighted cell counts use sparse
histograms, and all public word and owner pins are emitted with one gate per bit. -/
theorem frame_size {σ E : Type*} [Fintype σ] [Fintype E] {s C k w N M : ℕ}
    (up : Frame σ (Input s k w E)) (boxes rows : Fin s → ℕ)
    (data : Fin N → Owner s C × Atom E C) (chunk : Fin M → Owner s C) :
    (frame up boxes rows data chunk).size ≤ up.size + 2*histogramBudget s C k w +
      N*(k+w) + M*k + Fintype.card E*w + 1 := by
  have hb := counts_size (E := E) (C := C) (k := k) (w := w) boxes
  have hr := counts_size (E := E) (C := C) (k := k) (w := w) rows
  have h (i : Schema.Pins N M k w E) : (emit data chunk i).size ≤ 1 := by
    rcases i with ⟨i,j|j⟩ | ⟨i,j⟩ | ⟨e,j⟩ | u
    · cases h : (data i).1 <;> simp [emit,ownerBit,h,scalar,PackedHistogram.fixed,StatementCircuit.Expr.size]
    · cases h : (data i).2 <;> simp [emit,atomBit,h,scalar,PackedHistogram.fixed,StatementCircuit.Expr.size]
    · cases h : chunk i <;> simp [emit,ownerBit,h,scalar,PackedHistogram.fixed,StatementCircuit.Expr.size]
    · rfl
    · rfl
  have st := Frame.step_size_le (prepare boxes rows C k w E) (emit data chunk) 1 h
  simp only [prepare,Frame.withInput_size,Crossing.parallelFrame_size,Schema.Pins,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,mul_one] at st
  simp only [frame,Frame.subst_size]
  exact (Nat.add_le_add_left st _).trans (by omega)

end LiveWords

namespace Schema

open private field keyPin valuePin from OAI.Computability.BorderVNP.CellPacketGeometrySchema

/-- Inserting real markers and padding, expanding owner keys over triples and
retaining the operand bank all cost one gate per emitted input bit. -/
theorem source_size {σ E : Type*} [Fintype σ] [Fintype E] {N M k w : ℕ} (C p d : ℕ)
    (upstream : Frame σ (Pins N M k w E)) :
    (source C p d upstream).size ≤ upstream.size + 2^p*(k+w) + 2^d*k + Fintype.card E*w+1 := by
  have h (i : Columns p d k w E) : (field C N M p d k w E i).size ≤ 1 := by
    rcases i with ⟨i,j|j⟩ | ⟨i,j⟩ | ⟨e,j⟩ | u
    · cases he : Markers.row C N i.val <;> simp [field,keyPin,he,StatementCircuit.Expr.size]
    · cases he : Markers.row C N i.val <;> simp [field,valuePin,he,StatementCircuit.Expr.size]
    · cases he : Markers.row C (coords M).length i.val <;> simp [field,keyPin,he,StatementCircuit.Expr.size]
    · rfl
    · rfl
  have h := Frame.step_size_le upstream (field C N M p d k w E) 1 h
  simp only [Columns,Stable.Input,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,
    mul_one] at h
  exact h.trans_eq (by omega)

/-- The inclusive span uses a subtraction and an addition. Other descriptor
fields use fewer expression nodes, even for a private box. -/
theorem expression_nodes_le {C N M p : ℕ} {E : Type*} (d : ℕ) (fit : C+N+C ≤ 2^p)
    (dest H : ℕ) (ref : Fin M → Reference N E) (i : Fin (2^d)) :
    (expression C d fit dest H ref i).nodes ≤ 5 := by
  unfold expression
  cases Markers.row C (coords M).length i.val with
  | data z =>
    let r := (coords M)[z.val]
    change ((ref r.1).fields fit dest H r.2).nodes ≤ 5
    rcases r with ⟨t,j⟩
    cases he : ref t <;> fin_cases j <;> norm_num [Reference.fields,publicDescriptor,privateDescriptor,
      addressExpr,extentExpr,WidthExpr.nodes]
  | _ => exact (by decide : 1 ≤ 5)

/-- Full sorter and three-word descriptor arithmetic after the sparse live word
pins. Both Batcher circuits retain the same upstream frame by fanout. -/
theorem joint_budget {σ E : Type*} [Fintype σ] [Fintype E] {C N M k w p d : ℕ}
    (upstream : Frame σ (Pins N M k w E)) (fit : C+N+C ≤ 2^p) (dest H : ℕ)
    (ref : Fin M → Reference N E) :
    (joint (source C p d upstream) (expression C d fit dest H ref)).size ≤
      upstream.size + 2^p*(k+w) + 2^d*k + Fintype.card E*w + 1 +
      (sortedFrame p k w).size + (sortedFrame d k w).size + 1 + 5*2^d*(100*(w+1)^2) := by
  have h := joint_size (source C p d upstream) (expression C d fit dest H ref)
  have hs := source_size C p d upstream
  have hn := Finset.sum_le_sum (s := Finset.univ) (fun i _ => expression_nodes_le d fit dest H ref i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hn
  change (∑ i, (expression C d fit dest H ref i).nodes) ≤ 2^d*5 at hn
  rw [Nat.mul_comm (2^d) 5] at hn
  exact h.trans (Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ hn))

end Schema
end CellPacketGeometry

end BorderVNP
end Computability
end OAI
