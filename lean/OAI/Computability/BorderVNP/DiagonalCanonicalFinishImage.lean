import OAI.Computability.BorderVNP.CubePhysicalFinishReceipt

/-! # Concrete signed finish receipts for canonical common fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM DiagonalTallyRAM DiagonalTallyAllocation
open scoped BigOperators

variable {T dim digits w reserve axes groups cap : ℕ} (fields : PositiveFields reserve axes groups cap T dim digits)
    {t : Fin T} {rows : Fin T → Fin dim → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {state : Bank w} {mem : Memory w} (receipt : FinishInput t rows digits pub mac state mem fields.tallyWords)

/-- The actual native serializer destination, common to every accepted
operand list fitting the reserved arena. -/
def FinishInput.outputBase := receipt.post.localBase+dim+T*dim+dim+dim+1

/-- For canonical transmitted subtotals, the real native suffix has one
chronological positive return and writes the true current-owner totals. -/
theorem FinishInput.canonical_run (honest : fields.subtotals=canonicalSubtotals digits rows)
    (small : ∀ i c, rows i c < 2^digits) (sumFit : ∀ c,(∑ i, rows i c) < 2^w) :
    ∃ z : Returns (finishExpansion signedOccurrences) pub mac state mem,
      let arena := receipt.post.arenaFor receipt.operands.length receipt.raw dim T t.val digits
      traceCost z.val.1 ≤ traceCost receipt.earlier+(alignTallies.slots+allocateTallies.slots+arena.work w receipt.operands) ∧
      (∀ e∈z.val.1,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin dim, ∀ j<w, z.val.2.2 (receipt.outputBase fields+(c.val*w+j)) =
        word w (((∑ i,rows i c).testBit j).toNat) := by
  have canonical : fields.tallyWords=broadcast digits rows := by
    change splitFields digits (T*dim) (List.ofFn fields.subtotals)=_
    rw [honest,ofFn_canonicalSubtotals,splitFields_broadcast]
  exact receipt.complete canonical small sumFit


/-- Chronological successful execution with its real signed event trace, cost,
fixed output address and specified natural column values. -/
def FinishInput.ColumnRun (column : Fin dim → ℕ) : Prop :=
    ∃ z : Returns (finishExpansion signedOccurrences) pub mac state mem,
      let arena := receipt.post.arenaFor receipt.operands.length receipt.raw dim T t.val digits
      traceCost z.val.1 ≤ traceCost receipt.earlier+(alignTallies.slots+allocateTallies.slots+arena.work w receipt.operands) ∧
      (∀ e∈z.val.1,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin dim, ∀ j<w, z.val.2.2 (receipt.outputBase fields+(c.val*w+j)) =
        word w (((column c).testBit j).toNat)

/-- The selected returned memory reads the binary digit of its real column
at the fixed address reserved by the input arena. -/
def FinishInput.ColumnBit (column : Fin dim → ℕ) (z : Returns (finishExpansion signedOccurrences) pub mac state mem)
    (c : Fin dim) (j : ℕ) : Prop :=
  z.val.2.2 (receipt.outputBase fields+(c.val*w+j)) = word w (((column c).testBit j).toNat)

/-- The canonical native return written at its exact fixed address, with a
caller-specified column total proved equal to the actual current-owner sum. -/
theorem FinishInput.column_run (honest : fields.subtotals=canonicalSubtotals digits rows)
    (small : ∀ i c, rows i c < 2^digits) (sumFit : ∀ c,(∑ i, rows i c) < 2^w)
    (column : Fin dim → ℕ) (totals : ∀ c, (∑ i,rows i c)=column c) :
    receipt.ColumnRun fields column := by
  obtain ⟨z,cost,positive,out⟩ := receipt.canonical_run fields honest small sumFit
  exact ⟨z,cost,positive,fun c j hj => (out c j hj).trans (congrArg (fun x : ℕ => word w (x.testBit j).toNat) (totals c))⟩

/-- A caller's arbitrary returned suffix has the same serialized columns as
the canonical native run from its initial post-cell state. -/
theorem FinishInput.column_bits (honest : fields.subtotals=canonicalSubtotals digits rows)
    (small : ∀ i c, rows i c < 2^digits) (sumFit : ∀ c,(∑ i, rows i c) < 2^w)
    (column : Fin dim → ℕ) (totals : ∀ c, (∑ i,rows i c)=column c)
    (z : Returns (finishExpansion signedOccurrences) pub mac state mem) (c : Fin dim) (j : ℕ) (hj : j<w) :
    receipt.ColumnBit fields column z c j := by
  obtain ⟨u,_,_,out⟩ := receipt.column_run fields honest small sumFit column totals
  exact (finish_eq u z) ▸ out c j hj

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI
