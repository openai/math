import OAI.Optimization.LinearProgramming.Geometry.BorderBatchInput
import OAI.Optimization.LinearProgramming.Geometry.BorderPackedState

/-! Frame and width proofs for completed geometric border batches. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
open RAM
variable {r n B : ℕ}

private theorem belowHeaders (L : Layout r n) : 256 ≤ L.headers := L.pivots_ge.trans ((Nat.le_add_right _ _).trans L.pivots_end)

/-- Reconstitute the prefix invariant from exactly its live public addresses and the
previously committed rounded rows. The descriptor and triple tapes can be overwritten. -/
theorem stored_after_border_frame {a : ℕ} {L : Layout r n} {base m t : Memory ℚ} {D : Matrix (Fin r) (Fin n) ℚ}
    {price : Fin n → ℚ} {rows : Fin a → PivotRow n} (input : Inputs L D price B base)
    (old : PivotPrefixRAM.Stored base m rows price B) (ha : a ≤ r)
    (idx : ∀ p, 128≤p → p<L.headers → p≠139 → t.index p=m.index p)
    (data : ∀ p, L.rounded≤p → p<L.answers → t.data p=m.data p) : PivotPrefixRAM.Stored base t rows price B := by
  have high := belowHeaders L
  have bp : base.index 136=L.pivots := input.initial.pivotAddr
  have br : base.index 134=L.rounded := input.initial.roundedAddr
  refine ⟨(idx _ (by decide) (by omega) (by decide)).trans old.length,
    (idx _ (by decide) (by omega) (by decide)).trans old.rowCursor,
    (idx _ (by decide) (by omega) (by decide)).trans old.pivotCursor,?_,?_,?_⟩
  · intro i lo hi h135 h137 h139
    exact (idx _ (by omega) (by omega) h139).trans (old.permanent i lo hi h135 h137 h139)
  · intro i
    have hp := L.pivots_ge; have he := L.pivots_end; have hi := i.isLt
    exact (idx _ (by omega) (by omega) (by omega)).trans (old.pivots i)
  · intro i j
    have off : i.val*n+j.val<r*n := matrixOffset_lt (Fin.castLE ha i) j
    have he := L.rounded_end
    exact (data _ (by omega) (by omega)).trans (old.rounded i j)

theorem rows_after_scan {a : ℕ} {L : Layout r n} {base m t : Memory ℚ} {D : Matrix (Fin r) (Fin n) ℚ}
    {price : Fin n → ℚ} {rows : Fin a → PivotRow n} (input : Inputs L D price B base)
    (old : PivotPrefixRAM.Stored base m rows price B) (ha : a ≤ r) (keep : PreservesInput L base m)
    (frame : ScanFrame L m t) : PivotPrefixRAM.Stored base t rows price B ∧ PreservesInput L base t := by
  have sg := L.source_ge; have sp := L.source_end; have lp := L.prices_end; have lt' := L.triples_end
  have la := L.rounded_end; have ls := L.answers_end
  constructor
  · exact stored_after_border_frame input old ha (fun _ lo _ no => frame.indices _ lo no)
      (fun _ lo hi => frame.data _ (by omega) (by omega) (Or.inr (by omega)))
  · intro p lo hi; exact (frame.data p lo (by omega) (Or.inl hi)).trans (keep p lo hi)

/-- Put a completed streaming scan directly into the three-word representation of
one rational pivot row. Value zero is also covered on the skipped-minor branch. -/
theorem packed_of_scan {k e g : ℕ} {L : Layout r n} {D : Matrix (Fin (k+1)) (Fin n) ℚ} {J : Fin k → Fin n}
    {price : Fin n → ℚ} {o t : Memory ℚ} {values : Fin n → ℚ} {row : PivotRow n}
    (ready : ScanReady L o (borderedMinor D J) price (fun q => ratBits q ≤ max 3 g) n values t)
    (base : t.index 133=L.triples) (raw : row.raw=borderedMinor D J) (logs : row.logs=values)
    (kbound : k+1≤n) (hmat : ∀ i j, ratBits (D i j) ≤ e) (hprice : ∀ j, ratBits (price j) ≤ e) :
    PivotPrefixRAM.PackedRow t row price (batchLocalWidth n e g) := by
  have cell (j : Fin n) := ready.cells j j.isLt
  constructor
  · intro j; rw [base,raw]; exact (cell j).first
  · intro j; rw [base,logs]; exact (cell j).second
  · intro j; rw [base]; exact (cell j).third
  · intro j q hq; rw [base]
    have hr := minor_width D J kbound hmat j
    have hv := ready.bounded j
    have hp := hprice j
    interval_cases q
    · rw [Nat.add_zero,(cell j).first]; dsimp [batchLocalWidth]; omega
    · rw [(cell j).second]; dsimp [batchLocalWidth]; omega
    · rw [(cell j).third]; dsimp [batchLocalWidth]; omega

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
