import OAI.Optimization.LinearProgramming.Geometry.BorderDetRAM
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixContract
import OAI.Optimization.LinearProgramming.Compression.RationalMinorSize

/-! Shared inputs, persistent arrays, and explicit bit envelopes of the actual border batch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Compression Matrix

variable {r n B k : ℕ}

/-- The price and source matrix are stored once. All public address arguments are the
ones read by the descriptor builder, signed-minor service, and pivot prefix program. -/
structure Inputs (L : Layout r n) (D : Matrix (Fin r) (Fin n) ℚ) (price : Fin n → ℚ) (B : ℕ) (base : Memory ℚ) : Prop where
  initial : L.Ready D (Fin.elim0 : Fin 0 → Fin n) (PivotPrefixRAM.initial base)
  precision : base.index 138 = B
  prices (j : Fin n) : base.data (L.prices+j.val) = price j

/-- The original input area persists through all adaptive stages and is available to
later computations regardless of the answers received. -/
def PreservesInput (L : Layout r n) (base m : Memory ℚ) : Prop :=
  ∀ p, 32 ≤ p → p < L.triples → m.data p = base.data p

private theorem source_bounds (L : Layout r n) : 256 ≤ L.triples ∧ 256 ≤ L.rounded ∧ 256 ≤ L.answers ∧ 256 ≤ L.scratch := by
  have := L.source_ge; have := L.source_end; have := L.prices_end; have := L.triples_end
  have := L.rounded_end; have := L.answers_end; omega

/-- Row-major offset lies strictly before the end of the rectangular array. -/
theorem matrixOffset_lt (i : Fin r) (j : Fin n) : i.val*n+j.val<r*n := by
  have capacity : i.val*n+n ≤ r*n := by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right n i.isLt
  have := j.isLt; omega

namespace Inputs
variable {L : Layout r n} {D : Matrix (Fin r) (Fin n) ℚ} {price : Fin n → ℚ} {base m : Memory ℚ}

theorem prefixLayout (h : Inputs L D price B base) : PivotPrefixRAM.Layout base r n B := by
  have triples : base.index 133=L.triples := h.initial.tripleAddr
  have rounded : base.index 134=L.rounded := h.initial.roundedAddr
  have pivots : base.index 136=L.pivots := h.initial.pivotAddr
  obtain ⟨ht,hr,_,_⟩ := source_bounds L
  exact ⟨h.initial.height,h.initial.width,h.precision,triples ▸ ht,rounded ▸ hr,pivots ▸ L.pivots_ge,
    Or.inl (by rw [triples,rounded]; exact L.triples_end)⟩

theorem aux_stable (h : Inputs L D price B base) :
    PivotPrefixRAM.FrameStable base r n (fun m _ => PreservesInput L base m) := by
  intro s t _ frame kept p lo hi
  have out : base.index 134=L.rounded := h.initial.roundedAddr
  have below := L.triples_end
  exact (frame.data p (by omega) (Or.inl (by omega))).trans (kept p lo hi)

theorem ready {rows : Fin k → PivotRow n} (h : Inputs L D price B base) (stored : PivotPrefixRAM.Stored base m rows price B)
    (kept : PreservesInput L base m) : L.Ready D (fun j => (rows j).pivot) m := by
  have ctrl (i : ℕ) (lo : 129 ≤ i) (hi : i ≤ 145) (h135 : i ≠ 135) (h137 : i ≠ 137) (h139 : i ≠ 139) :=
    stored.permanent i lo (by omega) h135 h137 h139
  refine ⟨stored.length,(ctrl 129 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.height,
    (ctrl 130 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.width,
    (ctrl 131 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.sourceAddr,
    (ctrl 132 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.priceAddr,
    (ctrl 133 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.tripleAddr,
    (ctrl 134 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.roundedAddr,
    (ctrl 136 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.pivotAddr,
    (ctrl 140 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.headerAddr,
    (ctrl 141 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.rowAddr,
    (ctrl 142 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.colAddr,
    (ctrl 143 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.answerAddr,
    (ctrl 144 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.scratchAddr,
    (ctrl 145 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.initial.maskAddr,?_,?_⟩
  · intro j; have addr : base.index 136=L.pivots := h.initial.pivotAddr
    rw [← addr,stored.pivots]
  · intro i j
    have off := matrixOffset_lt i j
    have s := L.source_ge; have e := L.source_end; have p := L.prices_end
    exact (kept _ (by omega) (by omega)).trans (h.initial.matrixData i j)

theorem prices_live (h : Inputs L D price B base) (kept : PreservesInput L base m) (j : Fin n) : m.data (L.prices+j.val)=price j := by
  have lo := L.source_ge; have sp := L.source_end; have pt := L.prices_end; have jj := j.isLt
  exact (kept _ (by omega) (by omega)).trans (h.prices j)

end Inputs

/-- The finite output tape can hold each rational determinant, each one-word compressed
answer (with zero on a skipped minor), and the input price. -/
def batchLocalWidth (n E G : ℕ) : ℕ := E+G+(3+n^2+E*n+2*E*n^3)

/-- Only these local widths are added to the caller's previous global register bound. -/
def batchIncrement (n E G : ℕ) : ℕ := detRegisterBits n E+n+G+6

theorem minor_width {n k E : ℕ} (A : Matrix (Fin (k+1)) (Fin n) ℚ) (J : Fin k → Fin n)
    (hn : k+1≤n) (hs : ∀ i j, ratBits (A i j) ≤ E) (j : Fin n) :
    ratBits (borderedMinor A J j) ≤ 3+n^2+E*n+2*E*n^3 := by
  rw [borderedMinor_eq]
  have d := rational_det_bits (A.submatrix id (Fin.lastCases j J)) (fun i c => hs i (Fin.lastCases j J c))
  apply d.trans
  gcongr

theorem addr_width (i : ℕ) : ratBits (i : ℚ) ≤ i+3 := by
  simp only [ratBits,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,show Nat.log2 1=0 by rfl,Nat.add_zero]
  have := Nat.log2_le_self i
  omega

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
