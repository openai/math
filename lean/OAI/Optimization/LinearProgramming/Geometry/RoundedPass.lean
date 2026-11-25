import OAI.Optimization.LinearProgramming.Geometry.RowRAM
import OAI.Optimization.LinearProgramming.Geometry.PivotCellRAM
import OAI.Optimization.LinearProgramming.Geometry.Pivot

/-! A complete RAM pass returning the same signed row as the adaptive pivot stage. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace RowRAM

open RAM RAM.Block SignType

/-- The signed cell written at output address `m.index 8 + j`. -/
def packedValue (m : Memory ℚ) (B j : ℕ) : ℚ :=
  let start := m.index 7 + 3*j
  (sign (m.data 21) : ℚ) * (sign (m.data start) : ℚ) *
    roundedPower (m.data (start+1) - m.data (start+2) - m.data 22) B

/-- Width of the source data actually used by one cell. It can stay fixed even as
unrelated scratch registers accumulate during successive pivot rows. -/
structure PackedWidth (m : Memory ℚ) (L : ℕ) : Prop where
  pivot : ratBits (m.data 21) ≤ L
  best : ratBits (m.data 22) ≤ L
  triple (j : ℕ) : j < m.index 9 → ∀ q < 3, ratBits (m.data (m.index 7+3*j+q)) ≤ L

theorem PackedWidth.of_within {m : Memory ℚ} {L : ℕ} (hm : Within L m) : PackedWidth m L :=
  ⟨hm _, hm _, fun _ _ _ _ => hm _⟩

/-- The first maximum and all actual input triples are already in registers.
The fixed second pass has no external calls, and includes every rounded cell calculation,
write and traversal instruction. -/
theorem signed_pass_localWidth (m : Memory ℚ) (H L B : ℕ) (hm : Within H m) (hw : PackedWidth m L) (hb : m.index 6 = B)
    (hpivot : m.data 21 ≠ 0)
    (hmax : ∀ j < m.index 9, m.data (m.index 7+3*j) ≠ 0 →
      m.data (m.index 7+3*j+1) - m.data (m.index 7+3*j+2) ≤ m.data 22)
    (hi : 27 ≤ m.index 7) (ho : 27 ≤ m.index 8)
    (hsep : m.index 7+3*m.index 9 ≤ m.index 8 ∨ m.index 8+m.index 9 ≤ m.index 7) :
    ∃ t k, k ≤ m.index 9*(32*B+181)+4 ∧
      Eval (Within (H+m.index 9*PowerRAM.signedWidth 0 L B)) (pass PowerRAM.signedBlock) m k t ∧
      (∀ j < m.index 9, t.data (m.index 8+j) = packedValue m B j) ∧
      (∀ i, 27 ≤ i → (i < m.index 8 ∨ m.index 8+m.index 9 ≤ i) → t.data i = m.data i) ∧
      (∀ i, 6 ≤ i → i ≠ 10 → i ≠ 11 → i ≠ 12 → t.index i = m.index i) := by
  let C := PowerRAM.signedWidth 0 L B
  apply pass_eval PowerRAM.signedBlock m H C (32*B+170) (packedValue m B) hm hi ho hsep
  intro j hj u hu u6 u21 u22 u23 u24 u25
  have hθ : u.data 23 ≠ 0 → u.data 24-u.data 25 ≤ u.data 22 := by
    simpa only [u23,u24,u25,u22] using hmax j hj
  have localBound (r : ℕ) (hr : 21 ≤ r) (hr' : r ≤ 25) : ratBits (u.data r) ≤ L := by
    interval_cases r
    · simpa only [u21] using hw.pivot
    · simpa only [u22] using hw.best
    · simpa only [u23, Nat.add_zero] using hw.triple j hj 0 (by decide)
    · simpa only [u24] using hw.triple j hj 1 (by decide)
    · simpa only [u25] using hw.triple j hj 2 (by decide)
  obtain ⟨v,k,hk,run,out,frame⟩ := PowerRAM.run_signedBlock u (H+j*C) L B (u6.trans hb) (u21 ▸ hpivot) hθ hu localBound
  have widthEq : PowerRAM.signedWidth (H+j*C) L B = H+(j+1)*C := by rw [PowerRAM.signedWidth_additive]; ring
  rw [widthEq] at run
  refine ⟨v,k,hk,run,?_,⟨fun r hr => frame.data r (by omega) (by omega),fun r hr => frame.index r (by omega)⟩⟩
  simpa only [packedValue,u21,u22,u23,u24,u25] using out

/-- The second-pass RAM output agrees coordinatewise with the row passed to the Gram
projector, including the exact pivot and all zero entries. -/
theorem signed_pass_matches_localWidth {n : ℕ} (row : PivotRow n) (price : Fin n → ℚ)
    (m : Memory ℚ) (H L B : ℕ) (hm : Within H m) (hw : PackedWidth m L) (hb : m.index 6=B) (hn : m.index 9=n)
    (hpivot : m.data 21 = row.raw row.pivot) (hbest : m.data 22 = row.logs row.pivot-price row.pivot)
    (hnz : row.raw row.pivot ≠ 0) (hmax : ∀ j, row.raw j ≠ 0 → row.logs j-price j ≤ row.logs row.pivot-price row.pivot)
    (hr : ∀ j : Fin n, m.data (m.index 7+3*j.val) = row.raw j)
    (hl : ∀ j : Fin n, m.data (m.index 7+3*j.val+1) = row.logs j)
    (ht : ∀ j : Fin n, m.data (m.index 7+3*j.val+2) = price j)
    (hi : 27 ≤ m.index 7) (ho : 27 ≤ m.index 8)
    (hsep : m.index 7+3*n ≤ m.index 8 ∨ m.index 8+n ≤ m.index 7) :
    ∃ u k, k ≤ n*(32*B+181)+4 ∧
      Eval (Within (H+n*PowerRAM.signedWidth 0 L B)) (pass PowerRAM.signedBlock) m k u ∧
      (∀ j : Fin n, u.data (m.index 8+j.val) = row.rounded price B j) ∧
      (∀ i, 27 ≤ i → (i < m.index 8 ∨ m.index 8+n ≤ i) → u.data i = m.data i) ∧
      (∀ i, 6 ≤ i → i ≠ 10 → i ≠ 11 → i ≠ 12 → u.index i = m.index i) := by
  obtain ⟨u,k,hk,run,out,hframe,iframe⟩ := signed_pass_localWidth m H L B hm hw hb (hpivot ▸ hnz) (by
    intro j hj
    let p : Fin n := ⟨j,hn ▸ hj⟩
    rw [hr p,hl p,ht p,hbest]
    exact hmax p) hi ho (hn ▸ hsep)
  refine ⟨u,k,hn ▸ hk,hn ▸ run,?_,hn ▸ hframe,iframe⟩
  intro j
  rw [out _ (hn ▸ j.isLt)]
  simp [packedValue,PivotRow.rounded,pivotRound,hpivot,hbest,hr j,hl j,ht j]

/-- A single incoming bit bound also bounds the local data. -/
theorem signed_pass_matches {n : ℕ} (row : PivotRow n) (price : Fin n → ℚ)
    (m : Memory ℚ) (H B : ℕ) (hm : Within H m) (hb : m.index 6=B) (hn : m.index 9=n)
    (hpivot : m.data 21 = row.raw row.pivot) (hbest : m.data 22 = row.logs row.pivot-price row.pivot)
    (hnz : row.raw row.pivot ≠ 0) (hmax : ∀ j, row.raw j ≠ 0 → row.logs j-price j ≤ row.logs row.pivot-price row.pivot)
    (hr : ∀ j : Fin n, m.data (m.index 7+3*j.val) = row.raw j)
    (hl : ∀ j : Fin n, m.data (m.index 7+3*j.val+1) = row.logs j)
    (ht : ∀ j : Fin n, m.data (m.index 7+3*j.val+2) = price j)
    (hi : 27 ≤ m.index 7) (ho : 27 ≤ m.index 8)
    (hsep : m.index 7+3*n ≤ m.index 8 ∨ m.index 8+n ≤ m.index 7) :
    ∃ u k, k ≤ n*(32*B+181)+4 ∧
      Eval (Within (H+n*PowerRAM.signedWidth 0 H B)) (pass PowerRAM.signedBlock) m k u ∧
      (∀ j : Fin n, u.data (m.index 8+j.val) = row.rounded price B j) ∧
      (∀ i, 27 ≤ i → (i < m.index 8 ∨ m.index 8+n ≤ i) → u.data i = m.data i) ∧
      (∀ i, 6 ≤ i → i ≠ 10 → i ≠ 11 → i ≠ 12 → u.index i = m.index i) :=
  signed_pass_matches_localWidth row price m H H B hm (PackedWidth.of_within hm) hb hn hpivot hbest
    hnz hmax hr hl ht hi ho hsep

end RowRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
