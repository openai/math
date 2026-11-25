import OAI.Optimization.LinearProgramming.Compression.ServiceState

/-! Exact live bounds for the original matrices and the currently stored sorted rows.
Scratch scalars above the last live row have no prescribed value. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open RAM GeneratorTable

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}

theorem slot_word_lt_end (n : ℕ) {i g j : ℕ} (hi : i < g) (hj : j < stride n) :
    slotBase n i+j < slotBase n g := by
  calc
    slotBase n i+j < slotBase n i+stride n := Nat.add_lt_add_left hj _
    _ = slotBase n (i+1) := by unfold slotBase; rw [Nat.succ_mul]; omega
    _ ≤ slotBase n g := Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _

theorem GeneratorTable.Stored.keep_live {keys : List (NonzeroPairMinor D E)} {s t : Memory ℚ}
    (h : Stored D E keys s) (hc : t.data 4=s.data 4)
    (frame : ∀ i, 7 ≤ i → i < slotBase n keys.length → t.data i=s.data i) :
    Stored D E keys t := by
  refine ⟨h.sorted,hc.trans h.count,?_⟩
  intro i
  exact (h.slots i).transfer (fun j hj => frame _ (by unfold slotBase tableBase; omega)
    (slot_word_lt_end n i.isLt hj))

theorem Persistent.withTable {J J' : Finset (NonzeroPairMinor D E)} {H : ℕ} {s t : Memory ℚ}
    (h : Persistent D E J H s) (header : ∀ i, 1 ≤ i → i ≤ 3 → t.data i=s.data i)
    (matrix : ∀ i, 7 ≤ i → i < tableBase n → t.data i=s.data i)
    (rows : Stored D E J'.sort t) (hb : ∀ i, ratBits (t.data i) ≤ H) :
    Persistent D E J' H t := by
  refine ⟨(header 1 (by decide) (by decide)).trans h.leftRows,
    (header 2 (by decide) (by decide)).trans h.rightRows,
    (header 3 (by decide) (by decide)).trans h.columns,?_,rows,hb⟩
  intro j hj
  exact (matrix _ (by omega) (by unfold tableBase; omega)).trans (h.entries j hj)

/-- Preserving the finite live scalar segment suffices when computing a nonrestart
response. Temporary scalar arrays may be allocated above it. -/
theorem Persistent.keep_prefix {J : Finset (NonzeroPairMinor D E)} {H : ℕ} {s t : Memory ℚ}
    (h : Persistent D E J H s)
    (frame : ∀ i, i < slotBase n J.card → i ≠ 0 → i ≠ 5 → i ≠ 6 → t.data i=s.data i)
    (hb : ∀ i, ratBits (t.data i) ≤ H) : Persistent D E J H t := by
  have hbase : 7 ≤ tableBase n := by unfold tableBase; omega
  have hend : tableBase n ≤ slotBase n J.card := Nat.le_add_right _ _
  apply h.withTable (fun i h1 h3 => frame _ (by omega) (by omega) (by omega) (by omega))
    (fun i hi hi' => frame _ (by omega) (by omega) (by omega) (by omega)) _ hb
  apply h.generators.keep_live (frame 4 (by omega) (by decide) (by decide) (by decide))
  intro i hi hlo
  rw [Finset.length_sort] at hlo
  exact frame i hlo (by omega) (by omega) (by omega)

end Compression
end LinearProgramming
end Optimization
end OAI
