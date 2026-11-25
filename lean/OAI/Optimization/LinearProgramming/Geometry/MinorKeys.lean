import OAI.Optimization.LinearProgramming.Compression.MinorIndex
import OAI.Optimization.LinearProgramming.Geometry.Circuits
import Mathlib.Data.Finset.Sort

/-! Canonical indices for querying signed prefix minors by their unordered column sets. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Finset
open scoped Matrix

variable {k r n : ℕ}

/-- The compression oracle indexes a square minor by its sorted row and column sets.
A prefix request can be malformed only before the determinant has been tested. -/
def canonicalPrefixIndex (r : ℕ) (key : ℕ × Finset (Fin n)) :
    Option (Compression.SquareMinorIndex r n) :=
  if h : key.1 ≤ r ∧ key.2.card = key.1 then
    let hn : key.1 ≤ n := by simpa only [← h.2, Fintype.card_fin] using key.2.card_le_univ
    some ⟨⟨key.1, Nat.lt_succ_of_le hn⟩, Fin.castLEOrderEmb h.1, key.2.orderEmbOfFin h.2⟩
  else none

def prefixMinorKey (J : Fin k → Fin n) (j : Fin n) : ℕ × Finset (Fin n) :=
  (k+1, insert j (univ.image J))

/-- Reordering a list of columns while preserving its underlying set only changes
the determinant by a sign. -/
theorem abs_det_sorted_columns {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Matrix (Fin k) (Fin n) K) (col : Fin k → Fin n) (S : Finset (Fin n))
    (hS : ∀ i, col i ∈ S) (hcard : S.card = k) (hc : Function.Injective col) :
    |(A.submatrix id col).det| = |(A.submatrix id (S.orderEmbOfFin hcard)).det| := by
  let order := S.orderIsoOfFin hcard
  let p (i : Fin k) : Fin k := order.symm ⟨col i, hS i⟩
  have hp (i) : S.orderEmbOfFin hcard (p i) = col i := by
    change (order (order.symm ⟨col i, hS i⟩)).val = _
    simp
  have hinj : Function.Injective p := fun i j hij => hc ((hp i).symm.trans ((congrArg _ hij).trans (hp j)))
  let e := Equiv.ofBijective p hinj.bijective_of_finite
  let M := A.submatrix id (S.orderEmbOfFin hcard)
  have hperm : A.submatrix id col = M.submatrix id e := by
    ext i j
    change A i (col j) = A i (S.orderEmbOfFin hcard (p j))
    rw [hp]
  rw [hperm, Matrix.det_permute', abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs, M]

/-- All entries of the ordered prefix determinant, including ones from repeated
indices, fold into the same unordered column set. -/
theorem image_lastCases (J : Fin k → Fin n) (j : Fin n) :
    univ.image (Fin.lastCases j J) = insert j (univ.image J) := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · left; simp
    · right; exact ⟨i, by simp⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last k, by simp⟩
    · exact ⟨i.castSucc, by simp⟩

/-- Every nonzero candidate at a pivot stage corresponds to an admissible sorted minor,
and its magnitude agrees exactly with that minor. -/
theorem canonicalPrefixIndex_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Matrix (Fin r) (Fin n) K) (hr : k + 1 ≤ r) (J : Fin k → Fin n) (j : Fin n)
    (hnz : circuitMinor (A.submatrix (Fin.castLE hr) id) J j ≠ 0) :
    ∃ u : Compression.SquareMinorIndex r n,
      canonicalPrefixIndex r (prefixMinorKey J j) = some u ∧
      |(A.submatrix u.2.1 u.2.2).det| = |circuitMinor (A.submatrix (Fin.castLE hr) id) J j| := by
  let col : Fin (k+1) → Fin n := Fin.lastCases j J
  let S := insert j (univ.image J)
  have hinj : Function.Injective col := by
    intro x y he
    by_contra hxy
    apply hnz
    exact Matrix.det_zero_of_column_eq hxy (fun i => congrArg (fun z => A (Fin.castLE hr i) z) he)
  have hcard : S.card = k+1 := by
    rw [show S = univ.image col from (image_lastCases J j).symm]
    simpa using Finset.card_image_of_injective univ hinj
  have hmem (i) : col i ∈ S := by
    rw [show S = univ.image col from (image_lastCases J j).symm]
    exact mem_image_of_mem _ (mem_univ i)
  have hn : k+1 ≤ n := by
    have := S.card_le_univ
    simpa [hcard] using this
  let u : Compression.SquareMinorIndex r n :=
    ⟨⟨k+1, Nat.lt_succ_of_le hn⟩, Fin.castLEOrderEmb hr, S.orderEmbOfFin hcard⟩
  refine ⟨u, ?_, ?_⟩
  · simp [canonicalPrefixIndex, prefixMinorKey, hr, show (insert j (univ.image J)).card = k+1 from hcard, u, S]
  · exact (abs_det_sorted_columns (A.submatrix (Fin.castLE hr) id) col S hmem hcard hinj).symm

/-- A total fixed assignment on prefix queries obtained from a full two-side assignment.
Only the nonzero sorted-minor branch can arise in an actual successful query. -/
noncomputable def prefixAssignment {s : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (f : Compression.NonzeroPairMinor D E → ℚ)
    (key : ℕ × Finset (Fin n)) : ℚ := by
  classical
  exact match canonicalPrefixIndex r key with
  | none => 0
  | some u =>
    if h : Compression.pairMinorValue D E (.inl u) ≠ 0 then f ⟨.inl u, h⟩ else 0

/-- Analogous assignment at the dual price scaling. -/
noncomputable def dualPrefixAssignment {s : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (f : Compression.NonzeroPairMinor D E → ℚ)
    (key : ℕ × Finset (Fin n)) : ℚ := by
  classical
  exact match canonicalPrefixIndex s key with
  | none => 0
  | some u =>
    if h : Compression.pairMinorValue D E (.inr u) ≠ 0 then f ⟨.inr u, h⟩ else 0

/-- True logs of the actual, canonical, nonzero minor magnitudes. -/
noncomputable def pairMinorLog {s : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (u : Compression.NonzeroPairMinor D E) : ℝ :=
  Real.logb 2 |((Compression.pairMinorValue D E u.val : ℚ) : ℝ)|

theorem prefixAssignment_matches {s : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (f : Compression.NonzeroPairMinor D E → ℚ)
    (hr : k+1 ≤ r) (J : Fin k → Fin n) (j : Fin n)
    (hnz : circuitMinor (D.submatrix (Fin.castLE hr) id) J j ≠ 0) :
    ∃ u, f u = prefixAssignment D E f (prefixMinorKey J j) ∧
      pairMinorLog D E u = Real.logb 2 |((circuitMinor (D.submatrix (Fin.castLE hr) id) J j : ℚ) : ℝ)| := by
  obtain ⟨a, ha, he⟩ := canonicalPrefixIndex_spec D hr J j hnz
  have hval : Compression.pairMinorValue D E (.inl a) ≠ 0 := by
    intro hz; change (D.submatrix a.2.1 a.2.2).det = 0 at hz
    exact hnz (abs_eq_zero.mp (he.symm.trans (by rw [hz, abs_zero])))
  refine ⟨⟨.inl a, hval⟩, ?_, ?_⟩
  · simp [prefixAssignment, ha, hval]
  · unfold pairMinorLog
    apply congrArg (Real.logb 2)
    exact_mod_cast he

theorem dualPrefixAssignment_matches {s : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (f : Compression.NonzeroPairMinor D E → ℚ)
    (hr : k+1 ≤ s) (J : Fin k → Fin n) (j : Fin n)
    (hnz : circuitMinor (E.submatrix (Fin.castLE hr) id) J j ≠ 0) :
    ∃ u, f u = dualPrefixAssignment D E f (prefixMinorKey J j) ∧
      pairMinorLog D E u = Real.logb 2 |((circuitMinor (E.submatrix (Fin.castLE hr) id) J j : ℚ) : ℝ)| := by
  obtain ⟨a, ha, he⟩ := canonicalPrefixIndex_spec E hr J j hnz
  have hval : Compression.pairMinorValue D E (.inr a) ≠ 0 := by
    intro hz; change (E.submatrix a.2.1 a.2.2).det = 0 at hz
    exact hnz (abs_eq_zero.mp (he.symm.trans (by rw [hz, abs_zero])))
  refine ⟨⟨.inr a, hval⟩, ?_, ?_⟩
  · simp [dualPrefixAssignment, ha, hval]
  · unfold pairMinorLog
    apply congrArg (Real.logb 2)
    exact_mod_cast he

end Geometry
end LinearProgramming
end Optimization
end OAI
