import OAI.Optimization.LinearProgramming.Compression.ServiceCanonicalWords
import OAI.Optimization.LinearProgramming.Compression.MinorLoadInput
import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import Mathlib.Data.List.OfFn

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM OracleSpec MinorLoad

variable {K : Type*} {d e n : ℕ}

/-- Row-major interpretation of the two original matrices inside the running service. -/
structure MatrixBank (D : Matrix (Fin d) (Fin n) K) (E : Matrix (Fin e) (Fin n) K) (s : Memory K) : Prop where
  left : ∀ (i : Fin d) (j : Fin n),s.data (7+i.val*n+j.val) = D i j
  right : ∀ (i : Fin e) (j : Fin n),s.data (7+d*n+i.val*n+j.val) = E i j

private theorem entries_flat {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℚ) :
    MinorLog.entries A = List.ofFn (fun x : Fin (d*n) => matrixCell A x.val) := by
  rw [List.ofFn_mul]
  simp [MinorLog.entries,matrixCell_at]

/-- The native matrix-bank interpretation follows directly from the public input list. -/
theorem MatrixBank.of_public (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (s : Memory ℚ) (hdim : d+e = n)
    (h : ∀ j < n*n,s.data (7+j) = (MinorLog.entries D++MinorLog.entries E)[j]?.getD 0) : MatrixBank D E s := by
  have len : n*n = d*n+e*n := by rw [←Nat.add_mul,hdim]
  constructor
  · intro i j
    have hb := flat_lt i.isLt j.isLt
    have hx := h (i.val*n+j.val) (by omega)
    rw [entries_flat, List.getElem?_append_left (by simpa using hb),List.getElem?_ofFn,dite_eq_left hb] at hx
    simpa [Nat.add_assoc,matrixCell_at] using hx
  · intro i j
    have hb := flat_lt i.isLt j.isLt
    have hx := h (d*n+(i.val*n+j.val)) (by omega)
    rw [entries_flat D,entries_flat E,List.getElem?_append_right (by simp),List.length_ofFn,
      Nat.add_sub_cancel_left,List.getElem?_ofFn,dite_eq_left hb] at hx
    simpa [Nat.add_assoc,matrixCell_at] using hx

theorem MatrixBank.frame {D : Matrix (Fin d) (Fin n) K} {E : Matrix (Fin e) (Fin n) K}
    {s t : Memory K} (h : MatrixBank D E s) (hdim : d+e = n)
    (fr : ∀ a,7 ≤ a → a < tableBase n → t.data a = s.data a) : MatrixBank D E t := by
  have hlen : n*n = d*n+e*n := by rw [←Nat.add_mul,hdim]
  constructor
  · intro i j
    have hb := flat_lt i.isLt j.isLt
    exact (fr _ (by omega) (by unfold tableBase; omega)).trans (h.left i j)
  · intro i j
    have hb := flat_lt i.isLt j.isLt
    exact (fr _ (by omega) (by unfold tableBase; omega)).trans (h.right i j)

/-- The determinant argument uses the real request cursor and two fresh work buffers
above both the old generator table and the staged candidate. -/
def serviceLayout (D : Matrix (Fin d) (Fin n) K) (E : Matrix (Fin e) (Fin n) K)
    (u : PairMinorIndex d e n) (g base : ℕ) (hdim : d+e = n) (hb : 40 ≤ base) : Layout K :=
  let v := pairLayout D E u
  { v with
    dst := slotBase n (g+2)+4
    rowArray := base+2
    colArray := base+2+order u
    disjoint := v.disjoint.trans (by
      have hv : v.dst = 7+(d+e)*n := by cases u <;> rfl
      rw [hv,hdim]
      unfold slotBase tableBase
      omega)
    rowArray_ge := by omega
    colArray_ge := by omega }

structure DetParameters (u : PairMinorIndex d e n) (g : ℕ) (s : Memory K) : Prop where
  src : s.index 0 = (if tag u = 0 then 7 else 7+d*n)
  width : s.index 1 = n
  size : s.index 2 = order u
  row : s.index 3 = s.index 40+2
  col : s.index 4 = s.index 40+2+order u
  out : s.index 5 = slotBase n (g+2)+4
  saved : s.index 30 = slotBase n (g+2)

theorem DetParameters.frame {u : PairMinorIndex d e n} {g : ℕ} {s t : Memory K} (h : DetParameters u g s)
    (idx : ∀ a,a < 8 ∨ 12 ≤ a → t.index a = s.index a) : DetParameters u g t :=
  ⟨(idx _ (by decide)).trans h.src,(idx _ (by decide)).trans h.width,(idx _ (by decide)).trans h.size,
    by rw [idx 3 (by decide),idx 40 (by decide),h.row],by rw [idx 4 (by decide),idx 40 (by decide),h.col],
    (idx _ (by decide)).trans h.out,(idx _ (by decide)).trans h.saved⟩

theorem detInput {D : Matrix (Fin d) (Fin n) K} {E : Matrix (Fin e) (Fin n) K}
    (u : PairMinorIndex d e n) (g : ℕ) (s : Memory K) (hdim : d+e = n)
    (h : DetParameters u g s) (w : Wire u s) (M : MatrixBank D E s) :
    Input (serviceLayout D E u g (s.index 40) hdim w.base) s := by
  rcases u with ⟨k,r,c⟩ | ⟨k,r,c⟩
  · refine ⟨h.src,h.width,h.size,h.row,h.col,h.out,?_,?_,M.left⟩
    · intro i
      have hi : i.val < k.val := i.isLt
      change s.index (s.index 40+2+i.val) = (r ⟨i.val,hi⟩).val
      simpa only [rowWord,dite_eq_left hi] using w.rows i.val hi
    · intro i
      have hi : i.val < k.val := i.isLt
      change s.index (s.index 40+2+k.val+i.val) = (c ⟨i.val,hi⟩).val
      simpa only [order,colWord,dite_eq_left hi] using w.cols i.val hi
  · refine ⟨h.src,h.width,h.size,h.row,h.col,h.out,?_,?_,M.right⟩
    · intro i
      have hi : i.val < k.val := i.isLt
      change s.index (s.index 40+2+i.val) = (r ⟨i.val,hi⟩).val
      simpa only [rowWord,dite_eq_left hi] using w.rows i.val hi
    · intro i
      have hi : i.val < k.val := i.isLt
      change s.index (s.index 40+2+k.val+i.val) = (c ⟨i.val,hi⟩).val
      simpa only [order,colWord,dite_eq_left hi] using w.cols i.val hi

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
