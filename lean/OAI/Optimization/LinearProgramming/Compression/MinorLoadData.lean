import OAI.Optimization.LinearProgramming.RAM.Code
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! A memory layout for loading a selected square submatrix. Address registers 0–5 hold its
parameters, 6–15 are scratch, and the row and column index arrays begin at 16 or above. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

structure Layout (K : Type*) where
  m : ℕ
  n : ℕ
  k : ℕ
  src : ℕ
  dst : ℕ
  rowArray : ℕ
  colArray : ℕ
  matrix : Matrix (Fin m) (Fin n) K
  row : Fin k → Fin m
  col : Fin k → Fin n
  src_pos : 0 < src
  disjoint : src + m * n ≤ dst
  rowArray_ge : 16 ≤ rowArray
  colArray_ge : 16 ≤ colArray

variable {K : Type*} (v : Layout K)

/-- The input in the two RAM register banks. This accepts arbitrary selections, hence also
the sorted distinct selections used for minor requests. -/
structure Input (s : Memory K) : Prop where
  src : s.index 0 = v.src
  width : s.index 1 = v.n
  order : s.index 2 = v.k
  rowBase : s.index 3 = v.rowArray
  colBase : s.index 4 = v.colArray
  out : s.index 5 = v.dst
  rows : ∀ i, s.index (v.rowArray + i.val) = (v.row i).val
  cols : ∀ i, s.index (v.colArray + i.val) = (v.col i).val
  source : ∀ i j, s.data (v.src + i.val * v.n + j.val) = v.matrix i j

/-- All original registers outside the documented scratch and output retain their values. -/
structure Frame (s t : Memory K) : Prop where
  index : ∀ a, a < 6 ∨ 16 ≤ a → t.index a = s.index a
  data : ∀ a, a ≠ 0 → a < v.dst ∨ v.dst + v.k * v.k ≤ a → t.data a = s.data a

variable {v}

theorem Frame.refl (s : Memory K) : Frame v s s := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem Frame.putIndex {s t : Memory K} (h : Frame v s t) {a : ℕ} (lo : 6 ≤ a) (hi : a < 16)
    (x : ℕ) : Frame v s (t.putIndex a x) := by
  refine ⟨?_, h.data⟩
  intro r hr
  simpa [Memory.putIndex, Function.update_of_ne (show r ≠ a by omega)] using h.index r hr

theorem Frame.cellAddress {s t u : Memory K} (h : Frame v s t)
    (hd : u.data = t.data) (hi : ∀ r, r ≠ 12 → r ≠ 13 → r ≠ 14 → u.index r = t.index r) :
    Frame v s u := by
  refine ⟨fun r hr => (hi r (by omega) (by omega) (by omega)).trans (h.index r hr), ?_⟩
  intro a ha he
  rw [hd]; exact h.data a ha he

theorem Frame.putTemp {s t : Memory K} (h : Frame v s t) (x : K) : Frame v s (t.putData 0 x) := by
  refine ⟨h.index, ?_⟩
  intro a ha he
  simpa [Memory.putData, Function.update_of_ne ha] using h.data a ha he

theorem Frame.putOutput {s t : Memory K} (h : Frame v s t) {w : ℕ} (hw : w < v.k*v.k)
    (x : K) : Frame v s (t.putData (v.dst + w) x) := by
  refine ⟨h.index, ?_⟩
  intro a ha he
  simpa [Memory.putData, Function.update_of_ne (show a ≠ v.dst+w by omega)] using h.data a ha he

theorem flat_lt {a b m n : ℕ} (ha : a < m) (hb : b < n) : a*n+b < m*n := calc
  _ < (a+1)*n := by rw [Nat.succ_mul]; omega
  _ ≤ m*n := Nat.mul_le_mul_right _ ha

theorem flat_injective {k : ℕ} {a b i j : Fin k} (h : a.val*k+b.val = i.val*k+j.val) :
    a = i ∧ b = j := by
  have ha : a.val = i.val := by
    rcases lt_trichotomy a.val i.val with hlt | eq | hgt
    · have hh := flat_lt hlt b.isLt
      omega
    · exact eq
    · have hh := flat_lt hgt j.isLt
      omega
  obtain rfl := Fin.ext ha
  exact ⟨rfl, Fin.ext (Nat.add_left_cancel h)⟩

theorem Input.of_frame {s t : Memory K} (h : Input v s) (hs : Frame v s t) : Input v t := by
  refine ⟨(hs.index 0 (by decide)).trans h.src, (hs.index 1 (by decide)).trans h.width,
    (hs.index 2 (by decide)).trans h.order, (hs.index 3 (by decide)).trans h.rowBase,
    (hs.index 4 (by decide)).trans h.colBase, (hs.index 5 (by decide)).trans h.out, ?_, ?_, ?_⟩
  · intro i
    exact (hs.index _ (.inr (v.rowArray_ge.trans (Nat.le_add_right ..)))).trans (h.rows i)
  · intro i
    exact (hs.index _ (.inr (v.colArray_ge.trans (Nat.le_add_right ..)))).trans (h.cols i)
  · intro i j
    have hj := flat_lt i.isLt j.isLt
    have hz := v.src_pos
    have he := v.disjoint
    exact (hs.data _ (by omega) (Or.inl (by omega))).trans (h.source i j)

/-- A rectangular row-major prefix of the destination has obtained its final values. -/
def Copied (v : Layout K) (s : Memory K) (w : ℕ) : Prop := ∀ i j : Fin v.k,
  i.val*v.k+j.val < w → s.data (v.dst+(i.val*v.k+j.val)) = v.matrix (v.row i) (v.col j)

theorem Copied.zero (s : Memory K) : Copied v s 0 := fun _ _ h => (Nat.not_lt_zero _ h).elim

theorem Copied.of_data_eq {s t : Memory K} {w : ℕ} (h : Copied v s w) (he : t.data = s.data) :
    Copied v t w := fun i j hi => by rw [he]; exact h i j hi

theorem Copied.putTemp {s : Memory K} {w : ℕ} (h : Copied v s w) (x : K) :
    Copied v (s.putData 0 x) w := by
  intro i j hi
  have hD := v.disjoint
  have hS := v.src_pos
  simpa [Memory.putData, Function.update_of_ne (show v.dst + (i.val*v.k+j.val) ≠ 0 by omega)]
    using h i j hi

theorem Copied.putNext {s : Memory K} (i j : Fin v.k) (h : Copied v s (i.val*v.k+j.val)) :
    Copied v (s.putData (v.dst+(i.val*v.k+j.val)) (v.matrix (v.row i) (v.col j)))
      (i.val*v.k+j.val+1) := by
  intro a b hab
  by_cases he : a.val*v.k+b.val = i.val*v.k+j.val
  · obtain ⟨rfl, rfl⟩ := flat_injective he
    simp [Memory.putData]
  · have hne : v.dst+(a.val*v.k+b.val) ≠ v.dst+(i.val*v.k+j.val) := by omega
    simpa [Memory.putData, Function.update_of_ne hne] using h a b (by omega)

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
