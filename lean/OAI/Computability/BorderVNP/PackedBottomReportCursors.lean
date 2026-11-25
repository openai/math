import OAI.Computability.BorderVNP.PackedBottomBundleHeader

/-! # The weighted-source cursor across a cell's ordered bottom bundles

The cursor advances only by a bundle's actual weighted count times its copy
count. The native equality-row scan and the private evaluator consequently
use the same report bit for every source occurrence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse

/-- Exactly one equality for each element of the private weighted list. -/
@[simp] theorem links_length (base stride copies cursor : ℕ) (ps : List (Port × ℕ)) :
    (links base stride copies cursor ps).length = ps.length := by
  induction ps generalizing cursor with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨p,r⟩; simp [links,ih]

/-- Address of the actual use flag at a row's implicit sidecar rank. -/
theorem links_at (base stride copies cursor : ℕ) (ps : List (Port × ℕ)) (i : Fin ps.length) :
    (links base stride copies cursor ps)[i.val]'(by simp) =
      .equal copies 1 (stagedPort base stride ps[i.val].2) (usePort (cursor+i.val*copies)) := by
  induction ps generalizing cursor with
  | nil => exact i.elim0
  | cons p ps ih =>
    rcases p with ⟨p,r⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [links]
    · simp only [links,Fin.val_succ,List.getElem_cons_succ,ih (cursor+copies) j,Nat.succ_mul]
      congr 2
      omega

private theorem rows_range (f : Writer.Frame) (rel : ℕ → ℕ) (n : ℕ) :
    f.rows rel n = (List.range n).map (fun i => f.equalRow i (rel i)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Writer.Frame.rows,List.range_succ,ih]

/-- Native scalar packet rows are exactly the typed constraints, with the
third field of each decoded immutable sidecar row used as a relative lane. -/
theorem writer_reportRows (f : Writer.Frame) (fs : List Factor) (rel : ℕ → ℕ)
    (hs : f.stride = bottomStride f.orig f.cap)
    (hrel : ∀ i : Fin (positions f.orig fs).length, rel i.val = (positions f.orig fs)[i.val].stagedReportRel) :
    f.rows rel (count fs) ++ [f.zeroRow (count fs)] = reportRows f.base f.orig f.cap f.copies f.useStart fs := by
  unfold reportRows
  congr 1
  · rw [rows_range]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < (sidecar f.orig fs).length := by simpa using hj
      have hk : i < (positions f.orig fs).length := by simpa using hi'
      rw [links_at f.base (bottomStride f.orig f.cap) f.copies f.useStart (sidecar f.orig fs) ⟨i,hi'⟩]
      simp only [List.getElem_map,List.getElem_range,Writer.Frame.equalRow,hs,hrel ⟨i,hk⟩,
        positions,List.getElem_map]
  · simp only [Writer.Frame.zeroRow,padding,hs]

/-- One owned bundle, with its true private immutable source factor list. -/
structure Bundle where
  /-- Public geometry operands read from the six-word array. -/
  header : BundleHeader
  /-- Real one-copy fine factors before staging. -/
  factors : List Factor

/-- The actual report section consumes one bit per expanded weighted source. -/
def Bundle.useBits (s : Bundle) := count s.factors * s.header.copies

/-- Advance past the weighted positions of all preceding bundles in this cell. -/
def nextCursor (start : ℕ) (ss : List Bundle) : ℕ := start+(ss.map Bundle.useBits).sum

/-- Successive stable sublists use adjacent intervals in the use-guess suffix. -/
theorem nextCursor_append (start : ℕ) (xs ys : List Bundle) :
    nextCursor start (xs++ys) = nextCursor (nextCursor start xs) ys := by
  simp [nextCursor,Nat.add_assoc]

/-- A single box consumes precisely its true sidecar count times its multiplicity. -/
theorem nextCursor_cons (start : ℕ) (x : Bundle) (xs : List Bundle) :
    nextCursor start (x::xs) = nextCursor (start+x.useBits) xs := by simp [nextCursor,Nat.add_assoc]

/-- Supplemental records accumulated in the order of the cell's actual bottom sites. -/
def supplements : ℕ → List Bundle → List Record
  | _, [] => []
  | start, x :: xs =>
    reportRows x.header.boxBase x.header.orig x.header.cap x.header.copies start x.factors ++
      supplements (start+x.useBits) xs

/-- Every later bundle begins precisely after all previous expanded weighted uses. -/
theorem supplements_append (start : ℕ) (xs ys : List Bundle) :
    supplements start (xs++ys) = supplements start xs ++ supplements (nextCursor start xs) ys := by
  induction xs generalizing start with
  | nil => simp [supplements,nextCursor]
  | cons x xs ih => simp only [List.cons_append,supplements,ih,nextCursor_cons,List.append_assoc]

/-- The native row count charges one equality per weighted source and one zero suffix
per bottom description; the copy count stays inside a strided record. -/
theorem supplements_length (start : ℕ) (xs : List Bundle) :
    (supplements start xs).length = (xs.map (fun x => count x.factors)).sum+xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    simp only [supplements,reportRows,List.length_append,links_length,sidecar_length,
      List.length_cons,List.length_nil,List.map_cons,List.sum_cons,ih]
    omega

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
