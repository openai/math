import HexMatrix.Basic
import Batteries.Data.List.Lemmas
import Mathlib.Basic.IsEmpty.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Basic

/-! Pointwise reads of in-place table sweeps with distinct update indices.
The row-update lemmas use Kim Morrison's [Hex matrix library](https://github.com/leanprover/hex-matrix/blob/3ce0f3dcaf3b51a23af13aa15f8524f387aa015f/HexMatrix/Basic.lean)
(© 2026 Lean FRO, LLC, Apache-2.0). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

private theorem observe_fold_distinct {S A I : Type} (read : S → A) (update : S → I → S)
    (label : I → ℕ) (target : ℕ) (f : A → A)
    (h : ∀ s i, read (update s i) = if label i=target then f (read s) else read s)
    (ids : List I) (nd : (ids.map label).Nodup) (s : S) :
    read (ids.foldl update s) = if target ∈ ids.map label then f (read s) else read s := by
  induction ids generalizing s with
  | nil => simp
  | cons i ids ih =>
    have hh := List.nodup_cons.mp nd
    rw [List.foldl_cons, ih hh.2, h]
    by_cases hi : label i = target
    · simp_all
    · have hi' := Ne.symm hi
      simp [hi,hi']

/-- In a single sweep, a fixed table entry is updated at most once. -/
theorem observe_finFold {S A : Type} (n : ℕ) (read : S → A) (update : S → Fin n → S)
    (target : ℕ) (f : A → A)
    (h : ∀ s i, read (update s i)=if i.val=target then f (read s) else read s) (s : S) :
    read (Fin.foldl n update s) = if target<n then f (read s) else read s := by
  have hmap : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  rw [Fin.foldl_eq_finRange_foldl,observe_fold_distinct read update Fin.val target f h _ (by
    rw [hmap]; exact List.nodup_range), hmap]
  simp

def copyPrefix {n : ℕ} (src old : Vector ℤ n) (p : Fin n) : Vector ℤ n :=
  Fin.foldl p.val (fun row j =>
    let i : Fin n := ⟨j.val,lt_trans j.isLt p.isLt⟩
    row.set i (src.get i)) old

theorem copyPrefix_get {n : ℕ} (src old : Vector ℤ n) (p l : Fin n) :
    (copyPrefix src old p).get l = if l.val<p.val then src.get l else old.get l := by
  unfold copyPrefix
  apply observe_finFold p.val (fun row : Vector ℤ n => row.get l) _ l.val (fun _ => src.get l)
  intro row j
  change (row.set j.val _ _)[l.val] = _
  rw [Vector.getElem_set _ l.isLt]
  by_cases h : j.val=l.val
  · simp [h]
  · simp [h]
    rfl

/-- Read one row after the native trailing-pair sweep. -/
theorem trailingRows_get {n m : ℕ} (k : ℕ) (A : Hex.Matrix ℤ n m)
    (u : Fin n → Vector ℤ m → Vector ℤ m) (i : Fin n) :
    (Fin.foldl n (fun (M : Hex.Matrix ℤ n m) j =>
      if k < j.val then M.modifyRow j.val (u j) else M) A).getRow i =
      if k < i.val then u i (A.getRow i) else A.getRow i := by
  have h := observe_finFold n (fun M : Hex.Matrix ℤ n m => M.getRow i)
    (fun M j => if k < j.val then M.modifyRow j.val (u j) else M) i.val
    (fun row => if k < i.val then u i row else row) (by
      intro M j
      by_cases hij : j=i
      · subst j
        by_cases hk : k < i.val <;> simp [hk]
      · have hv : j.val ≠ i.val := fun he => hij (Fin.ext he)
        by_cases hk : k < j.val <;> simp [hk,hv,Hex.Matrix.getRow_modifyRow_ne _ _ _ _ hv]) A
  simpa [i.isLt] using h

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
