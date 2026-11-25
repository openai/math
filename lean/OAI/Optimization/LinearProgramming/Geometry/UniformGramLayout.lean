import OAI.Optimization.LinearProgramming.RAM.Array

/-! Address-bank initialization and the memory layout of the uniform Gram projector. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM

/-- Copy address-register pairs in order, leaving the scalar bank untouched. -/
def indexMoves (xs : List (ℕ × ℕ)) : Block :=
  .straight (xs.map fun ij => .addrCopy ij.1 ij.2)

def movedIndices {K : Type*} (s : Memory K) : List (ℕ × ℕ) → Memory K
  | [] => s
  | (d,i)::xs => movedIndices (s.putIndex d (s.index i)) xs

@[simp] theorem movedIndices_data {K : Type*} (s : Memory K) (xs : List (ℕ × ℕ)) :
    (movedIndices s xs).data = s.data := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih => exact ih _

theorem movedIndices_other {K : Type*} (s : Memory K) (xs : List (ℕ × ℕ)) (p : ℕ)
    (h : ∀ ij ∈ xs, p≠ij.1) : (movedIndices s xs).index p = s.index p := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
    rcases a with ⟨d,i⟩
    exact (ih _ (fun z hz => h z (List.mem_cons_of_mem _ hz))).trans
      (Memory.putIndex_ne _ (h (_,_) List.mem_cons_self) _)

theorem indexMoves_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : s.AllData P) (xs : List (ℕ × ℕ)) :
    Block.Eval (Memory.AllData P) (indexMoves xs) s xs.length (movedIndices s xs) := by
  induction xs generalizing s with
  | nil => exact .skip hs
  | cons a as ih =>
    rcases a with ⟨d,i⟩
    have h := (Block.Eval.op_addrCopy (safe := Memory.AllData P) s d i hs hs).seq
      (ih (s.putIndex d (s.index i)) hs)
    simpa only [indexMoves, List.map_cons, Block.straight,
      movedIndices, List.length_cons, Nat.add_comm] using h

/-- All tables are consecutive or separated by gaps. The working determinant
matrices may be reused between independent cofactor calls. -/
structure GramLayout (r n : ℕ) where
  d : ℕ
  tr : ℕ
  g : ℕ
  inv : ℕ
  left : ℕ
  out : ℕ
  sub : ℕ
  workA : ℕ
  workB : ℕ
  minimum : 64 ≤ d
  d_tr : d + r*n ≤ tr
  tr_g : tr + n*r ≤ g
  g_inv : g + r*r ≤ inv
  inv_left : inv + r*r ≤ left
  left_out : left + n*r ≤ out
  out_sub : out + n*n ≤ sub
  sub_workA : sub + r*r ≤ workA
  workA_workB : workA + r*r ≤ workB

/-- Canonical buffer bases after the ordinary input tape. -/
def packedGramLayout (r n : ℕ) : GramLayout r n :=
  let d := 64 + r*n
  let tr := d + r*n
  let g := tr + n*r
  let inv := g + r*r
  let left := inv + r*r
  let out := left + n*r
  let sub := out + n*n
  let a := sub + r*r
  { d := d, tr := tr, g := g, inv := inv, left := left, out := out, sub := sub, workA := a,
    workB := a+r*r, minimum := Nat.le_add_right _ _, d_tr := le_rfl, tr_g := le_rfl,
    g_inv := le_rfl, inv_left := le_rfl, left_out := le_rfl, out_sub := le_rfl,
    sub_workA := le_rfl, workA_workB := le_rfl }

/-- Stable header values for the fixed Gram block. Register 14 holds zero for
the determinant. Registers 50–60 carry the dimensions and bases. -/
structure GramHeader {K : Type*} {r n : ℕ} (l : GramLayout r n) (s : Memory K) : Prop where
  zero : s.index 14 = 0
  rows : s.index 50 = r
  cols : s.index 51 = n
  d : s.index 52 = l.d
  tr : s.index 53 = l.tr
  g : s.index 54 = l.g
  inv : s.index 55 = l.inv
  left : s.index 56 = l.left
  out : s.index 57 = l.out
  sub : s.index 58 = l.sub
  a : s.index 59 = l.workA
  b : s.index 60 = l.workB

theorem GramHeader.of_frame {K : Type*} {r n : ℕ} {l : GramLayout r n} {s t : Memory K}
    (h : GramHeader l s) (frame : ∀ q, q=14 ∨ 50≤q ∧ q≤60 → t.index q=s.index q) :
    GramHeader l t where
  zero := (frame 14 (by decide)).trans h.zero
  rows := (frame 50 (by decide)).trans h.rows
  cols := (frame 51 (by decide)).trans h.cols
  d := (frame 52 (by decide)).trans h.d
  tr := (frame 53 (by decide)).trans h.tr
  g := (frame 54 (by decide)).trans h.g
  inv := (frame 55 (by decide)).trans h.inv
  left := (frame 56 (by decide)).trans h.left
  out := (frame 57 (by decide)).trans h.out
  sub := (frame 58 (by decide)).trans h.sub
  a := (frame 59 (by decide)).trans h.a
  b := (frame 60 (by decide)).trans h.b

end Geometry
end LinearProgramming
end Optimization
end OAI
