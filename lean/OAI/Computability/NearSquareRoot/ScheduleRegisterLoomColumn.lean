import OAI.Computability.NearSquareRoot.ScheduleRegisterLoom

/-! # A fixed-register column of a serialized matrix of P192 trees -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space

private def rowBody (op : Cmd) : Cmd :=
  splitRoot 0 (give 0) (op.join ((move 0 1 2).join
    ((Prog.again 0).join ((move 1 0 2).join (pack 0)))))

/-- Map the field projection over a variable-length series of records. -/
def columnCommand (n : ℕ) : Cmd := .tie (rowBody (cellCommand n))

theorem column_within (n : ℕ) : Within 3 (columnCommand n) :=
  split_within (by decide) (fun _ => (by decide : 0 < 3))
    ⟨cell_within n, move_within (by decide) (by decide) (by decide),
     trivial, move_within (by decide) (by decide) (by decide), (by decide : 0 < 3)⟩

theorem count_le_forest {K : Type} (v : K → Tree) {xs : List K} {k : K}
    (h : k ∈ xs) : (v k).count ≤ (Task.forest v xs).count := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rw [Task.forest_cons, Tree.count]
    rcases List.mem_cons.mp h with h | h
    · subst k
      omega
    · have := ih h
      omega

private theorem forest_rows {K : Type} (rows : List K) (p q : K → Tree) (op : Cmd)
    (h : ∀ k, (q k).count ≤ (p k).count)
    (hc : ∀ k env r, Fits env op (pile 0 (p k) r) (pile 0 (q k) r) (90 * (p k).count))
    (env : Env) (r : Deck) :
    Fits (rowBody op :: env) (rowBody op) (pile 0 (Task.forest p rows) r)
      (pile 0 (Task.forest q rows) r) (190 * (Task.forest p rows).count) := by
  let G := rowBody op :: env
  induction rows generalizing r with
  | nil =>
    exact (fits_bit (b := false) (c := give 0) (fits_give false ..)).mono
      (by simp [Tree.count])
  | cons x xs ih =>
    have process := hc x G (pile 0 (Task.forest p xs) r)
    have send := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide)
      (q x) G (pile 0 (Task.forest p xs) r)
    rw [pile_comm 1 _ _ 0 _ (by decide)] at send
    have recurse := (ih (pile 1 (q x) r)).again0
    rw [pile_comm 0 (Task.forest q xs) r 1 (q x) (by decide)] at recurse
    have back := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide)
      (q x) G (pile 0 (Task.forest q xs) r)
    apply (fits_pair (process.join (send.join (recurse.join (back.join (fits_pack _ _ r 0 G)))))).mono
    have := h x
    simp only [Task.forest_cons, Tree.count, Nat.mul_add, Nat.mul_one]
    omega

/-- A column projection reads the matrix once with a uniform linear clock,
irrespective of both dimensions and of the selected field. -/
theorem column_fits {K A : Type} [DecidableEq K] (columns : Series K) (rows : Series A)
    (v : A → K → Tree) (k : K) (env : Env) (r : Deck) :
    Fits env (columnCommand (columns.explore.idxOf k)) (pile 0 (stripe rows (stripe columns ∘ v)) r)
      (pile 0 (stripe rows (fun a => v a k)) r) (191 * (stripe rows (stripe columns ∘ v)).count) := by
  let p := stripe columns ∘ v
  let q := fun a => v a k
  have small (a) : (q a).count ≤ (p a).count := by
    simpa only [p, q, Function.comp_apply, stripe_simple] using count_le_forest (v a) (columns.complete k)
  have cell (a env r) : Fits env (cellCommand (columns.explore.idxOf k))
      (pile 0 (p a) r) (pile 0 (q a) r) (90 * (p a).count) := by
    simpa only [p, q, Function.comp_apply, stripe_simple] using
      cell_fits (v a) columns.explore _ k (List.getElem?_idxOf (columns.complete k)) env r
  have run := (forest_rows rows.explore p q _ small cell env r).tie
  change Fits _ _ (pile 0 (stripe rows p) _) (pile 0 (stripe rows q) _) _
  simp only [stripe_simple] at ⊢
  apply run.mono
  have h := (Task.forest p rows.explore).count_pos
  change 190 * (Task.forest p rows.explore).count + 1 ≤ 191 * (Task.forest p rows.explore).count
  omega

theorem column_bounded {K A : Type} [DecidableEq K] (columns : Series K) (rows : Series A)
    (v : A → K → Tree) (k : K) (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let V := (stripe rows (stripe columns ∘ v)).count
    BoundedFits env (columnCommand (columns.explore.idxOf k)) (pile 0 (stripe rows (stripe columns ∘ v)) r)
      (pile 0 (stripe rows (fun a => v a k)) r) (191 * V) (base + 192 * V) (191 * V) := by
  have ht := column_fits columns rows v k env r
  refine BoundedFits.of_fits ht (fun i => ?_) le_rfl
  have h := hr.pile 0 (stripe rows (stripe columns ∘ v)) i
  omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
