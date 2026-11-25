import OAI.ThreeFlat.Diagonal.ChunkScan
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Option

namespace OAI
/-! # The shared history in the switched computation

An opening transition chooses one history while preserving the external
index. Every intermediate block preserves that choice, and a closing
transition forgets it. This allows one branch to implement the exact
identity while the other branches simulate the evaluator.
-/

namespace ThreeFlat.Diagonal

variable {R X H : Type*} [Semiring R] [Fintype X] [DecidableEq X]
  [Fintype H] [DecidableEq H]

/-- Open a history register, allowing every history with unit weight, without
changing the external index. The transpose closes the register. -/
def openHistory : Matrix X (X × H) R := fun x yz => (1 : Matrix X X R) x yz.1

private theorem open_mul_block (M : H → Matrix X X R) (x y : X) (h : H) :
    (openHistory (R := R) (X := X) (H := H) * Matrix.blockDiagonal M) x (y, h) = M h x y := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_prod_type, openHistory, Matrix.one_apply,
    Matrix.blockDiagonal_apply, mul_ite, ite_mul]

private theorem sandwich_block (M : H → Matrix X X R) :
    openHistory * Matrix.blockDiagonal M * openHistory.transpose = ∑ h, M h := by
  classical
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [open_mul_block, openHistory, Matrix.one_apply, Matrix.transpose_apply,
    mul_ite, Matrix.sum_apply]

/-- Intermediate transitions preserve the history register, so opening and
closing it sums only once over the histories through the whole product. -/
theorem run_persistent_history {ι : Type*} (steps : List ι) (M : ι → H → Matrix X X R) :
    openHistory * (steps.map fun t => Matrix.blockDiagonal (M t)).prod *
      openHistory.transpose = ∑ h, (steps.map fun t => M t h).prod := by
  have diag : (steps.map fun t => Matrix.blockDiagonal (M t)).prod =
      Matrix.blockDiagonal (fun h => (steps.map fun t => M t h).prod) := by
    induction steps with
    | nil =>
      ext ⟨x, h⟩ ⟨y, h'⟩
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply, and_comm,
        ← ite_and]
    | cons t rest ih =>
      simp only [List.map_cons, List.prod_cons, ih, Matrix.blockDiagonal_mul]
  rw [diag, sandwich_block]

/-- Reserve the empty history for the identity branch and choose a history
for the simulated branch. Both branches are now ordinary matrix products
on the same external register. -/
theorem switched_history_evaluation {ι : Type*} (steps : List ι) (M : ι → H → Matrix X X R) :
    let update := fun t => fun h : Option H => h.elim 1 (M t)
    openHistory * (steps.map fun t => Matrix.blockDiagonal (update t)).prod *
      openHistory.transpose = 1 + ∑ h, (steps.map fun t => M t h).prod := by
  dsimp only
  rw [run_persistent_history, Fintype.sum_option]
  simp

/-- Entry of the switched chronological product when each external group has
one occasion to change. After a shared history is chosen, every group can
apply its own arbitrary weighted test to all its old and new bits. -/
theorem switched_scan_entry {S ι : Type*} [CommSemiring S] [Fintype ι] [DecidableEq ι]
    {Y : ι → Type*} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (K : H → ∀ i, Matrix (Y i) (Y i) S) (order : List ι)
    (hd : order.Nodup) (covers : ∀ i, i ∈ order) (x y : ∀ i, Y i) :
    let update := fun i => fun h : Option H =>
      h.elim (1 : Matrix (∀ i, Y i) (∀ i, Y i) S) (fun k => chunkKernel (K k) {i})
    (openHistory (H := Option H) (X := ∀ i, Y i) (R := S) *
      (order.map fun i => Matrix.blockDiagonal (update i)).prod *
        (openHistory (H := Option H) (X := ∀ i, Y i) (R := S)).transpose :
          Matrix (∀ i, Y i) (∀ i, Y i) S) x y =
      (1 : Matrix (∀ i, Y i) (∀ i, Y i) S) x y + ∑ h, ∏ i, K h i (x i) (y i) := by
  dsimp only
  rw [switched_history_evaluation order (fun i h => chunkKernel (K h) {i})]
  simp only [Matrix.add_apply, Matrix.sum_apply, complete_chunk_scan_apply _ order hd covers]

private theorem product_submatrix {S I J L : Type*} [Semiring S]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J)
    (steps : List L) (M : L → Matrix J J S) :
    (steps.map fun t => (M t).submatrix e e).prod =
      (steps.map M).prod.submatrix e e := by
  induction steps with
  | nil =>
    ext i j
    simp [Matrix.one_apply]
  | cons t rest ih =>
    simp only [List.map_cons, List.prod_cons, ih, Matrix.submatrix_mul_equiv]

/-- The partition of the external bits into groups may itself depend on the
chosen compression history. Each branch uses its own indexing equivalence
throughout the scan but acts on the common external state type. -/
theorem switched_reindexed_scan {S ι : Type*} [CommSemiring S] [Fintype ι] [DecidableEq ι]
    {Y : H → ι → Type*} [∀ h i, Fintype (Y h i)] [∀ h i, DecidableEq (Y h i)]
    (index : ∀ h, X ≃ (∀ i, Y h i)) (K : ∀ h i, Matrix (Y h i) (Y h i) S)
    (order : List ι) (hd : order.Nodup) (covers : ∀ i, i ∈ order) (x y : X) :
    let active := fun i h => (chunkKernel (K h) {i}).submatrix (index h) (index h)
    let update := fun i => fun h : Option H => h.elim (1 : Matrix X X S) (active i)
    (openHistory * (order.map fun i => Matrix.blockDiagonal (update i)).prod *
      openHistory.transpose : Matrix X X S) x y =
        (1 : Matrix X X S) x y + ∑ h, ∏ i, K h i (index h x i) (index h y i) := by
  dsimp only
  rw [switched_history_evaluation]
  simp only [Matrix.add_apply, Matrix.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [product_submatrix (index h) order (fun i => chunkKernel (K h) {i})]
  exact complete_chunk_scan_apply _ order hd covers _ _

end ThreeFlat.Diagonal

end OAI
