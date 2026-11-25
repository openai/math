import OAI.Computability.NearSquareRoot.SynchronizedAxisLayout
import OAI.Computability.NearSquareRoot.SynchronizedBatchWord
import OAI.Computability.NearSquareRoot.SynchronizedFixedSemantics

/-! # Fourier action of the batched physical block word

A descriptor selects an axis, one of its fifteen batches of spectator fibers,
and an instruction from the restored fixed-bit circuit. Each instruction acts
on all its placed fibers at once and fixes every cell outside that placement.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open Matrix SynchronizedPadding SynchronizedBorrowing ResidueFourier IntegerMultiplication.Code AxisWord

noncomputable section

variable {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
  (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
  (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)

/-- The gate is placed in every workspace in its batch; the physical address
is given by the supplied spectator-rank equivalence. -/
def gateMatrix (g : Fin m × Fin 15 × Inst) : Matrix (∀ i, BlockAxis a c i) (∀ i, BlockAxis a c i) ℂ :=
  let i := g.1
  let b := g.2.1
  let x := g.2.2
  let e := axisLayout a c spectator i
  let u := auxiliaryLayout (har i)
  let v := (fixedSlot (a i) (k i) x).matrix dilationAddress
  (batchMatrix (b := Fintype.card (Spectators a c i)) (c := c i) (hborrow i) b
    (v.submatrix u.symm u.symm)).submatrix e e

private theorem map_submatrix_prod {X Y Z : Type} [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z]
    (e : Z ≃ Y) (op : X → Matrix Y Y ℂ) (w : List X) :
    ((w.map fun x => (op x).submatrix e e).prod) = ((w.map op).prod).submatrix e e := by
  induction w with
  | nil => simp
  | cons x w ih => simp [ih, submatrix_mul_equiv]

private theorem map_flatMap_prod {X Y M : Type} [Monoid M] (f : X → List Y) (g : Y → M) (w : List X) :
    ((w.flatMap f).map g).prod = (w.map fun x => ((f x).map g).prod).prod := by
  induction w with
  | nil => simp
  | cons x w ih => simp [ih]

private theorem batch_gate_prod (hwrap : ∀ i, 2 * a i - 1 ≤ 2 ^ k i) (i : Fin m) (b : Fin 15) :
    ((fixedWord (tally (k i))).map (fun x => gateMatrix a c k spectator har hborrow (i,b,x))).prod =
      (batchMatrix (b := Fintype.card (Spectators a c i)) (c := c i) (hborrow i) b
        (extend (rowInclusion (a i) (2 * 2 ^ k i - a i)) (normalizedFourier (a i)))).submatrix
          (axisLayout a c spectator i) (axisLayout a c spectator i) := by
  let w := fixedWord (tally (k i))
  let matrix := fun x => (fixedSlot (a i) (k i) x).matrix dilationAddress
  let u := (auxiliaryLayout (har i)).symm
  let e := axisLayout a c spectator i
  let M := fun x => (matrix x).submatrix u u
  let H := batchMatrix (b := Fintype.card (Spectators a c i)) (c := c i) (hborrow i) b
  change (w.map (fun x => (H (M x)).submatrix e e)).prod = _
  rw [map_submatrix_prod]
  have h : (w.map M).prod = extend (rowInclusion (a i) (2 * 2 ^ k i - a i)) (normalizedFourier (a i)) := by
    rw [show (w.map M).prod = (w.map matrix).prod.submatrix u u from map_submatrix_prod u matrix w,
      fixedWord_correct (hwrap i) (har i), auxiliaryLayout_extend]
  rw [← h, batchMatrix_list_prod, List.map_map]
  rfl

private theorem axis_gate_prod (hwrap : ∀ i, 2 * a i - 1 ≤ 2 ^ k i)
    (hspec : ∀ i, 8 ≤ Fintype.card (Spectators a c i)) (i : Fin m) :
    (((List.finRange 15).flatMap (fun b => (fixedWord (tally (k i))).map (fun x => (i,b,x)))).map
      (gateMatrix a c k spectator har hborrow)).prod =
      (fiberMatrix (c := c i) (Fintype.card (Spectators a c i)) (normalizedFourier (a i))).submatrix
        (axisLayout a c spectator i) (axisLayout a c spectator i) := by
  rw [map_flatMap_prod]
  simp only [List.map_map, Function.comp_def, batch_gate_prod a c k spectator har hborrow hwrap]
  rw [map_submatrix_prod, ← fiberMatrix_eq_batches (hspec i) (hborrow i)]

/-- The product of the exact axis-tagged and batch-tagged instruction word is
the desired Fourier tensor, extended by the identity on each axis's spare slots. -/
theorem typed_prod (hwrap : ∀ i, 2 * a i - 1 ≤ 2 ^ k i)
    (hspec : ∀ i, 8 ≤ Fintype.card (Spectators a c i)) :
    ((typed k).map (gateMatrix a c k spectator har hborrow)).prod =
      tensorMatrix (fun i => axisPadding (b := Fin (c i)) (axisMatrix (a i))) := by
  rw [typed, map_flatMap_prod]
  simp only [axis_gate_prod a c k spectator har hborrow hwrap hspec]
  exact axisPass_prod a c spectator

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
