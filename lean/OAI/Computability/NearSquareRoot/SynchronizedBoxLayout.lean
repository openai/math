import OAI.Computability.NearSquareRoot.BoxFin
import OAI.Computability.NearSquareRoot.BoxScale
import OAI.Computability.NearSquareRoot.SynchronizedBlocks
import OAI.Computability.NearSquareRoot.SynchronizedAssembly
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Physical address layout of the synchronized blocks

The regrouping of axes is a definitional interpretation of consecutive fields
of one address. The designated Walsh bit is the high bit of the first axis of
each block in the natural order (occupied residues followed by padding).
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedBlocks

open Matrix Finset SynchronizedPadding

/-- All padded addresses of a single axis, with residue representatives first. -/
abbrev Axis (a c : ℕ) := ZMod a ⊕ Fin c

/-- Local address type of the block of four to seven consecutive axes. -/
abbrev BlockAddress {d : ℕ} (A : Fin d → Type) (j : Fin (d/4)) :=
  (i : Fin (count j)) → A (axis j i)

/-- Group the consecutive axes without changing the individual entries. -/
def regroup {d : ℕ} (hd : 4 ≤ d) (A : Fin d → Type) :
    (∀ i, A i) ≃ ∀ j, BlockAddress A j :=
  ((Equiv.piCongrLeft A (coordinates hd)).symm).trans
    (Equiv.piCurry (fun j i => A (axis j i)))

@[simp] theorem regroup_apply {d : ℕ} (hd : 4 ≤ d) (A : Fin d → Type) (x : ∀ i, A i)
    (j : Fin (d/4)) (i : Fin (count j)) :
    regroup hd A x j i = x (axis j i) := rfl

/-- A tensor of the block tensors is the original axis tensor in physical order. -/
theorem regroup_tensor {d : ℕ} (hd : 4 ≤ d) {A : Fin d → Type}
    (M : ∀ i, Matrix (A i) (A i) ℂ) :
    (tensorMatrix (fun j : Fin (d/4) => tensorMatrix (fun i : Fin (count j) => M (axis j i)))).submatrix
      (regroup hd A) (regroup hd A) = tensorMatrix M := by
  ext x y
  simp only [tensorMatrix, Matrix.submatrix_apply, Matrix.of_apply, regroup_apply]
  let w (i : Fin d) := M i (x i) (y i)
  exact (Fintype.prod_sigma (fun s : Σ j : Fin (d/4), Fin (count j) => w (axis s.1 s.2))).symm.trans
    ((coordinates hd).prod_comp w)

/-- The first axis of a block exists even when the last block has extra axes. -/
def firstAxis {d : ℕ} (j : Fin (d / 4)) : Fin (count j) := ⟨0, by have := (count_bounds j).1; omega⟩

/-- Low bits of the first axis and all other axes are spectators to the
fixed Walsh bit. -/
abbrev Spectator {d : ℕ} (A : Fin d → Type) (w : Fin d → ℕ) (j : Fin (d/4)) :=
  Fin (2 ^ (w (axis j (firstAxis j)) - 1)) ×
    ((i : {i : Fin (count j) // i ≠ firstAxis j}) → A (axis j i))

/-- Reading the most significant bit from the physical interval of an axis. -/
noncomputable def splitAxis {a c w : ℕ} [NeZero a] (hw : 0 < w) (ha : a+c = 2^w) :
    Axis a c ≃ Fin 2 × Fin (2 ^ (w-1)) :=
  let p : a + c = 2 * 2^(w-1) := by
    rw [ha, ← Nat.pow_succ']
    congr 1
    omega
  ((Equiv.sumCongr (ZMod.finEquiv a).symm.toEquiv (Equiv.refl (Fin c))).trans
    finSumFinEquiv).trans ((finCongr p).trans finProdFinEquiv.symm)

/-- The fixed bit used by the layer compiler on each block of the padded box. -/
noncomputable def bitLayout {d : ℕ} (a c w : Fin d → ℕ) [∀ i, NeZero (a i)]
    (hw : ∀ i, 0 < w i) (ha : ∀ i, a i + c i = 2 ^ w i)
    (j : Fin (d/4)) :
    BlockAddress (fun i => Axis (a i) (c i)) j ≃
      Fin 2 × Spectator (fun i => Axis (a i) (c i)) w j :=
  let i := firstAxis j
  let axisBit := splitAxis (hw (axis j i)) (ha (axis j i))
  (Equiv.piSplitAt i (fun t => Axis (a (axis j t)) (c (axis j t)))).trans
    ((Equiv.prodCongr axisBit (Equiv.refl _)).trans (Equiv.prodAssoc ..))

/-- At sufficiently large lengths the box has at least four axes. -/
theorem four_le_length {k L : ℕ} {box : List (ℕ × ℕ)} (h : BoxShape.Valid k L box)
    (hk : 3*L < k) : 4 ≤ box.length := by
  have hs := List.sum_le_length_nsmul (box.map Prod.fst) L (by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
    exact (h.axisBounds _ hp).2.1)
  simp only [List.length_map, nsmul_eq_mul, h.widthSum] at hs
  change k ≤ box.length * L at hs
  by_contra! hlen
  have := Nat.mul_le_mul_right L (show box.length ≤ 3 by omega)
  omega

private theorem sixty_le_pow {j : ℕ} (hj : 10 ≤ j) : 60 * (j+1) ≤ 2^j := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j _ ih => rw [Nat.pow_succ]; omega

theorem three_width_lt {k : ℕ} (hk : 1024 ≤ k) : 3 * BoxScale.width k < k := by
  have hk' : 1 < k := by omega
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by decide) hk'
  unfold BoxScale.width
  by_cases hs : Nat.clog 2 k ≤ 10
  · omega
  · have h' := sixty_le_pow (j := (Nat.clog 2 k).pred) (by rw [Nat.pred_eq_sub_one]; omega)
    simp only [Nat.pred_eq_sub_one] at *
    omega

end SynchronizedBlocks

namespace ShortFourier

open Matrix SynchronizedBlocks

noncomputable section

variable {d : ℕ} {A : Fin d → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable {S : Fin (d/4) → Type} [∀ j, Fintype (S j)] [∀ j, DecidableEq (S j)]

/-- View the allowed global layer on the ungrouped address fields. -/
def BoxStage (hd : 4 ≤ d) (bits : ∀ j, BlockAddress A j ≃ Fin 2 × S j)
    (N : Matrix (∀ i, A i) (∀ i, A i) ℂ) : Prop :=
  ∃ M, GlobalStage bits M ∧ M.submatrix (regroup hd A) (regroup hd A) = N

abbrev BoxAxis (box : List (ℕ × ℕ)) (i : Fin box.length) := Axis (BoxFin.modulus box i) (BoxFin.padding box i)

def boxBits {k L : ℕ} {box : List (ℕ × ℕ)} (h : BoxShape.Valid k L box)
    [∀ i, NeZero (BoxFin.modulus box i)] (j : Fin (box.length/4)) :
    BlockAddress (BoxAxis box) j ≃ Fin 2 × Spectator (BoxAxis box) (fun i => (box.get i).1) j :=
  bitLayout (BoxFin.modulus box) (BoxFin.padding box) (fun i => (box.get i).1) (fun i => (h.axisBounds _ (List.get_mem box i)).1)
    (fun i => Nat.add_sub_of_le (h.axisBounds _ (List.get_mem box i)).2.2.2) j

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI
