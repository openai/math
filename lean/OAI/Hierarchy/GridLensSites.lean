import OAI.Hierarchy.GridLens

namespace OAI
/-! # Mounted grid cells, translated ports, and rail segments -/

namespace Hierarchy.GridLens
open scoped BigOperators
noncomputable section

variable {k n : ℕ}

/-- The cell with longitudinal index `t` and the transverse indices of `row`. -/
def cellOnRail (j : Fin k) (row : Fin k → Fin (n+1)) (t : Fin (n+1)) : Fin k → Fin (n+1) :=
  fun i => if i = j then t else row i

@[simp] theorem cellOnRail_axis (j : Fin k) (row : Fin k → Fin (n+1)) (t : Fin (n+1)) :
    cellOnRail j row t j = t := by simp [cellOnRail]

@[simp] theorem cellOnRail_off {i j : Fin k} (row : Fin k → Fin (n+1)) (t : Fin (n+1))
    (h : i ≠ j) : cellOnRail j row t i = row i := by simp [cellOnRail, h]

@[simp] theorem cellOnRail_self (j : Fin k) (x : Fin k → Fin (n+1)) :
    cellOnRail j x (x j) = x := by
  funext i
  by_cases h : i = j <;> simp [cellOnRail, h]

theorem cellOnRail_injective (j : Fin k) (row : Fin k → Fin (n+1)) :
    Function.Injective (cellOnRail j row) := by
  intro a b h
  simpa using congrFun h j

theorem cellOnRail_eq_iff (j : Fin k) (row x : Fin k → Fin (n+1)) (t : Fin (n+1)) :
    cellOnRail j row t = x ↔ t = x j ∧ ∀ i, i ≠ j → row i = x i := by
  constructor
  · intro h
    refine ⟨by simpa using congrFun h j, ?_⟩
    intro i hi
    simpa [hi] using congrFun h i
  · rintro ⟨ht, hrow⟩
    funext i
    by_cases h : i = j
    · subst i
      simpa using ht
    · simpa [h] using hrow i h

/-- The Euclidean center of a cell in the grid of spacing three. -/
def cellCenter (x : Fin k → Fin (n+1)) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => center (x i).val)

@[simp] theorem cellCenter_apply (x : Fin k → Fin (n+1)) (i : Fin k) :
    cellCenter x i = center (x i).val := rfl

/-- The negative (false) or positive (true) unit translate of a cell center. -/
def cellPort (x : Fin k → Fin (n+1)) (j : Fin k) (side : Bool) : EuclideanSpace ℝ (Fin k) :=
  cellCenter x + EuclideanSpace.single j (if side then 1 else -1)

theorem cellPort_eq_point (x : Fin k → Fin (n+1)) (j : Fin k) (side : Bool) :
    cellPort x j side = point j (fun i => center (x i).val)
      (center (x j).val + if side then 1 else -1) := by
  ext i
  by_cases h : i = j <;> simp [cellPort, h]

theorem cellCenter_onRail (j : Fin k) (row : Fin k → Fin (n+1)) (t : Fin (n+1)) :
    cellCenter (cellOnRail j row t) = point j (fun i => center (row i).val) (center t.val) := by
  ext i
  by_cases h : i = j <;> simp [h]

theorem cellPort_onRail (j : Fin k) (row : Fin k → Fin (n+1)) (t : Fin (n+1)) (side : Bool) :
    cellPort (cellOnRail j row t) j side = point j (fun i => center (row i).val)
      (center t.val + if side then 1 else -1) := by
  rw [cellPort_eq_point]
  ext i
  by_cases h : i = j <;> simp [h]

theorem dist_cellPort (x : Fin k → Fin (n+1)) (j : Fin k) :
    dist (cellPort x j false) (cellPort x j true) = 2 := by
  simp only [cellPort_eq_point, Bool.false_eq_true, ↓reduceIte]
  rw [dist_along _ _ _ _ (by linarith)]
  ring

theorem dist_cellCenter_port (x : Fin k → Fin (n+1)) (j : Fin k) (side : Bool) :
    dist (cellCenter x) (cellPort x j side) = 1 := by
  have hc : cellCenter x = point j (fun i => center (x i).val) (center (x j).val) := by
    simpa using cellCenter_onRail j x (x j)
  rw [hc, cellPort_eq_point]
  cases side
  · rw [dist_comm, dist_along _ _ _ _ (by simp)]
    simp
  · rw [dist_along _ _ _ _ (by simp)]
    simp

theorem center_succ (t : ℕ) : center (t+1) = center t + 3 := by
  simp only [center, Nat.cast_add, Nat.cast_one]
  ring

theorem point_zero_eq_single (j : Fin k) (a : ℝ) :
    point j 0 a = EuclideanSpace.single j a := by
  ext i
  simp [PiLp.single_apply]

theorem dist_consecutive_centers (j : Fin k) (row : Fin k → Fin (n+1)) (t : Fin n) :
    dist (cellCenter (cellOnRail j row t.castSucc)) (cellCenter (cellOnRail j row t.succ)) = 3 := by
  simp only [cellCenter_onRail, Fin.val_castSucc, Fin.val_succ, center_succ]
  rw [dist_along _ _ _ _ (by linarith)]
  ring

theorem dist_consecutive_ports (j : Fin k) (row : Fin k → Fin (n+1)) (t : Fin n) :
    dist (cellPort (cellOnRail j row t.castSucc) j true)
      (cellPort (cellOnRail j row t.succ) j false) = 1 := by
  simp only [cellPort_onRail, Fin.val_castSucc, Fin.val_succ, center_succ,
    Bool.false_eq_true, ↓reduceIte]
  rw [dist_along _ _ _ _ (by linarith)]
  ring

/-- The geometric cost of the mounted path agrees with the scalar rail ledger,
including its two possibly transverse links to the foci. -/
theorem railCost_eq_mounted (j : Fin k) (row : Fin k → Fin (n+1)) (R : ℝ) :
    railCost j row R =
      dist (point j 0 (-R)) (cellPort (cellOnRail j row 0) j false) +
      (∑ t : Fin (n+1), dist (cellPort (cellOnRail j row t) j false) (cellPort (cellOnRail j row t) j true)) +
      (∑ t : Fin n, dist (cellPort (cellOnRail j row t.castSucc) j true)
        (cellPort (cellOnRail j row t.succ) j false)) +
      dist (cellPort (cellOnRail j row (Fin.last n)) j true) (point j 0 R) := by
  simp [railCost, cellPort_onRail, sub_eq_add_neg]

end
end Hierarchy.GridLens

end OAI
