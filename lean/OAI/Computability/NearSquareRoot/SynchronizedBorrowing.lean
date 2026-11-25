import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Borrowed coordinates for synchronized short Fourier transforms

Number the fibers through one short axis in tape order. A batch is a
consecutive interval of at most one eighth of the fibers. The formulas below
give disjoint locations for all primary and borrowed coordinates, including
for a short final batch. They operate on indices and require no search.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedBorrowing

/-- Fifteen batches of width `b / 8` suffice for every block with eight fibers. -/
theorem batchCapacity {b : ℕ} (hb : 8 ≤ b) : b ≤ 15 * (b / 8) := by omega

/-- The first fiber of batch `j`, clipped for empty trailing batches. -/
def first (b : ℕ) (j : Fin 15) : ℕ := min b (j.val * (b / 8))

/-- The fiber count of batch `j`. -/
def size (b : ℕ) (j : Fin 15) : ℕ := min (b / 8) (b - first b j)

theorem batchFits (b : ℕ) (j : Fin 15) : first b j + size b j ≤ b := by
  have := min_le_left b (j.val * (b / 8))
  unfold size first at *
  omega

/-- Batch containing the indicated physical fiber. -/
def batchOf {b : ℕ} (hb : 8 ≤ b) (i : Fin b) : Fin 15 :=
  ⟨i.val / (b / 8), (Nat.div_lt_iff_lt_mul (by omega)).mpr
    (lt_of_lt_of_le i.isLt (batchCapacity hb))⟩

/-- Each fiber lies in its assigned batch's half-open interval. -/
theorem mem_batchOf {b : ℕ} (hb : 8 ≤ b) (i : Fin b) :
    first b (batchOf hb i) ≤ i.val ∧ i.val < first b (batchOf hb i) + size b (batchOf hb i) := by
  have hpos : 0 < b / 8 := by omega
  have hmod := Nat.mod_lt i.val hpos
  have hdiv := Nat.div_add_mod i.val (b / 8)
  have hi := i.isLt
  rw [Nat.mul_comm (b / 8)] at hdiv
  have hmin : min b (i.val / (b / 8) * (b / 8)) = i.val / (b / 8) * (b / 8) := by omega
  simp only [first, size, batchOf, hmin]
  omega

/-- A fiber in the interval belongs to this unique batch. -/
theorem batchOf_eq_of_mem {b : ℕ} (hb : 8 ≤ b) (i : Fin b) (j : Fin 15)
    (hl : first b j ≤ i.val) (hu : i.val < first b j + size b j) : batchOf hb i = j := by
  apply Fin.ext
  change i.val / (b / 8) = j.val
  have hi := i.isLt
  have hpos : 0 < b / 8 := by omega
  have hstart : j.val * (b / 8) < b := by
    by_contra! h
    simp [first, min_eq_left h] at hl
    omega
  have hs : first b j = j.val * (b / 8) := min_eq_right hstart.le
  have hv : size b j ≤ b / 8 := min_le_left _ _
  rw [Nat.div_eq_iff hpos]
  rw [hs] at hl hu
  exact ⟨hl, by omega⟩

/-- The primary coordinates of the `v` active fibers. -/
def activeFiber {start v b : ℕ} (h : start + v ≤ b) : Fin v ↪ Fin b where
  toFun i := ⟨start + i.val, by have := i.isLt; omega⟩
  inj' _ _ he := Fin.ext (by have := congrArg Fin.val he; dsimp at this; omega)

/-- Enumerate inactive fibers in order, skipping the active interval. -/
def inactiveFiber {start v b : ℕ} (h : start + v ≤ b) : Fin (b - v) ↪ Fin b where
  toFun i := ⟨if i.val < start then i.val else i.val + v, by have := i.isLt; split <;> omega⟩
  inj' i j he := by
    have e := congrArg Fin.val he
    dsimp at e
    apply Fin.ext
    split at e <;> split at e <;> omega

theorem active_ne_inactive {start v b : ℕ} (h : start + v ≤ b) (i : Fin v) (j : Fin (b-v)) :
    activeFiber h i ≠ inactiveFiber h j := by
  intro e
  have he := congrArg Fin.val e
  have hi := i.isLt
  change start + i.val = (if j.val < start then j.val else j.val + v) at he
  split at he <;> omega

theorem borrowedCapacity {v b a r : ℕ} (hv : v ≤ b / 8) (hr : 2*r ≤ 8*a) :
    v * (2*r - a) ≤ (b - v) * a := by
  calc
    v * (2*r-a) ≤ v * (7*a) := Nat.mul_le_mul_left v (by omega)
    _ = (7*v)*a := by ring
    _ ≤ (b-v)*a := Nat.mul_le_mul_right a (by omega)

/-- All borrowed slots fit into distinct physical coordinates in inactive fibers. -/
def borrowedCells {start v b a r : ℕ} (h : start + v ≤ b) (hv : v ≤ b / 8) (hr : 2*r ≤ 8*a) :
    Fin v × Fin (2*r-a) ↪ Fin b × Fin a :=
  finProdFinEquiv.toEmbedding |>.trans (Fin.castLEEmb (borrowedCapacity hv hr))
    |>.trans finProdFinEquiv.symm.toEmbedding
    |>.trans ((inactiveFiber h).prodMap (.refl _))

/-- Borrowed coordinates in a batch are disjoint from every active fiber's
primary coordinates. The embeddings also prevent collisions between two borrows. -/
theorem borrowedCells_not_active {start v b a r : ℕ} (h : start + v ≤ b)
    (hv : v ≤ b / 8) (hr : 2*r ≤ 8*a) (i : Fin v) (x : Fin v × Fin (2*r-a)) :
    activeFiber h i ≠ (borrowedCells h hv hr x).1 :=
  active_ne_inactive h i _

/-- Assemble the original `a` cells and the `2*r-a` borrowed cells into
a disjoint workspace for each active fiber, leaving every primary cell in place. -/
def placement {start v b a r : ℕ} (h : start + v ≤ b) (hv : v ≤ b / 8) (hr : 2*r ≤ 8*a) :
    Fin v × (Fin a ⊕ Fin (2*r-a)) ↪ Fin b × Fin a where
  toFun x := match x.2 with
    | .inl t => (activeFiber h x.1, t)
    | .inr t => borrowedCells h hv hr (x.1, t)
  inj' := by
    rintro ⟨i, x | x⟩ ⟨j, y | y⟩ e
    · obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
      exact Prod.ext ((activeFiber h).injective e₁) (congrArg Sum.inl e₂)
    · exact (borrowedCells_not_active h hv hr i (j, y) (congrArg Prod.fst e)).elim
    · exact (borrowedCells_not_active h hv hr j (i, x) (congrArg Prod.fst e.symm)).elim
    · have hxy := (borrowedCells h hv hr).injective e
      obtain ⟨e₁, e₂⟩ := Prod.mk.inj hxy
      exact Prod.ext e₁ (congrArg Sum.inr e₂)

theorem placement_primary {start v b a r : ℕ} (h : start + v ≤ b) (hv : v ≤ b / 8)
    (hr : 2*r ≤ 8*a) (i : Fin v) (t : Fin a) :
    placement h hv hr (i, .inl t) = (activeFiber h i, t) := rfl

/-- The physical allocation for any one of the fifteen scheduled batches. -/
def batchPlacement {a r : ℕ} (b : ℕ) (j : Fin 15) (hr : 2*r ≤ 8*a) :
    Fin (size b j) × (Fin a ⊕ Fin (2*r-a)) ↪ Fin b × Fin a :=
  placement (batchFits b j) (min_le_left _ _) hr

end SynchronizedBorrowing

end NearSquareRoot
end Computability
end OAI
