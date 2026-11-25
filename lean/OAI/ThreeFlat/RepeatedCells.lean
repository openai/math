import OAI.ThreeFlat.BitNetwork
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Prod

namespace OAI
/-! # Row-major copies and private overrides in the terminal slice

Each pallet has its own hidden variables and its own pin locations. Its rows
use a common addressing template. The full family can be materialized in
physical order, followed by a sparse list of private coefficient updates.
-/

namespace ThreeFlat.BitNetwork

open scoped BigOperators

variable {F : Type*} {p g : ℕ} (N : BitNetwork F p) (c : ℕ)

abbrev PrivateTable (F : Type*) := (Fin 3 → Bool) → F
abbrev DirtyRow (F : Type*) (size : ℕ) := Fin size × PrivateTable F

/-- Process overrides in transcript order; the last installation at a row wins. -/
def writeOverrides {q : ℕ} (updates : List (DirtyRow F q)) (base : Fin q → PrivateTable F) :
    Fin q → PrivateTable F := updates.foldl (fun rows e => Function.update rows e.1 e.2) base

def rebase (connect : Fin c → Fin p → BitSource 0 g) (i : Fin c) :
    BitSource N.internal p → BitSource (c*N.internal) g
  | .hidden j => .hidden (finProdFinEquiv (i,j))
  | .constant b => .constant b
  | .pin j =>
    match connect i j with
    | .pin k => .pin k
    | .constant b => .constant b
    | .hidden k => Fin.elim0 k

/-- The actual workspace arrays for a collection of copies. -/
def repeated (connect : Fin c → Fin p → BitSource 0 g)
    (updates : List (DirtyRow F (c*N.cells))) : BitNetwork F g where
  internal := c * N.internal
  cells := c * N.cells
  source j k := let ij := finProdFinEquiv.symm j
                N.rebase c connect ij.1 (N.source ij.2 k)
  table := writeOverrides updates fun j => N.table (finProdFinEquiv.symm j).2

private def groupBits (a : Fin c → Fin N.internal → Bool) : Fin (c*N.internal) → Bool :=
  fun h => a (finProdFinEquiv.symm h).1 (finProdFinEquiv.symm h).2

private def groupedEquiv : (Fin c → Fin N.internal → Bool) ≃ (Fin (c*N.internal) → Bool) where
  toFun := N.groupBits c
  invFun q i j := q (finProdFinEquiv (i,j))
  left_inv a := by funext i j; simp [groupBits]
  right_inv q := by
    funext h
    exact congrArg q (finProdFinEquiv.apply_symm_apply h)

private theorem read_rebase (connect : Fin c → Fin p → BitSource 0 g) (i : Fin c)
    (h : Fin c → Fin N.internal → Bool) (pin : Fin g → Bool) (s : BitSource N.internal p) :
    (N.rebase c connect i s).read (N.groupBits c h) pin =
      s.read (h i) (fun j => (connect i j).read Fin.elim0 pin) := by
  cases s with
  | hidden j => simp [rebase, BitSource.read, groupBits]
  | constant _ => rfl
  | pin j =>
    simp only [rebase, BitSource.read]
    cases connect i j with
    | hidden k => exact Fin.elim0 k
    | constant _ => rfl
    | pin _ => rfl

/-- The private table installed at one physical occurrence. -/
def installed (updates : List (DirtyRow F (c*N.cells))) (i : Fin c) : BitNetwork F p :=
  {N with table := fun j =>
    writeOverrides updates (fun j' => N.table (finProdFinEquiv.symm j').2) (finProdFinEquiv (i,j))}

private theorem repeated_weight [CommMonoid F] (connect : Fin c → Fin p → BitSource 0 g)
    (updates : List (DirtyRow F (c*N.cells))) (pin : Fin g → Bool)
    (h : Fin c → Fin N.internal → Bool) :
    (N.repeated c connect updates).weight pin (N.groupBits c h) =
      ∏ i, (N.installed c updates i).weight (fun j => (connect i j).read Fin.elim0 pin) (h i) := by
  unfold weight
  let f (i : Fin (c*N.cells)) := (N.repeated c connect updates).factor pin (N.groupBits c h) i
  change (∏ i, f i) = _
  rw [← finProdFinEquiv.prod_comp f, Fintype.prod_prod_type]
  dsimp only [f]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp [factor, repeated, installed, read_rebase]

/-- Arbitrary private rows do not couple separate pallets. -/
theorem repeated_eval [CommSemiring F] (connect : Fin c → Fin p → BitSource 0 g)
    (updates : List (DirtyRow F (c*N.cells))) (pin : Fin g → Bool) :
    (N.repeated c connect updates).eval pin =
      ∏ i, (N.installed c updates i).eval (fun j => (connect i j).read Fin.elim0 pin) := by
  classical
  unfold eval
  let f (h : Fin (c*N.internal) → Bool) := (N.repeated c connect updates).weight pin h
  change (∑ h, f h) = _
  rw [← (N.groupedEquiv c).sum_comp f]
  change (∑ h, (N.repeated c connect updates).weight pin (N.groupBits c h)) = _
  simp_rw [repeated_weight]
  exact (Fintype.prod_sum _).symm

end ThreeFlat.BitNetwork

end OAI
