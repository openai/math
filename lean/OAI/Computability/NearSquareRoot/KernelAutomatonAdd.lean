import OAI.Computability.NearSquareRoot.KernelAutomatonSeries
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Elementary rational word series

Relabeling allows transfer matrices to use the natural finite index type of
a construction. Independent evaluations can be combined by a block diagonal
direct sum. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelAutomatonEquiv.Series

open Matrix
open scoped Matrix

variable {γ ι : Type*} {d : ℕ}

/-- A representation on an explicitly enumerated finite state set. -/
def ofEquiv (e : ι ≃ Fin d) (u : ι → ℚ) (L : γ → Matrix ι ι ℚ)
    (v : ι → ℚ) : Series γ where
  dim := d
  initial := u ∘ e.symm
  letter a := (L a).submatrix e.symm e.symm
  final := v ∘ e.symm

theorem ofEquiv_eval [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin d)
    (u : ι → ℚ) (L : γ → Matrix ι ι ℚ) (v : ι → ℚ) (w : List γ) :
    (ofEquiv e u L v).eval w = u ⬝ᵥ ((w.map L).prod *ᵥ v) := by
  have hprod : ∀ xs : List γ,
      (xs.map (fun a => (L a).submatrix e.symm e.symm)).prod =
      (xs.map L).prod.submatrix e.symm e.symm := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih]
  unfold eval weight ofEquiv
  dsimp only
  rw [hprod, submatrix_mulVec_equiv]
  simp [Function.comp_assoc]

/-- Add the two series on disjoint sets of states. -/
def add (P Q : Series γ) : Series γ :=
  ofEquiv finSumFinEquiv (Sum.elim P.initial Q.initial)
    (fun a => Matrix.fromBlocks (P.letter a) 0 0 (Q.letter a)) (Sum.elim P.final Q.final)

theorem add_eval (P Q : Series γ) (w : List γ) :
    (add P Q).eval w = P.eval w + Q.eval w := by
  rw [add, ofEquiv_eval]
  have h (xs : List γ) : (xs.map (fun a =>
      Matrix.fromBlocks (P.letter a) 0 0 (Q.letter a))).prod =
      Matrix.fromBlocks (xs.map P.letter).prod 0 0 (xs.map Q.letter).prod := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih, fromBlocks_multiply]
  rw [h, fromBlocks_mulVec]
  simp [eval, weight, dotProduct, Fintype.sum_sum_type]

/-- Multiply the initial row by a rational scalar. -/
def scale (c : ℚ) (P : Series γ) : Series γ := {P with initial := c • P.initial}

theorem scale_eval (c : ℚ) (P : Series γ) (w : List γ) :
    (scale c P).eval w = c * P.eval w := by
  exact smul_dotProduct c P.initial ((w.map P.letter).prod *ᵥ P.final)

/-- Select the `(i,j)` entry of every transition product. -/
def entry (L : γ → Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) : Series γ :=
  ⟨d, Pi.single i 1, L, Pi.single j 1⟩

theorem entry_eval (L : γ → Matrix (Fin d) (Fin d) ℚ) (i j : Fin d) (w : List γ) :
    (entry L i j).eval w = (w.map L).prod i j := by
  change Pi.single i (1 : ℚ) ⬝ᵥ ((w.map L).prod *ᵥ (Pi.single j 1)) = _
  rw [single_one_dotProduct, mulVec_single_one]
  rfl

/-- Multiply one scalar weight per letter, including the empty product. -/
def letterProduct (c : γ → ℚ) : Series γ :=
  entry (fun a => Matrix.scalar (Fin 1) (c a)) 0 0

theorem letterProduct_eval (c : γ → ℚ) (w : List γ) :
    (letterProduct c).eval w = (w.map c).prod := by
  rw [letterProduct, entry_eval]
  have h (xs : List γ) :
      (xs.map (fun a => Matrix.scalar (Fin 1) (c a))).prod =
        Matrix.scalar (Fin 1) (xs.map c).prod := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp only [List.map_cons, List.prod_cons, ih, map_mul]
  rw [h]
  simp [Matrix.scalar_apply]

/-- A series with the same value on all words. -/
def constant (c : ℚ) : Series γ := scale c (letterProduct fun _ => 1)

theorem constant_eval (c : ℚ) (w : List γ) : (constant c).eval w = c := by
  simp [constant, scale_eval, letterProduct_eval]

end KernelAutomatonEquiv.Series

end NearSquareRoot
end Computability
end OAI
