import OAI.Computability.NearSquareRoot.KernelPass
import OAI.Computability.NearSquareRoot.KernelNormalization
import OAI.Computability.NearSquareRoot.SynchronizedLayerTensor

/-! # Exact normalized transforms and slot reindexings in stream plans

The direct spectral conversions used in Hermite repair cost exactly one call
per axis and per independent row. The complex interpretation of each rational
kernel is the corresponding tensor of normalized Walsh matrices. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Finset Matrix SynchronizedPadding
open scoped BigOperators

variable {A : ℕ}

def identity : Plan A 1 1 := .mix fun _ _ => (1,0)

def fullConversion (axes : List (Fin A)) : Plan A 1 1 :=
  axes.foldr (fun a rest => .seq (.child a) rest) identity

theorem calls_fullConversion (axes : List (Fin A)) :
    (fullConversion axes).calls = axes.length := by
  induction axes with
  | nil => rfl
  | cons a tail ih =>
    change 1 + (fullConversion tail).calls = tail.length + 1
    omega

/-- Remove the singleton row-bank index. This preserves matrix multiplication. -/
def oneRow {h : ℕ} (M : RowMatrix A h 1 1) : Matrix (Addr A h) (Addr A h) ℚ :=
  fun y x => M (0,y) (0,x)

theorem oneRow_mul {h : ℕ} (M N : RowMatrix A h 1 1) :
    oneRow (M * N) = oneRow M * oneRow N := by
  ext y x
  simp [oneRow, Matrix.mul_apply, Fintype.sum_prod_type]

private abbrev bitPair := Fin 2 → ZMod 2

private def pairM : Matrix bitPair bitPair ℚ := pairEntry

private def stage (a b : Fin A) : Matrix bitPair bitPair ℚ :=
  if b = a then pairM else 1

private theorem tensor_stage (a : Fin A) : tensorMatrix (stage a) = childEntry a := by
  ext y x
  classical
  change (∏ b, stage a b (y b) (x b)) = childEntry a y x
  unfold childEntry
  split_ifs with hs
  · rw [prod_eq_single a]
    · simp [stage, pairM]
    · intro b _ hb
      simp [stage, hb, Matrix.one_apply, hs b hb]
    · simp
  · push Not at hs
    obtain ⟨b,hb,hne⟩ := hs
    exact prod_eq_zero (mem_univ b) (by simp [stage, hb, Ne.symm hne])

private theorem single_conversion {h : ℕ} (a : Fin A) :
    oneRow (Plan.eval h (.child a)) =
      tensorMatrix (fun _ : Fin h => tensorMatrix (stage a)) := by
  rw [tensor_stage]
  rfl

private theorem oneRow_identity (h : ℕ) :
    oneRow (identity (A := A) |>.eval h) = 1 := by
  ext y x
  change (if x = y then value (1,0) else 0) = _
  simp [value, Matrix.one_apply, eq_comm]

private theorem fullConversion_matrix (h : ℕ) (axes : List (Fin A)) :
    oneRow ((fullConversion axes).eval h) =
      tensorMatrix (fun _ : Fin h => tensorMatrix
        (fun b : Fin A => (axes.map (fun a => stage a b)).prod)) := by
  induction axes with
  | nil => simp [fullConversion, oneRow_identity]
  | cons a axes ih =>
    change oneRow (Plan.eval h (.child a) * (fullConversion axes).eval h) = _
    rw [oneRow_mul, single_conversion, ih, ← tensorMatrix_mul]
    simp only [← tensorMatrix_mul, List.map_cons, List.prod_cons]

private theorem stage_word (a : Fin A) (axes : List (Fin A)) (h : axes.Nodup) :
    (axes.map (fun b => stage b a)).prod = if a ∈ axes then pairM else 1 := by
  induction axes with
  | nil => simp
  | cons b l ih =>
    obtain ⟨hb,hl⟩ := List.nodup_cons.mp h
    simp only [List.map_cons, List.prod_cons, ih hl, List.mem_cons]
    by_cases e : a = b
    · subst b
      simp [stage, hb]
    · simp [stage, e]

/-- The full conversion is a verified pass template on one row, including
width zero, with A recursive calls. -/
theorem fullConversion_correct (A : ℕ) : Correct (fullConversion (List.finRange A)) := by
  intro h
  ext ⟨row,y⟩ ⟨col,x⟩
  have hr : row = 0 := Subsingleton.elim ..; subst row
  have hc : col = 0 := Subsingleton.elim ..; subst col
  have E := congrFun (congrFun (fullConversion_matrix h (List.finRange A)) y) x
  change oneRow _ y x = _
  rw [E]
  simp [tensorMatrix, stage_word _ _ (List.nodup_finRange A), target, pairM]

/-- Rational two-bit kernel agrees with the numerical transform used in the
synchronized stage decomposition. -/
theorem pairEntry_complex (y x : bitPair) :
    (pairEntry y x : ℂ) = KernelNormalization.axis y x := by
  rw [KernelNormalization.axis_character, KernelNormalization.normalization_pair]
  rw [Fin.sum_univ_two]
  by_cases hz : y 0 * x 0 + y 1 * x 1 = 0
  · simp [pairEntry, hz, KernelNormalization.character]
  · have hz' : y 0 * x 0 + y 1 * x 1 = 1 := by
      have hbit : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
      exact (hbit _).resolve_left hz
    simp [pairEntry, hz', KernelNormalization.character, OAI.LinearAlgebra.FiniteFourier.digitPhase_apply,
      show (1 : ZMod 2).val = 1 from rfl]

end KernelPass

end NearSquareRoot
end Computability
end OAI
