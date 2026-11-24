import OAI.Computability.VPVNP.MotifSelector
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases

/-!
# The six-party motif for the shrinking step

The parties are A, B, C, D, M, N in that order. Each supply edge carries
a layout bit recording the layout in which it survives, and a type from
zero to three. These are the same labels as in `SurvivingSlots`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkMotif

/-- The two demands in the order AB, CD. -/
def demandSource : Bool → Fin 6 | false => 0 | true => 2

/-- Target party of each demand edge, B for the AB demand and D for the CD demand. -/
def demandTarget : Bool → Fin 6 | false => 1 | true => 3

/-- The source party for each of BC, BN, CN, DM and AC, AM, CM, DN. -/
def supplySource : Bool × Fin 4 → Fin 6
  | (l, 0) | (l, 1) => if l then 0 else 1
  | (_, 2) => 2
  | (_, 3) => 3

/-- The target party in the same two supply groups. -/
def supplyTarget : Bool × Fin 4 → Fin 6
  | (_, 0) => 2
  | (l, 1) | (l, 2) => if l then 4 else 5
  | (l, 3) => if l then 5 else 4

private def adjacent (x y : Fin 6) : Prop := ∃ e,
  (supplySource e = x ∧ supplyTarget e = y) ∨ (supplySource e = y ∧ supplyTarget e = x)

private theorem path_to_center (x : Fin 6) : Relation.ReflTransGen adjacent x 2 := by
  fin_cases x
  · exact .single ⟨(true,0), Or.inl ⟨rfl,rfl⟩⟩
  · exact .single ⟨(false,0), Or.inl ⟨rfl,rfl⟩⟩
  · exact .refl
  · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single
      (r := adjacent) (b := 4) ⟨(false,3), Or.inl ⟨rfl,rfl⟩⟩) ⟨(true,2), Or.inr ⟨rfl,rfl⟩⟩
  · exact .single ⟨(true,2), Or.inr ⟨rfl,rfl⟩⟩
  · exact .single ⟨(false,2), Or.inr ⟨rfl,rfl⟩⟩

/-- Connected supply graph with one incident edge at every party for reading selectors. -/
def supply : MotifSelector.Supply (Fin 6) (Bool × Fin 4) where
  src := supplySource
  dst := supplyTarget
  anchor := ![(true,0), (false,0), (true,0), (false,3), (true,2), (false,2)]
  anchor_incident j := by fin_cases j <;> decide
  connected x y := by
    have hsym (i j : Fin 6) (h : adjacent j i) : adjacent i j := by
      obtain ⟨e, he⟩ := h
      exact ⟨e, he.symm⟩
    exact (path_to_center x).trans ((path_to_center y).swap.mono hsym 2 y)

/-- Relative masses of AB and CD. -/
def demandMass : Bool → ℚ | false => 1 / 3 | true => 1

/-- Relative masses in each group of Lemma 6.2. -/
def relativeMass : Fin 4 → ℚ := ![8 / 31, 4 / 31, 40 / 93, 16 / 31]

/-- Relative supply-edge mass indexed by edge type, using the same four masses in each layout. -/
def supplyMass (e : Bool × Fin 4) : ℚ := relativeMass e.2

theorem demandMass_pos (i : Bool) : 0 < demandMass i := by
  cases i <;> norm_num [demandMass]

theorem relativeMass_pos (e : Fin 4) : 0 < relativeMass e := by
  fin_cases e <;> norm_num [relativeMass]

theorem supplyMass_pos (e : Bool × Fin 4) : 0 < supplyMass e := relativeMass_pos e.2

theorem sum_relativeMass : ∑ e, (relativeMass e : ℝ) = 4 / 3 := by
  norm_num [Fin.sum_univ_succ, relativeMass]

end Compression.ShrinkMotif

end VPVNP
end Computability
end OAI
