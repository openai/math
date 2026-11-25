import OAI.ThreeFlat.Diagonal.ShrinkMotif
import OAI.ThreeFlat.Diagonal.SlotCounts

namespace OAI
/-! # One common placement of the shrinking motifs

For the first placement the roles A, C, M share one site, and D, N share
another. For the second placement B, C, N and D, M share the indicated
sites. One deterministic layout is chosen for the full list of motif terms,
so each old vertex has a single destination.
-/

namespace ThreeFlat.Diagonal.ShrinkMotif

/-- The three packed sites are respectively A, B, and the destination of D. -/
def role : Bool → Fin 6 → Fin 3
  | false => ![0,1,0,2,0,2]
  | true => ![0,1,1,2,2,1]

/-- Surviving edge types in the order used by slot regularization. -/
def survivor : Bool → Fin 4 → Fin 8
  | false => ![1,3,5,6]
  | true => ![0,2,4,7]

theorem survivor_distinct (b : Bool) : Function.Injective (survivor b) := by cases b <;> decide

theorem survives_iff (b : Bool) (e : Fin 8) :
    role b (supplySrc e) ≠ role b (supplyDst e) ↔ ∃ i, survivor b i = e := by
  revert b e
  decide

theorem retained_mass (b : Bool) (i : Fin 4) : supplyMass (survivor b i) = SlotEnergy.retainedMass i := by
  cases b <;> fin_cases i <;> rfl

/-- Every old supply edge is retained in exactly one of the two layouts. -/
def twoLayouts : Bool × Fin 4 ≃ Fin 8 where
  toFun i := survivor i.1 i.2
  invFun := ![(true,0),(false,0),(true,1),(false,1),(true,2),(false,2),(false,3),(true,3)]
  left_inv := by decide
  right_inv := by decide

variable {M : Type*} [Fintype M]

/-- Energy of all surviving wires for a single common placement of the
old endpoints. `W` already includes the supply masses and widths. -/
noncomputable def retainedEnergy (W : M → Fin 8 → ℝ) (b : Bool) : ℝ :=
  ∑ j, ∑ i, W j (survivor b i)

/-- Exact tie breaking used when a list of motif selectors is fixed. -/
noncomputable def chooseLayout (W : M → Fin 8 → ℝ) : Bool :=
  if retainedEnergy W false ≤ retainedEnergy W true then false else true

theorem chosen_energy (W : M → Fin 8 → ℝ) :
    2 * retainedEnergy W (chooseLayout W) ≤ ∑ j, ∑ e, W j e := by
  have split : retainedEnergy W false + retainedEnergy W true = ∑ j, ∑ e, W j e := by
    rw [retainedEnergy, retainedEnergy, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← twoLayouts.sum_comp (W j), Fintype.sum_prod_type, Fintype.sum_bool]
    exact add_comm _ _
  rw [← split]
  unfold chooseLayout
  split_ifs <;> linarith

end ThreeFlat.Diagonal.ShrinkMotif

end OAI
