import OAI.ThreeFlat.Diagonal.CompressorDemandReader
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Modular evaluation of the old physical demand-word reader -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Demand
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast BigOperators
variable {n w : ℕ}
variable (data : Param → Word w) (m : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value data m vs

theorem totals_word (xs : List (Formula n)) :
    V (RAM.MotifRows.totals xs) = (xs.map V).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (V x + ·) ih

theorem slots_word (d c : ℕ) (f : Fin d → Fin (2^c) → Formula n) :
    V (allSlots d c f) = ∑ h, ∑ u, V (f h u) := by
  simp only [allSlots,totals_word,List.map_map,Function.comp_def,← Fin.sum_univ_def]

theorem slots_nat (d c : ℕ) (f : Fin d → Fin (2^c) → Formula n) (width : ℕ)
    (pars : Param → ℕ) (mem : ℕ → ℕ) (r : Fin n → ℕ) :
    Formula.natural width pars mem r (allSlots d c f) =
      ∑ h, ∑ u, Formula.natural width pars mem r (f h u) := by
  simp only [allSlots,RAM.MotifRows.totals_value,List.map_map,Function.comp_def,← Fin.sum_univ_def]

theorem eval_toggle (g : ArcColumns (Formula n)) (s : Site (Formula n)) :
    (toggle (formulaOps n) g.toColumns s).map V =
      toggle (words m) (g.map V).toColumns (s.map V) := by rfl

theorem eval_thick (g : ArcColumns (Formula n)) (x : Position (Formula n)) :
    V (thickBit (formulaOps n) g.toColumns x) = thickBit (words m) (g.map V).toColumns (x.map V) := by rfl

theorem eval_ends (g : ArcColumns (Formula n)) (d : ℕ) (incoming : Bool) (x : Position (Formula n))
    (i : Formula n) :
    (ends (formulaOps n) g d incoming x i).map V =
      ends (words m) (g.map V) d incoming (x.map V) (V i) := by cases incoming <;> rfl

theorem eval_select (v : Formula n) (yes no : Position (Formula n)) :
    (Position.select (formulaOps n) v yes no).map V =
      if V v=1 then yes.map V else no.map V := by
  by_cases h : V v=1 <;>
    simp [Position.select,Site.select,Position.map,Site.map,formulaOps,Formula.value,RAM.DescriptorExpr.Comparison.test,h]

theorem eval_choose (a b s t : Formula n) :
    V ((formulaOps n).choose a b s t) = if V a=V b then V s else V t := by
  simp [formulaOps,Formula.value,RAM.DescriptorExpr.Comparison.test]

theorem eval_lt (a b s t : Formula n) :
    V (.select .lt a b s t) = if V a<V b then V s else V t := by
  simp [Formula.value,RAM.DescriptorExpr.Comparison.test]

theorem physical_word (p : WidthLayout n) (x : Position (Formula n)) (i : Formula n) :
    V (physical p x i) = (V x.site.base*(p.degree:Word w)+V i)*V p.laneCount+
      (V x.bits+((2^p.colors:ℕ):Word w)*(V x.slot+(p.degree:Word w)*
        (V x.site.tag+V p.tagCount*V x.site.lane))) := rfl

theorem width_word (p : WidthLayout n) (x : Position (Formula n)) (i : Formula n) :
    V (width p x i) = m (V p.table+V (physical p x i)).val := rfl

end ThreeFlat.Diagonal.CompressorPacking.Native.Demand

end OAI
