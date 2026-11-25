import OAI.Computability.BorderVNP.CellProfileGenerator
import OAI.Computability.BorderVNP.CellGeneratorDepth

/-! # Fixed interpreter depths for the complete profile descriptor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open Prefix
open CellMacro.Address (depth)

private theorem wordIs_fitsAddr (as : List NatExpr) (j d : ℕ) (h : ∀ a ∈ as, depth a+1 ≤ d) :
    (wordIs as j).FitsAddr d := by
  induction as generalizing j with
  | nil => trivial
  | cons a as ih =>
    refine ⟨(Term.equal_fitsAddr ..).mpr ⟨h _ List.mem_cons_self,trivial⟩,
      ih _ (fun a ha => h _ (.tail _ ha))⟩

/-- A match uses the fixed-depth port formula with one stack-offset adjustment. -/
theorem selectTerm_fitsAddr (off : ℕ) (p : Port) (w t : ℕ) (i : NatExpr) {d : ℕ}
    (hd : depth i+5 ≤ d) : (selectTerm off p w t i).FitsAddr d := by
  apply wordIs_fitsAddr
  intro a ha
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
  simp [portExpr,Port.expr,depth]; omega

private theorem rangeGen_fitsDepth (off copies : ℕ) (s : Port) (w t : ℕ) :
    (rangeGen off copies s w t).FitsDepth 8 3 := by
  refine ⟨by decide,by simp [depth],Term.guard_fitsDepth _ (Term.any_fitsAddr _ _ ?_) _⟩
  intro f hf
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp hf
  exact selectTerm_fitsAddr _ _ _ _ _ (by decide)

private theorem termGen_fitsDepth (base off copies : ℕ) (s : Port) (w t adv : ℕ) :
    (termGen base off copies s w t adv).FitsDepth 8 3 := by
  constructor
  · exact generator_fitsDepth _ _ _ _ (by decide) (selectTerm_fitsAddr _ _ _ _ _ (by decide)) (by decide)
  · apply Term.guard_fitsDepth
    split <;> simp [Term.FitsAddr,flagTerm,depth]

private theorem routeGen_fitsDepth (base off copies : ℕ) (s : Port) (w terms : ℕ) (r : Route) :
    (routeGen base off copies s w terms r).FitsDepth 8 3 := by
  refine ⟨Term.guard_fitsDepth (.lit _) trivial _,by decide,by simp [depth],by decide,by simp [depth],by decide,by simp [depth],?_⟩
  apply Term.guard_fitsDepth
  simp only [laneTest,Term.implies,Term.FitsAddr,Term.equal_fitsAddr]
  refine ⟨⟨selectTerm_fitsAddr _ _ _ _ _ (by decide),?_⟩,?_,?_⟩ <;>
    simp [flagTerm,Term.FitsAddr,depth,portExpr,Port.expr]

/-- Three lexical branch/loop levels and eight arithmetic levels suffice for every
profile, regardless of the histogram, route count, repeated copies and wire offsets. -/
theorem profileGen_fitsDepth (base off copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ)
    (routes : List Route) : (profileGen base off copies s w hist routes).FitsDepth 8 3 := by
  refine ⟨rangeGen_fitsDepth .., sequence_fitsDepth _ ?_, sequence_fitsDepth _ ?_⟩
  · intro x hx; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    exact termGen_fitsDepth ..
  · intro x hx; obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
    exact routeGen_fitsDepth ..

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
