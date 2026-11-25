import OAI.Computability.BorderVNP.CellProfileGenerator
import OAI.Computability.BorderVNP.CellPrefixLexical

/-! # Lexical indices in the complete compact profile checker -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Profile

open Prefix

/-- A static term match reads lanes of the given symbolic copy only. -/
theorem selectTerm_lexical_le (off : ℕ) (p : Port) (w t : ℕ) (i : NatExpr) :
    (selectTerm off p w t i).lexical ≤ i.lexical := by
  apply wordIs_lexical_le
  intro a ha
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
  simp [portExpr,NatExpr.lexical]

private theorem rangeGen_lexical_le (off copies : ℕ) (s : Port) (w terms : ℕ) :
    (rangeGen off copies s w terms).lexical ≤ 0 := by
  simp only [rangeGen,Stmt.lexical,NatExpr.lexical,zero_max,Term.guard_lexical]
  apply Term.any_lexical_le
  intro a ha
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
  exact selectTerm_lexical_le ..

private theorem termGen_lexical_le (base off copies : ℕ) (s : Port) (w t adv : ℕ) :
    (termGen base off copies s w t adv).lexical ≤ 1 := by
  apply max_le
  · have h := generator_lexical_le (termBase base copies t) copies copies (selectTerm off s w t)
    have h₁ := selectTerm_lexical_le off s w t (.index 0)
    change _ ≤ 0 at h₁
    omega
  · rw [Term.guard_lexical]
    split <;> simp [Term.lexical,NatExpr.lexical]

private theorem routeGen_lexical_le (base off copies : ℕ) (s : Port) (w terms : ℕ) (r : Route) :
    (routeGen base off copies s w terms r).lexical ≤ 2 := by
  simp only [routeGen,Stmt.lexical,Term.guard_lexical,Term.lexical,NatExpr.lexical,zero_max,
    laneTest,Term.implies_lexical,Term.equal_lexical,flagTerm_lexical,portExpr,Port.expr_lexical,max_le_iff]
  have h := selectTerm_lexical_le off s w r.term (.index 2)
  change _ ≤ 2 at h
  omega

/-- The deepest three-loop route reads copy index 2, candidate index 1, and lane
index 0. All other profile checks stay within this same absolute index bound. -/
theorem profileGen_lexical_le (base off copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ) (routes : List Route) :
    (profileGen base off copies s w hist routes).lexical ≤ 2 := by
  apply max_le ((rangeGen_lexical_le ..).trans (by decide))
  apply max_le <;> apply sequence_lexical_le <;> intro a ha <;> obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
  · exact (termGen_lexical_le ..).trans (by decide)
  · exact routeGen_lexical_le ..

end CellSparse.Profile

end BorderVNP
end Computability
end OAI
