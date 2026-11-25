import OAI.Computability.BorderVNP.CubeGreedy

/-!
# Uniqueness of the pair-length declaration

Given the selectors in Section 8.2, the label-pair row of each packet or singleton
depends on the chosen grouping coordinate. Its contributions to all coordinate cuts
are independent of that choice. Summing rows therefore recovers the same global cut
vector for every proposed grouping, forcing the least minimizing coordinate and then
each individual row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

variable {E R : Type*} [Fintype E] [Fintype R] [DecidableEq R] {n : ℕ}

/-- Pair subtotals with rows defined by the proposed coordinate. The row type
can, in particular, be the unordered pairs of alphabet symbols including repetitions. -/
def subtotals (row : Fin (n+1) → E → R) (cross : E → Fin (n+1) → ℕ)
    (i : Fin (n+1)) (r : R) (j : Fin (n+1)) :=
  ∑ e : E, if row i e = r then cross e j else 0

/-- Every packet and singleton contributes to exactly one row. -/
theorem sum_subtotals (row : Fin (n+1) → E → R) (cross : E → Fin (n+1) → ℕ)
    (i j : Fin (n+1)) : ∑ r : R, subtotals row cross i r j = ∑ e, cross e j := by
  unfold subtotals
  rw [Finset.sum_comm]
  simp

/-- A passing declaration satisfies every local row check and the public least-minimizer rule. -/
def passes (row : Fin (n+1) → E → R) (cross : E → Fin (n+1) → ℕ)
    (decl : Fin (n+1) × (R → Fin (n+1) → ℕ)) : Prop :=
  (∀ r j, decl.2 r j = subtotals row cross decl.1 r j) ∧
    decl.1 = firstMinimum (fun j ↦ ∑ r, decl.2 r j)

/-- Each tuple of valid selectors has exactly one passing coordinate and length declaration. -/
theorem existsUnique_declaration (row : Fin (n+1) → E → R) (cross : E → Fin (n+1) → ℕ) :
    ∃! decl, passes row cross decl := by
  let i := firstMinimum (fun j ↦ ∑ e, cross e j)
  refine ⟨(i,subtotals row cross i), ⟨fun _ _ ↦ rfl, ?_⟩, ?_⟩
  · simp only [sum_subtotals,i]
  · rintro ⟨k,rows⟩ ⟨hrows,hk⟩
    change (∀ r j, rows r j = subtotals row cross k r j) at hrows
    change k = firstMinimum (fun j ↦ ∑ r, rows r j) at hk
    simp_rw [hrows,sum_subtotals] at hk
    exact Prod.ext hk (by ext r j; exact (hrows r j).trans (by rw [hk]))

end Cube

end BorderVNP
end Computability
end OAI
