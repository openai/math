import OAI.Computability.BorderVNP.CubeTeamRowFold
import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords

/-! # Coverage of the actual endpoint roles by the distributed row traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Physical

/-- Every ordered view occurs at exactly its actual owner team and ordinal. -/
def visitEquiv {d : ℕ} {Team : Type*} (owner : Fin d → Team) :
    (Σ team : Team, {q : Fin (d*d) // owner (pairAt d q).1 = team}) ≃ Fin d × Fin d where
  toFun a := pairAt d a.2.val
  invFun p := ⟨owner p.1,finProdFinEquiv p,by simp [pairAt]⟩
  left_inv a := by
    obtain ⟨t,⟨q,hq⟩⟩ := a
    subst t
    simp [pairAt]
    exact Subtype.ext (finProdFinEquiv.apply_symm_apply q)
  right_inv p := by simp [pairAt]

/-- A co-owned strict pair still has two different physical endpoint visits. -/
theorem swapped_ordinals_ne {d : ℕ} {u v : Fin d} (huv : u ≠ v) :
    finProdFinEquiv (u,v) ≠ finProdFinEquiv (v,u) := by
  intro eqn
  exact huv (congrArg Prod.fst (finProdFinEquiv.injective eqn))

/-- Acceptance of every incident row at every physical team checks all unordered
rows, including repeated symbols. The global minimum check then forces the
unique declaration. -/
theorem rows_and_minimum_iff {n d blocks K h : ℕ} {Team : Type*} (owner : Fin d → Team)
    (b s : ℕ) (select : Packet n d blocks → Selector n K h) (D : LengthDeclaration n d) :
    ((∀ team (q : Fin (d*d)), owner (pairAt d q).1 = team →
        ∀ j, D.2 (Sym2.mk (pairAt d q).1 (pairAt d q).2) j =
          subtotals itemRow (crossCount b s select) D.1 (Sym2.mk (pairAt d q).1 (pairAt d q).2) j) ∧
      D.1 = firstMinimum (fun j => ∑ r, D.2 r j)) ↔ passesLengths b s select D := by
  change (_ ∧ _) ↔ (∀ r j, D.2 r j = subtotals _ _ D.1 r j) ∧ _
  apply and_congr_left
  intro _
  constructor
  · intro checks row
    induction row using Sym2.inductionOn with
    | _ u v =>
      have check := checks (owner u) (finProdFinEquiv (u,v)) (by simp [pairAt])
      simpa [pairAt] using check
  · exact fun all _ q _ => all _

/-- The checked rows and the native minimum pin both the cut index and every
length entry to the values obtained from the recovered packet selectors. -/
theorem rows_force_declaration {n d blocks K h : ℕ} {Team : Type*} (owner : Fin d → Team)
    (b s : ℕ) (select : Packet n d blocks → Selector n K h) (D : LengthDeclaration n d)
    (rows : ∀ team (q : Fin (d*d)), owner (pairAt d q).1 = team →
      ∀ j, D.2 (Sym2.mk (pairAt d q).1 (pairAt d q).2) j =
        subtotals itemRow (crossCount b s select) D.1 (Sym2.mk (pairAt d q).1 (pairAt d q).2) j)
    (least : D.1 = firstMinimum (fun j => ∑ r, D.2 r j)) :
    D = (chosen b s select,subtotals itemRow (crossCount b s select) (chosen b s select)) :=
  (passesLengths_iff b s select D).mp ((rows_and_minimum_iff owner b s select D).mp ⟨rows,least⟩)

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
