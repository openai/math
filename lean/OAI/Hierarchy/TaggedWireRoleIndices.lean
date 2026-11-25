import OAI.Hierarchy.ProbeCoreBoard
import OAI.Hierarchy.ProbeExcess

namespace OAI
/-! # Ordinals of the original circuit rows and their public operands -/

noncomputable section
namespace Hierarchy.WireTelescope.SettledMatrix
abbrev Source (r : ℕ) (I A : Type) := Fin r ⊕ (I⊕A)

namespace Layout
variable {r : ℕ} {I A : Type} [Fintype I] [Fintype A]
/-- Permanent physical rows retain their native order. Goods and reserves
follow in separate blocks. Each of these two families has pairwise distinct
original chords in the tagged protocol. -/
def ordinal : Source r I A ≃ Fin (Fintype.card (Source r I A)) :=
  let rest := (Equiv.sumCongr (Fintype.equivFin I) (Fintype.equivFin A)).trans finSumFinEquiv
  ((Equiv.sumCongr (Equiv.refl _) rest).trans finSumFinEquiv).trans
    (finCongr (by simp [Source]))

def numbered := (ordinal (r:=r) (I:=I) (A:=A)).symm

theorem ordinal_paid (e:Fin r) : (ordinal (I:=I) (A:=A) (.inl e)).val=e.val := rfl
theorem ordinal_goods (g:I) :
    (ordinal (r:=r) (A:=A) (.inr (.inl g))).val=r+(Fintype.equivFin I g).val := by
  simp [ordinal,finSumFinEquiv,Fin.addCases]
theorem ordinal_reserve (a:A) :
    (ordinal (r:=r) (I:=I) (.inr (.inr a))).val=r+(Fintype.card I+(Fintype.equivFin A a).val) := by
  simp [ordinal,finSumFinEquiv,Fin.addCases]
end Layout
end Hierarchy.WireTelescope.SettledMatrix

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe
abbrev Goods (h W k : ℕ) := Commodity (Fin (2^h)) (Stages h (2^W)) k
abbrev Catalysts (h W k : ℕ) := Columns h (2^W)×Fin k
namespace RoleProgram
open WireTelescope
abbrev Old h W k edges := SettledMatrix.Source edges (Goods h W k) (Catalysts h W k)

end RoleProgram
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles
end

end OAI
