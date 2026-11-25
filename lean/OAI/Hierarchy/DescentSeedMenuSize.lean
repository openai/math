import OAI.Hierarchy.DescentSeedHistogram
import OAI.Hierarchy.DescentPhysicalDegree

namespace OAI
/-! # The normalized site needs at most eight fixed histogram rows -/

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing DescentPhysicalSplit
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1))

theorem seed_digits (tri : N.Trivalent) : (∑v,Fintype.card (Pattern N v))≤8*Fintype.card N.Site := by
  exact (Finset.sum_le_sum (s:=Finset.univ) fun v _ => patterns_le_eight N tri v).trans_eq (by simp [Nat.mul_comm])

end
end Hierarchy.DescentInitialHost

end OAI
