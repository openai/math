import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords
import OAI.Computability.BorderVNP.CubePhysicalDeclarationBudget

/-! # Bound on the lengths actually read from the broadcast

Each pair reserves its selector prefix followed by its crossing words.
For a passing raw broadcast their sum is bounded by equation (8.1).
The bound concerns the decoded fields used for the physical schedule.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open VPVNP VPVNP.MotifBase
open scoped Classical

variable {n d blocks K h : ℕ}

/-- The sum of reserved row lengths agrees exactly with the selected cut
and the single selector word used by each packet. -/
theorem reserved_sum (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (hp : passesLengths b s select D) :
    (∑ r, (D.2 r D.1 + rowSelectorBits n d blocks K h D.1 r)) =
      cutWidth b s select (chosen b s select) +
        Fintype.card (Packet n d blocks)*MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h := by
  obtain rfl := (passesLengths_iff _ _ _ _).mp hp
  simp only [Finset.sum_add_distrib, sum_pair_lengths, sum_rowSelectorBits]

/-- At the advertised grouping coordinate, the total number of bits reserved
by the passing broadcast obeys the paper's communication bound. -/
theorem broadcast_schedule_budget (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (hd : 0 < d) {η : ℝ} (hη : 0 ≤ η)
    (hwidth : ∀ σ : Fin h → Edge (n+1), (∑ e, (payload (onEdge s) σ e : ℝ)) ≤
      2*2^n*Real.sqrt (n+1)*(h*b : ℕ))
    (hsel : (MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h : ℝ) ≤ η*(h*b : ℕ))
    (raw : Broadcast n d (declarationCap n d blocks b h s)) (hp : passesBroadcast b s select raw) :
    ∃ i : Fin (n+1), readCode _ raw.1 = i.val ∧
      ((∑ r, (readCode _ (raw.2 r i) + rowSelectorBits n d blocks K h i r) : ℕ) : ℝ) ≤
        padded n d blocks (h*b)*(2/Real.sqrt (n+1) + (n+1)/d + η) := by
  obtain ⟨i,hi,hD⟩ := hp
  refine ⟨i,hi,?_⟩
  rw [reserved_sum _ _ _ (i,fun r j => readCode _ (raw.2 r j)) hD]
  simpa only [Nat.cast_add,Nat.cast_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    chosen_coordinate_budget b s select hd hη hwidth hsel

end Cube.Physical

end BorderVNP
end Computability
end OAI
