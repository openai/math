import OAI.Computability.BorderVNP.PackedGridRoutedFactors
import OAI.Computability.BorderVNP.ParseBooleanPhysical

/-! # Initial sparse factors for prewired Boolean verifiers

The verifier already has its interior variables on the hidden side of its input type.
The private descriptor treats its ordinary sites as Boolean tables and checks the use
reported at each designated power site against the bit on its physical incidence.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse BorderVNP.ParseBatch VPVNP.BooleanTranscript
open scoped Classical

variable {X W J R : Type} [Fintype X] [Fintype W] [Fintype J] [CommSemiring R]
variable {s : ℕ} (c : Circuit (X ⊕ W) s) (weighted : J → W)
variable (weight : J → Bool → R) (report : J → Port)

/-- The descriptor classifies a site of any prewired weighted Boolean verifier. -/
noncomputable def verifierRule (v : (BooleanLayout.layout c weighted).Site) :
    Rule (BooleanLayout.layout c weighted).network v :=
  if hw : ∃ j, BooleanLayout.weightSite c weighted j = v then
    let j := hw.choose
    let edge := BooleanLayout.weightEdge c weighted j
    .unary (.inl ⟨⟨edge,Or.inr ((BooleanLayout.weightEdge_dst c weighted j).trans hw.choose_spec)⟩,0⟩)
      (report j)
  else
    .truth (fun read => decide (CellBox.localRow (BooleanLayout.layout c weighted).network
      ((BooleanLayout.layout c weighted).tables (BooleanLayout.factor c weight)) v read = 1))

/-- On a true power site the descriptor compares the submitted use for that very index
with the distinguished physical wire. Every declared power source has its own site. -/
theorem verifierRule_at_weight (j : J) (read) (use : Port → Bool) :
    (verifierRule c weighted weight report (BooleanLayout.weightSite c weighted j)).passes read use =
      (read (.inl ⟨⟨BooleanLayout.weightEdge c weighted j,Or.inr (BooleanLayout.weightEdge_dst ..)⟩,0⟩) ==
        use (report j)) := by
  have hw : ∃ i, BooleanLayout.weightSite c weighted i = BooleanLayout.weightSite c weighted j := ⟨j,rfl⟩
  have he : hw.choose = j := (BooleanLayout.weightSite c weighted).injective hw.choose_spec
  simp only [verifierRule,hw,dite_true,Rule.passes,he]

/-- With correctly supplied uses, successful ordinary factors contribute one, and
the recorded bit of a weight site contributes exactly its specified field or polynomial
entry. Rejected ordinary rows have value zero. -/
theorem verifierRule_value (v : (BooleanLayout.layout c weighted).Site)
    (read : CellBox.Lane (BooleanLayout.layout c weighted).network v → Bool) (use : Port → Bool)
    (correct : ∀ (j : J) (hv : BooleanLayout.weightSite c weighted j = v),
      read (.inl ⟨⟨BooleanLayout.weightEdge c weighted j,Or.inr ((BooleanLayout.weightEdge_dst ..).trans hv)⟩,0⟩) =
        use (report j)) :
    (if (verifierRule c weighted weight report v).passes read use then
      if hw : ∃ j, BooleanLayout.weightSite c weighted j = v then weight hw.choose (use (report hw.choose))
      else 1 else 0) = CellBox.localRow (BooleanLayout.layout c weighted).network
        ((BooleanLayout.layout c weighted).tables (BooleanLayout.factor c weight)) v read := by
  by_cases hw : ∃ j, BooleanLayout.weightSite c weighted j = v
  · obtain ⟨j,rfl⟩ := hw
    let h : ∃ i, BooleanLayout.weightSite c weighted i = BooleanLayout.weightSite c weighted j := ⟨j,rfl⟩
    have he : h.choose = j := (BooleanLayout.weightSite c weighted).injective h.choose_spec
    rw [verifierRule_at_weight,dite_eq_left h,he]
    simp [CellBox.localRow,BooleanLayout.weight_table,correct j rfl]
  · have h := BooleanLayout.other_tables_zero_one c weighted weight v
      (fun j h => hw ⟨j,h.symm⟩) (fun e i => read (.inl ⟨e,i⟩)) (fun p i => read (.inr ⟨p,i⟩))
    rcases h with h | h <;> simp [verifierRule,hw,Rule.passes,CellBox.localRow,h]
    exact Eq.symm

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
