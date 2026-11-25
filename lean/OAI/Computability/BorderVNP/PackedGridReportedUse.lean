import OAI.Computability.BorderVNP.PackedGridVerifierFactors
import OAI.Computability.BorderVNP.ParseBooleanPowerSites
import OAI.Computability.BorderVNP.DiagonalInitialSiteWords

/-! # Matching the reported use bit to the verifier's actual power word

At its original site, the selected use is read from the designated physical edge.
The equation holds for an unused exponent position as well as a selected one.
This is the value compared by the one-copy sparse unary descriptor, independently
of the number of other powers later hosted in the same public cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse ParseBatch Diagonal.CellEntries VPVNP.BooleanTranscript
open scoped Classical
variable {X W Param Gadget : Type} [Fintype X] [Fintype W] [Fintype Param]
    {s b : ℕ} (c : Circuit (X ⊕ W) s) (weighted : Param × Fin b → W)

/-- The original PowerWords selected bit equals the weight site's actual incident bit
for either value, including zero. -/
theorem power_selected_eq (j : Param × Fin b) (a x) :
    ((BooleanLayout.powerSites (Gadget := Gadget) c weighted).toWords.selected
      (BooleanLayout.weightSite c weighted j) a x ((),j)) =
      a ⟨BooleanLayout.weightEdge c weighted j, Or.inr (BooleanLayout.weightEdge_dst ..)⟩ 0 := by
  have owner : (BooleanLayout.powerSites (Gadget := Gadget) c weighted).site ((),j) =
      BooleanLayout.weightSite c weighted j := rfl
  simp only [PowerSites.toWords,owner,true_and,BooleanLayout.powerTags_at]
  cases hx : a ⟨BooleanLayout.weightEdge c weighted j, Or.inr (BooleanLayout.weightEdge_dst ..)⟩ 0 with
  | false =>
    have hc : counters (1 : Entry Param Gadget) = (0,0) := rfl
    simp [unary,hc]
  | true =>
    have h : Finsupp.single j.1 (2^j.2.val : ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr (Nat.two_pow_pos _).ne'
    simp [unary,h]

/-- A successful one-copy sparse unary guard identifies the reported physical bit with
the actual named use recovered from the tagged source network. -/
theorem reported_selected (report : Param × Fin b → Port) (j : Param × Fin b) (a x) (use : Port → Bool)
    (passing : (verifierRule c weighted BooleanLayout.powerWeight report
      (BooleanLayout.weightSite c weighted j)).passes
        (fun | .inl ⟨e,i⟩ => a e i | .inr ⟨p,i⟩ => x p i) use = true) :
    use (report j) = (BooleanLayout.powerSites (Gadget := Gadget) c weighted).toWords.selected
      (BooleanLayout.weightSite c weighted j) a x ((),j) := by
  rw [power_selected_eq]
  rw [verifierRule_at_weight] at passing
  exact (eq_of_beq passing).symm

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
