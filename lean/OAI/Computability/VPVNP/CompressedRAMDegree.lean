import OAI.Computability.VPVNP.ExpandedMonomialDegree
import OAI.Computability.VPVNP.CompressionDegreeAssembly

/-!
# Total exponent of each compressed RAM path

The accepting choices of the initial validators have exponent zero. Each
subsequent kernel contributes the degrees of its resident template entries.
On the selected branch the number of occurrences and the degree of every
individual entry obey the bounds of Theorem 7.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting Compression NetworkKernel BurstRAM BurstRAM.PrivateRAM

variable {D base lanes a padding w p r k' e : ℕ} [NeZero D]
variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A}

/-- Every expanded validator path has a selected term chain whose recorded
degrees bound its total parameter exponent. -/
theorem expandedRAMStateCount_degree {b n : ℕ} (M : Machine w p r k') (fuel : ℕ)
    (initial : Word w) (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
    (labels : Fin D ≃ Fin base ⊕ Fin lanes) (hD : 1 < D) (hd : 2 + padding = 2 ^ a)
    (E : StateExecution A b n
      (cursorState labels hD hd (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)))
    (K : E.MapWitnesses κ) (rec : E.Records) (hrec : E.DegreeCovered K rec) :
    let W := expandedRAMStateCount M fuel initial header hw hc labels hD hd
      E.history (E.historyWitnesses K)
    ∀ c : W.Choice, ∃ z : E.Choices, ∀ B, (E.termChain rec z).AllRecordsLe B →
      (∑ l, W.exponents c l) ≤ ∑ v, (E.termChain rec z).occurrences (fun _ => 1) v * B := by
  intro W c
  let bits := (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)
  let I := cursorStateIso labels hD hd (ramSystemOrder D) bits
  let P : Factors Type (paddedNetwork D padding bits) := fun v z =>
    initialChoices M fuel initial header hw hc v (unpadHalf padding v z)
  let inst := I.pushChoiceFintype P fun v z =>
    initialChoicesFintype M fuel initial header hw hc v (unpadHalf padding v z)
  exact (E.history_degreeBound K rec hrec).expandedCount _ _ _ (I.pushFactors P) c

variable {k : Type*} [Field k] {S : BlockSchedule k}

/-- The actual path of (12.2) selects a final network. Its total parameter
degree is bounded by its number of sites, the maximum number of local
occurrences, and the largest degree of an individual map entry. -/
theorem compressedRAMCount_degree (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
    (M : Machine w p r k') (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
    (labels : Fin D ≃ Fin base ⊕ Fin lanes) (hD : 1 < D) (T : ℕ) (hT : T * S.laneBits ≤ lanes) :
    let X := cursorState labels hD (Nat.add_sub_of_le S.degree_bounds.1)
      (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)
    let E := B.execute f hf T hT X
    let W := compressedRAMCount B f hf M fuel initial header hw hc labels hD T hT
    ∀ c : W.Choice, ∃ z : E.Choices, (∑ l, W.exponents c l) ≤
      (E.finalState z).positions * B.growthConstant ^ T *
        (B.growthConstant ^ T * (X.maxWireWidth + 1)) := by
  intro X E W c
  let L := B.growthConstant ^ T * (X.maxWireWidth + 1)
  obtain ⟨z, hz⟩ := expandedRAMStateCount_degree M fuel initial header hw hc labels hD
    (Nat.add_sub_of_le S.degree_bounds.1) E _ _ (B.execute_degreeCovered f hf T hT X) c
  have bounds := B.branch_bounds f hf T hT X z
  refine ⟨z, (hz L bounds.2.2.2.2.1).trans ?_⟩
  calc
    _ ≤ ∑ _ : (E.finalState z).network.Site, B.growthConstant ^ T * L :=
      Finset.sum_le_sum fun v _ => Nat.mul_le_mul_right L (bounds.2.2.2.1 v)
    _ = (E.finalState z).positions * B.growthConstant ^ T * L := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_assoc]
      rfl

end CursorNetwork

end VPVNP
end Computability
end OAI
