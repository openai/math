import OAI.Computability.VPVNP.ShiftedPairing
import OAI.Computability.VPVNP.StateCount
import Lemmata.FockCircuits.FiniteIdentity

/-!
# Dimensions of the two wires in the shifted crossing

The operator indices in Appendix B range over nonvacuum occupation states.
The sigma type used for the integral pairing separates these states by their
positive particle number. Counting that type removes exactly the vacuum.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

private abbrev OccupationsBelow (H : ℕ) :=
  {s : Occupation H // doubledEnergy s ≤ (H : ℤ)}

private def emptyOccupation (H : ℕ) : OccupationsBelow H :=
  ⟨∅, by simp [doubledEnergy]⟩

private def nonvacuumEquiv (H : ℕ) :
    {s : OccupationsBelow H // s ≠ emptyOccupation H} ≃ BoundedState H where
  toFun s := ⟨s.val.val.map Fin.valEmbedding, by
    have hn : s.val.val ≠ ∅ := fun hz => s.prop (Subtype.ext hz)
    exact (Finset.nonempty_iff_ne_empty.mpr hn).map, by
    change Lemmata.FockCircuits.doubledEnergy _ ≤ H
    exact_mod_cast (doubledEnergy_map_val s.val.val).le.trans s.val.prop⟩
  invFun s := by
    have hbound (i : ℕ) (hi : i ∈ s.val) : i < H := by
      have := Finset.single_le_sum (f := fun j : ℕ => 2*j+1) (fun _ _ => Nat.zero_le _) hi
      have := s.prop.2
      omega
    refine ⟨⟨s.val.attachFin hbound, ?_⟩, ?_⟩
    · rw [← doubledEnergy_map_val, Finset.map_valEmbedding_attachFin]
      exact_mod_cast s.prop.2
    · intro he
      have hc := congrArg (fun p : OccupationsBelow H => p.val.card) he
      simp [emptyOccupation] at hc
      exact s.prop.1.ne_empty hc
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finset.map_injective Fin.valEmbedding
    exact Finset.map_valEmbedding_attachFin _
  right_inv s := Subtype.ext (Finset.map_valEmbedding_attachFin _)

/-- The positive particle-number sectors together index exactly the cutoff count
minus the unique empty occupation state. This includes the zero-energy cutoff. -/
theorem crossingState_card (H : ℕ) :
    Fintype.card (Σ m : Fin H, EnergySector H (m.val + 1) H) = cutoffCount H - 1 := by
  classical
  have h := Fintype.card_congr ((Equiv.optionCongr
    ((boundedStateEquivSectors H).symm.trans (nonvacuumEquiv H).symm)).trans
    (Equiv.optionSubtypeNe (emptyOccupation H)))
  rw [Fintype.card_option, occupationCount_eq H H le_rfl] at h
  omega

open Lemmata.FockCircuits.FiniteIdentity (Index)

private abbrev indexEnergy {N : ℕ} (p : Index N) : ℤ :=
  Lemmata.FockCircuits.doubledEnergy p.val

private theorem modeCutoff_card (N : ℕ) (B : ℤ) :
    Fintype.card (Cutoff (indexEnergy (N := N)) B) =
      Fintype.card (Cutoff (doubledEnergy (N := N)) B) := by
  symm
  let toIndex (s : Cutoff (doubledEnergy (N := N)) B) : Cutoff (indexEnergy (N := N)) B :=
    ⟨⟨s.1.map Fin.valEmbedding, Finset.mem_powerset.mpr (by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_range.mpr j.isLt)⟩, (doubledEnergy_map_val s.1).le.trans s.2⟩
  apply Fintype.card_of_bijective (f := toIndex)
  constructor
  · intro s t h
    exact Subtype.ext <| Finset.map_injective Fin.valEmbedding <| congrArg (fun p => p.val.val) h
  · intro p
    have h (i : ℕ) (hi : i ∈ p.val.val) : i < N :=
      Finset.mem_range.mp (Finset.mem_powerset.mp p.val.property hi)
    refine ⟨⟨p.val.val.attachFin h, ?_⟩, Subtype.ext <| Subtype.ext ?_⟩
    · rw [← doubledEnergy_map_val, Finset.map_valEmbedding_attachFin]
      exact p.property
    · exact Finset.map_valEmbedding_attachFin h

/-- Upper bound for the number of finite-mode matrix indices below an integer cutoff. -/
theorem modeCutoff_card_le (N : ℕ) (B : ℤ) :
    Fintype.card (Cutoff (fun p : Index N => (Lemmata.FockCircuits.doubledEnergy p.1 : ℤ)) B) ≤
      cutoffCount B.toNat := by
  rw [modeCutoff_card]
  by_cases h : 0 ≤ B
  · simpa only [Int.toNat_of_nonneg h] using occupationCount_le N B.toNat
  · rw [occupationCount_of_neg N (lt_of_not_ge h)]
    exact Nat.zero_le _

/-- A finite-mode matrix with at least `E` modes realizes every state at energy at most `E`. -/
theorem modeCutoff_card_eq (N E : ℕ) (h : E ≤ N) :
    Fintype.card (Cutoff (fun p : Index N => (Lemmata.FockCircuits.doubledEnergy p.1 : ℤ)) E) =
      cutoffCount E :=
  (modeCutoff_card N E).trans (occupationCount_eq N E h)

end Crossing

end VPVNP
end Computability
end OAI
