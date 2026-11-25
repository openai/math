import OAI.ThreeFlat.Routing.UnaryCountNetwork
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # The sparse correction selector cardinality check

Canonical compaction writes a unary string with one true bit for each selected
position. The first forbidden bit is zero exactly when the selector is legal.
-/

noncomputable section
namespace Hierarchy.CorrectionMask

open ThreeFlat
open ThreeFlat.Routing
open scoped Classical

private abbrev P (s : ℕ) := UnaryCount.Pin 0 s

private def test (F : Type*) [Zero F] [One F] (s p : ℕ) : BitNetwork F (Fintype.card (P s)) where
  internal := 0
  cells := 1
  source := fun _ _ => if hp : p < s then
    .pin (Fintype.equivFin (P s) (.inr ⟨p,hp⟩)) else .constant false
  table := fun _ row => if row 0 then 0 else 1

private def relabel (s : ℕ) (i : Fin (Fintype.card (P s))) :
    Option (Fin (Fintype.card (Fin s))) :=
  ((Fintype.equivFin (P s)).symm i).elim Fin.elim0 (fun j => some (Fintype.equivFin _ j))

def network (F : Type*) [Zero F] [One F] (s p : ℕ) : BitNetwork F (Fintype.card (Fin s)) :=
  (UnaryCount.network F 0 s (test F s p)).restrictPins (relabel s)

theorem eval (F : Type*) [CommSemiring F] {s p : ℕ} (mask : Fin s → Bool) :
    TypedWiring.value (network F s p) mask =
      if (Finset.univ.filter (fun i => mask i = true)).card ≤ p then 1 else 0 := by
  let label : Fin 0 → Bool := Fin.elim0
  have hrel : TypedWiring.value (network F s p) mask =
      TypedWiring.value (UnaryCount.network F 0 s (test F s p)) (Sum.elim label mask) := by
    unfold network TypedWiring.value
    rw [BitNetwork.restrictPins_eval]
    apply congrArg (UnaryCount.network F 0 s (test F s p)).eval
    funext i
    cases he : (Fintype.equivFin (P s)).symm i with
    | inl t => exact t.elim0
    | inr t => simp [relabel, he]
  rw [hrel, UnaryCount.network_value]
  simp only [TypedWiring.value,test,BitNetwork.eval,BitNetwork.weight,BitNetwork.factor]
  by_cases h : p < s
  · by_cases hl : p < (Finset.univ.filter (fun i => mask i = true)).card
    · simp [BitSource.read,StableCompaction.compact,StableCompaction.active,h,hl,not_le.mpr hl]
      change ((Finset.univ : Finset (Fin 0 → Bool)).card:F) * 0^(Finset.univ : Finset (Fin 1)).card=0
      norm_num [Finset.card_univ,Fintype.card_fun]
    · simp [BitSource.read,StableCompaction.compact,StableCompaction.active,h,hl,le_of_not_gt hl]
      change ((Finset.univ : Finset (Fin 0 → Bool)).card:F) = 1
      norm_num [Finset.card_univ,Fintype.card_fun]
  · have hc : (Finset.univ.filter (fun i => mask i = true)).card ≤ p :=
      (Finset.card_le_univ _).trans (by simpa using (le_of_not_gt h))
    simp [BitSource.read,h,hc]
    change ((Finset.univ : Finset (Fin 0 → Bool)).card:F) = 1
    norm_num [Finset.card_univ,Fintype.card_fun]

theorem cells (F : Type*) [Zero F] [One F] (s p : ℕ) :
    (network F s p).cells ≤ 32768 * (s+1) * (Nat.log 2 (s+1)+2)^3 + 1 :=
  UnaryCount.network_cells F 0 s (test F s p)

end Hierarchy.CorrectionMask

end
end OAI
