import OAI.Computability.VPVNP.RAMProcessorChoices
import OAI.Computability.VPVNP.RAMGuessBudget

/-!
# The finite choice generator counts private validator paths

Only strings accepted by the site are counted. Its proven guess bound covers
every such string, so restricting the physical generator to that length
preserves the natural cardinal used in the transcript contraction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProcessorChoices

open BurstRAM RAMLayout

private theorem sum_indicator (pred : List Bool → Bool) (xs : List (List Bool)) :
    (xs.map fun x => (pred x).toNat).sum = (xs.filter pred).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : pred x <;> simp [h, ih, Nat.add_comm]

theorem bounded_count (bound : ℕ) (pred : List Bool → Bool)
    (hb : ∀ bs, pred bs = true → bs.length ≤ bound) :
    ((words bound).map fun x => (pred x).toNat).sum = Nat.card {bs : List Bool // pred bs = true} := by
  classical
  let candidates := (words bound).filter pred
  let found := candidates.toFinset
  have hn : candidates.Nodup := (words_nodup bound).filter _
  have hm (bs : List Bool) : bs ∈ found ↔ pred bs = true := by
    simp only [found, candidates, List.mem_toFinset, List.mem_filter, mem_words]
    exact ⟨And.right, fun h => ⟨hb _ h, h⟩⟩
  let equiv : found ≃ {bs : List Bool // pred bs = true} :=
    ⟨fun x => ⟨x.val, (hm x.val).mp x.property⟩,
      fun x => ⟨x.val, (hm x.val).mpr x.property⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_coe, sum_indicator]
  exact (List.toFinset_card_of_nodup hn).symm

theorem site_choices {w p r k d e : ℕ} (M : PrivateRAM.Machine w p r k) (fuel : ℕ)
    (initial : Word w) (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (shared : RawAssignment d e w) (v : Fin (2^d)) :
    let accepted := fun bs => (M.validateIncident fuel initial (header v) hw hc v (incidentBits shared v) bs).1.isSome
    ((words (2*2^e*(fuel+w))).map fun bs => (accepted bs).toNat).sum =
      Nat.card (M.IncidentPaths fuel initial (header v) hw hc v (incidentBits shared v)) := by
  apply bounded_count
  intro bs hb
  exact M.incident_guesses_le fuel initial header hw hc shared v ⟨bs, hb⟩

end RAMTape.ProcessorChoices

end VPVNP
end Computability
end OAI
