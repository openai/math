import OAI.Computability.VPVNP.RAMValidatorPaths

/-!
# A uniform bound on the private bit string of a successful site

Every local binary choice uses one bit, and each admitted read guesses one
full word. These bounds give the finite range for a tape program that chooses
the complete private string, with a single stop at its selected length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMLayout

variable {w : ℕ}

theorem length_guessBits_le (es : List (Event w)) :
    (guessBits es).length ≤ es.length + w * countProbes es := by
  induction es with
  | nil => simp [guessBits, countProbes]
  | cons e es ih =>
    cases e <;> simp only [guessBits, countProbes, List.length_cons, List.length_append,
      length_wordBits, Nat.mul_add, Nat.mul_one] <;> omega

private theorem length_guesses_blocks {C : Type*} {P : Program w C} {s fuel rs}
    (h : LocalSegment P fuel s rs) :
    (rs.flatMap (fun r => guessBits r.events)).length ≤
      rs.length * fuel + w * RAMBuckets.probeCount Report.probes rs := by
  induction rs generalizing s with
  | nil => simp [RAMBuckets.probeCount]
  | cons r rs ih =>
    cases s with
    | none => contradiction
    | some s =>
      have he := length_guessBits_le r.events
      have hf := h.1.length_lt
      have ht := ih h.2
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
        RAMBuckets.probeCount, Nat.mul_add, Report.probes] at *
      omega

/-- This single public length bound works for every incident string arising
from the shared-bit layout, independently of its acceptance or rejection by
other sites. -/
theorem PrivateRAM.Machine.incident_guesses_le {p r k d e : ℕ} (M : PrivateRAM.Machine w p r k)
    (fuel : ℕ) (initial : Word w) (header : ℕ → Word w) (hw : 2 ≤ w)
    (hc : 2^d * 2^e < 2^w) (bits : RawAssignment d e w) (v : Fin (2^d))
    (path : M.IncidentPaths fuel initial (header v) hw hc v (incidentBits bits v)) :
    path.val.length ≤ 2 * 2^e * (fuel+w) := by
  obtain ⟨rs, hs⟩ := Option.isSome_iff_exists.mp path.property
  obtain ⟨hval, he⟩ := (M.validateIncident_iff fuel initial header hw hc bits v path.val rs).mp hs
  have hl := length_guesses_blocks hval.2.1.1.calls
  have hcost := hval.2.1.1.cost_lt (Nat.two_pow_pos e)
  rw [RAMBuckets.cost_eq_length_add_probes] at hcost
  rw [he]
  calc
    _ ≤ _ := hl
    _ ≤ (2*2^e)*fuel + w*(2*2^e) := Nat.add_le_add
      (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by rw [Nat.mul_add, Nat.mul_comm w]

end BurstRAM

end VPVNP
end Computability
end OAI
