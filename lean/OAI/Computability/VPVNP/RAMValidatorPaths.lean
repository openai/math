import OAI.Computability.VPVNP.RAMValidatorWork
import OAI.Computability.VPVNP.RAMPathCount

/-!
# Private binary multiplicity of the executable site validator

A successful site's raw choice string is exactly the concatenation of its
branch bits and its guessed words. Hence one genuine computation path
contributes once to the sum over shared bits of the product of local counts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open BurstRAM RAMLayout RAMMemory

variable {w p r k d e : ℕ}

/-- An accepting binary branch path for a fixed local input. -/
abbrev Machine.IncidentPaths (M : Machine w p r k) (fuel : ℕ) (initial header : Word w)
    (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (v : Fin (2^d)) (inc : Fin (width d (2^e) w) → Bool) :=
  {bs : List Bool // (M.validateIncident fuel initial header hw hc v inc bs).1.isSome = true}

/-- Reading and emitting the successful report is inverse to choosing its
specified bits. Distinct original binary branches remain distinct even when
their continuations coincide. -/
def Machine.incidentPathEquiv (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (bits : RawAssignment d e w)
    (v : Fin (2^d)) :
    M.IncidentPaths fuel initial (header v) hw hc v (BurstRAM.incidentBits bits v) ≃
      SitePaths M.program fuel initial header hw hc bits v := by
  let run := fun bs => (M.validateIncident fuel initial (header v) hw hc v (BurstRAM.incidentBits bits v) bs).1
  let enc := fun (rs : List (Report w)) => rs.flatMap (fun r => guessBits r.events)
  have spec (bs rs) : run bs = some rs ↔ BitValidator M.program fuel initial header hw hc bits v rs ∧ bs = enc rs :=
    M.validateIncident_iff ..
  refine ⟨fun b => ⟨(run b.val).get b.property, ((spec ..).mp (Option.some_get b.property).symm).1⟩,
    fun s => ⟨enc s.val, Option.isSome_iff_exists.mpr ⟨s.val, (spec ..).mpr ⟨s.property, rfl⟩⟩⟩,
    ?_, ?_⟩
  · intro b
    exact Subtype.ext ((spec ..).mp (Option.some_get b.property).symm).2.symm
  · intro s
    apply Subtype.ext
    apply Option.some.inj
    exact (Option.some_get _).trans ((spec ..).mpr ⟨s.property, rfl⟩)

/-- Native capped path count expressed using the actual site machines and
their own private choice strings. -/
theorem Machine.parsimoniousIncidentPaths (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) :
    Nat.card (ActualPaths M.program fuel initial (initialMemory (2^d) header) (withinCaps (2^d) (2^e))) =
      ∑ bits : RawAssignment d e w, ∏ v : Fin (2^d),
        Nat.card (M.IncidentPaths fuel initial (header v) hw hc v (BurstRAM.incidentBits bits v)) := by
  rw [parsimoniousRAMTranscripts M.program fuel initial header hw hc]
  exact Finset.sum_congr rfl fun b _ => Finset.prod_congr rfl fun v _ =>
    (Nat.card_congr (M.incidentPathEquiv fuel initial header hw hc b v)).symm

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
