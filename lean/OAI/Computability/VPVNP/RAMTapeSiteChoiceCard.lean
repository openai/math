import OAI.Computability.VPVNP.RAMTapeSiteGraphInput
import OAI.Computability.VPVNP.RAMProcessorChoiceCount

/-! # Cardinal of the bounded choice strings on the parsed incident tape -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteCutBank

open BurstRAM RAMLayout PrivateRAM

variable {d e w p r k : ℕ} (x : Input d e w) (T : Template p r k) (operands : Fin k → Word w)

/-- Test whether the instantiated private program’s incident validator succeeds on the given
site and choice string. -/
def Input.accepts (bs : List Bool) : Bool :=
  ((T.instantiate w operands).validateIncident (x.n^x.u) x.initialWord x.headerWord x.word_ge_two
    x.cap_lt x.v (RAMLayout.incidentBits x.sends x.v) bs).1.isSome

/-- Cardinality of the private incident paths for the instantiated table, parsed site, and
instruction fuel. -/
noncomputable def Input.pathCard :=
  Nat.card ((T.instantiate w operands).IncidentPaths (x.n^x.u) x.initialWord x.headerWord x.word_ge_two
    x.cap_lt x.v (RAMLayout.incidentBits x.sends x.v))

theorem Input.choiceCard :
    ((ProcessorChoices.words (2*2^e*(x.n^x.u+w))).map (fun bs => (x.accepts T operands bs).toNat)).sum =
      x.pathCard T operands := by
  let shared := (sendArraysEquiv d (2^e) w).symm x.sends
  have h := ProcessorChoices.site_choices (T.instantiate w operands) (x.n^x.u) x.initialWord
    (fun _ => x.headerWord) x.word_ge_two x.cap_lt shared x.v
  simpa only [BurstRAM.incidentBits, shared, Equiv.apply_symm_apply, Input.pathCard, Input.accepts] using h

theorem Input.invalid_choice (hinv : ¬x.valid) (bs : List Bool) : x.accepts T operands bs = false := by
  have he := scanSuccessors_spec x.word_ge_two x.cap_lt x.initialWord x.v (sortIncident x.sends x.v)
    x.sends (sortIncident_offset x.sends x.v)
  have h : x.summary.valid = false := Bool.eq_false_iff.mpr (fun hp => hinv (he.valid_iff.mp hp))
  change (if x.summary.valid then _ else (none, _)).1.isSome = false
  rw [h]; rfl

theorem Input.invalid_pathCard (hinv : ¬x.valid) : x.pathCard T operands = 0 := by
  rw [← x.choiceCard]
  simp [x.invalid_choice T operands hinv]

end RAMTape.SiteCutBank

end VPVNP
end Computability
end OAI
