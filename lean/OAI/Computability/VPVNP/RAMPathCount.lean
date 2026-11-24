import OAI.Computability.VPVNP.RAMBitTranscript
import OAI.Computability.VPVNP.RAMFinite

/-!
# Counting RAM paths as a contraction of local validators

For every shared-bit assignment, the factor at a site is the number of its
successful local branch histories. All these sets are finite, even for
malformed messages. Summing their product gives the genuine capped RAM
path count in Lemma 10.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMLayout RAMMemory

variable {d e w : ℕ} {C : Type*}

/-- Lists of call reports accepted by a single site's validator for the given shared-bit
assignment. -/
abbrev SitePaths (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (bits : RawAssignment d e w) (v : Fin (2^d)) :=
  {rs : List (Report w) // BitValidator P fuel initial header hw hc bits v rs}

instance (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (bits : RawAssignment d e w) (v : Fin (2^d)) :
    Finite (SitePaths P fuel initial header hw hc bits v) := by
  let pack (r : SitePaths P fuel initial header hw hc bits v) : BoundedReports w fuel (2 * 2^e) :=
    ⟨r.val, boundedReports_of_localSegment r.property.2.1.1.calls
      (r.property.2.1.1.cost_lt (Nat.two_pow_pos e)).le⟩
  exact Finite.of_injective pack fun _ _ h => Subtype.ext (congrArg (fun t : BoundedReports w fuel (2 * 2^e) => t.val) h)

instance (P : Program w C) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w) (d e : ℕ) :
    Finite (ActualPaths P fuel initial (initialMemory (2^d) header) (withinCaps (2^d) (2^e))) :=
  finite_actualPaths (maxCalls := 2^d * 2^e) (fun _ h => h.1)

/-- Lemma 10.1. The sites use the exact bit layout of (10.1), with the
first and last successor fields clamped. -/
theorem parsimoniousRAMTranscripts (P : Program w C) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) :
    Nat.card (ActualPaths P fuel initial (initialMemory (2^d) header) (withinCaps (2^d) (2^e))) =
      ∑ bits : RawAssignment d e w, ∏ v : Fin (2^d),
        Nat.card (SitePaths P fuel initial header hw hc bits v) := by
  rw [Nat.card_congr (bitTranscriptEquiv P fuel initial header hw hc),
    Nat.card_congr (siteWitnessEquiv (BitValidator P fuel initial header hw hc)), Nat.card_sigma]
  simp only [Nat.card_pi]

end BurstRAM

end VPVNP
end Computability
end OAI
