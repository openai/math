import OAI.Computability.VPVNP.RAMValidatorPaths

/-!
# Finiteness of the private path count for arbitrary incident bits

An accepted binary string is recovered from the reports of the bounded site
simulation. This remains true when the incident bits are supplied independently
of the assignments on the other sites.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open BurstRAM RAMLayout RAMSort

variable {w p r k d e : ℕ}

/-- The accepting site reports fit the bucket and fuel bounds, and their
guess bits recover the entire private branch string. -/
theorem Machine.validateIncident_boundedReports (M : Machine w p r k) (fuel : ℕ)
    (initial header : Word w) (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (v : Fin (2 ^ d))
    (inc : Fin (width d (2 ^ e) w) → Bool) {bs : List Bool} {rs : List (Report w)}
    (h : (M.validateIncident fuel initial header hw hc v inc bs).1 = some rs) :
    (rs.length ≤ 2 * 2 ^ e ∧ ∀ r ∈ rs, r.events.length < fuel) ∧
      bs = rs.flatMap (fun r => guessBits r.events) := by
  let raw := readIncident inc
  let edges := (scanSuccessors hw hc initial v raw).1
  let bucket := M.runBucket fuel (2 ^ d) (2 ^ e) v.val edges.input edges.output bs
  change (if edges.valid then _ else (none, _)).1 = some rs at h
  split at h
  · dsimp only at h
    cases hb : bucket.1 with
    | none =>
      rw [show (M.runBucket fuel (2 ^ d) (2 ^ e) v.val edges.input edges.output bs).1 =
        none from hb] at h
      cases h
    | some ts =>
      rw [show (M.runBucket fuel (2 ^ d) (2 ^ e) v.val edges.input edges.output bs).1 =
        some ts from hb] at h
      change (if (checkSiteMemory (e := e) hw v header raw edges ts).1 then some ts else none) =
        some rs at h
      split at h
      · cases h
        obtain ⟨hs, hbits⟩ := (M.runBucket_iff (Nat.two_pow_pos e)).mp hb
        exact ⟨boundedReports_of_localSegment hs.1.calls
          (hs.1.cost_lt (Nat.two_pow_pos e)).le, hbits⟩
      · cases h
  · cases h

/-- The actual accepting branch strings on a fixed local input form a finite
set, including inputs with inconsistent or malformed messages. -/
instance Machine.finiteIncidentPaths (M : Machine w p r k) (fuel : ℕ)
    (initial header : Word w) (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) (v : Fin (2 ^ d))
    (inc : Fin (width d (2 ^ e) w) → Bool) :
    Finite (M.IncidentPaths fuel initial header hw hc v inc) := by
  let output (b : M.IncidentPaths fuel initial header hw hc v inc) :=
    (M.validateIncident fuel initial header hw hc v inc b.val).1.get b.property
  have spec (b) := M.validateIncident_boundedReports fuel initial header hw hc v inc
    (rs := output b) (Option.some_get b.property).symm
  let encode (b) : BoundedReports w fuel (2 * 2 ^ e) := ⟨output b, (spec b).1⟩
  apply Finite.of_injective encode
  intro b c h
  exact Subtype.ext ((spec b).2.trans ((congrArg
    (fun t : BoundedReports w fuel (2 * 2 ^ e) =>
      t.val.flatMap (fun r => guessBits r.events)) h).trans
    (spec c).2.symm))

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
