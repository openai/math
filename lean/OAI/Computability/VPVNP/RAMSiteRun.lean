import OAI.Computability.VPVNP.RAMSiteLoop
import OAI.Computability.VPVNP.RAMFinite

/-!
# Binary paths of a site validator

The public bucket size bounds the number of calls independently of incoming
messages. The validator checks the input range before simulating the calls.
Its outgoing check compares an internal send with the actual result, or
requires acceptance on the terminal site. It consumes exactly the local binary
choices and fixed-width read guesses used by those calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- Simulate the private calls assigned to this site, leaving the unused bits. -/
def runSite (P : Program w C) (fuel S H v : ℕ) (c : Cut w) (bits : List Bool) :
    Option (List (Report w) × List Bool) :=
  if c.state.isSome → v * H ≤ c.cost ∧ c.cost < (v + 1) * H then
    runSiteLoop P fuel H ((v + 1) * H) (S * H) (2 * H - 1) c (2 * H - 1) bits
  else none

theorem runSite_iff {P : Program w C} {fuel S H v} {c : Cut w} {bits rs tail}
    (hH : 0 < H) : runSite P fuel S H v c bits = some (rs, tail) ↔
      SiteRun P fuel S H v c rs ∧ bits = rs.flatMap (fun r => guessBits r.events) ++ tail := by
  unfold runSite
  split
  · rename_i hin
    rw [runSiteLoop_iff]
    constructor
    · rintro ⟨hc, hb, hcall, hcap, _, _, hx, he⟩
      exact ⟨⟨hin, hb, hc, hcall, hcap, hx⟩, he⟩
    · rintro ⟨hr, he⟩
      have hcost := hr.cost_lt hH
      have hlen := RAMBuckets.cost_eq_length_add_probes Report.probes rs
      exact ⟨hr.calls, hr.before, hr.call_cap, hr.total_cap, by omega, by omega, hr.crossing, he⟩
  · rename_i hn
    exact ⟨nofun, fun h => (hn h.1.incoming).elim⟩

/-- Exact-use site validator with the successor or terminal check. Later local
record and sorting checks can be applied to the returned reports. -/
def validateSite (P : Program w C) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) : Option (List (Report w)) :=
  (runSite P fuel S H v input bits).bind fun (rs, tail) =>
    if tail = [] then
      match output with
      | some d => if d = input.advance rs then some rs else none
      | none => if (input.advance rs).state = none then some rs else none
    else none

theorem validateSite_iff {P : Program w C} {fuel S H v} {input : Cut w} {output bits rs}
    (hH : 0 < H) : validateSite P fuel S H v input output bits = some rs ↔
      SiteCheck P fuel S H v input output rs ∧ bits = rs.flatMap (fun r => guessBits r.events) := by
  rw [validateSite, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨ts, tail⟩, hrun, htest⟩
    dsimp only at htest
    split at htest
    · rename_i ht
      subst tail
      obtain ⟨hr, hb⟩ := (runSite_iff hH).mp hrun
      cases output <;> dsimp only at htest <;> split at htest <;> simp_all [SiteCheck]
    · contradiction
  · rintro ⟨⟨hsite, hend⟩, rfl⟩
    refine ⟨(rs, []), (runSite_iff hH).mpr ⟨hsite, by simp⟩, ?_⟩
    cases output <;> simp_all

/-- Any further deterministic check of the local reports preserves the exact
correspondence between valid reports and accepting binary inputs. -/
noncomputable def siteBitsEquiv {P : Program w C} {fuel S H v} {input : Cut w} {output}
    (hH : 0 < H) (check : List (Report w) → Prop) :
    {bs : List Bool // ∃ rs, validateSite P fuel S H v input output bs = some rs ∧ check rs} ≃
      {rs : List (Report w) // SiteCheck P fuel S H v input output rs ∧ check rs} := by
  let encode (r : {rs : List (Report w) // SiteCheck P fuel S H v input output rs ∧ check rs}) :
      {bs : List Bool // ∃ rs, validateSite P fuel S H v input output bs = some rs ∧ check rs} :=
    ⟨r.val.flatMap (fun t => guessBits t.events), r.val,
      (validateSite_iff hH).mpr ⟨r.property.1, rfl⟩, r.property.2⟩
  refine (Equiv.ofBijective encode ⟨?_, ?_⟩).symm
  · intro r t he
    have hr := (validateSite_iff hH).mpr (show SiteCheck P fuel S H v input output r.val ∧
        (encode r).val = _ from ⟨r.property.1, rfl⟩)
    have ht := (validateSite_iff hH).mpr (show SiteCheck P fuel S H v input output t.val ∧
        (encode t).val = _ from ⟨t.property.1, rfl⟩)
    rw [he] at hr
    exact Subtype.ext (Option.some.inj (hr.symm.trans ht))
  · intro bs
    obtain ⟨rs, hrun, hc⟩ := bs.property
    obtain ⟨hr, he⟩ := (validateSite_iff hH).mp hrun
    exact ⟨⟨rs, hr, hc⟩, Subtype.ext he.symm⟩

/-- The local path count is unchanged by restricting the ambient space of
reports to the finite domain used for the product of validator counts. -/
noncomputable def boundedSiteBitsEquiv {P : Program w C} {fuel S H v} {input : Cut w} {output}
    (hH : 0 < H) (check : List (Report w) → Prop) :
    {bs : List Bool // ∃ rs, validateSite P fuel S H v input output bs = some rs ∧ check rs} ≃
      {r : BoundedReports w fuel (2 * H) // SiteCheck P fuel S H v input output r.val ∧ check r.val} := by
  refine (siteBitsEquiv hH check).trans ?_
  refine ⟨fun r => ⟨⟨r.val, ?_⟩, r.property⟩, fun r => ⟨r.val.val, r.property⟩,
    fun _ => rfl, fun _ => rfl⟩
  exact boundedReports_of_localSegment r.property.1.1.calls (r.property.1.1.cost_lt hH).le

end BurstRAM

end VPVNP
end Computability
end OAI
