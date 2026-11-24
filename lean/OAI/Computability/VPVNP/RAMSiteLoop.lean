import OAI.Computability.VPVNP.RAMLocalRun
import OAI.Computability.VPVNP.RAMSuccessor

/-!
# Streaming the private choices of a site

The site starts calls until its incoming state halts or the cumulative charge
reaches the next bucket. A call may cross that boundary, subject to the three
remaining charge limits. Each call leaves a suffix for its successor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- Continue from the unused suffix and keep the current call's report. -/
def collectCall (call : Option (Report w × List Bool))
    (next : Report w → List Bool → Option (List (Report w) × List Bool)) :
    Option (List (Report w) × List Bool) :=
  call.bind fun (r, bs) => (next r bs).map fun (rs, tail) => (r :: rs, tail)

private theorem collectCall_ne_nil (call : Option (Report w × List Bool))
    (next : Report w → List Bool → Option (List (Report w) × List Bool)) (tail : List Bool) :
    collectCall call next ≠ some ([], tail) := by
  simp [collectCall, Option.bind_eq_some_iff]

private theorem collectCall_cons (call : Option (Report w × List Bool))
    (next : Report w → List Bool → Option (List (Report w) × List Bool))
    (r : Report w) (rs : List (Report w)) (tail : List Bool) :
    collectCall call next = some (r :: rs, tail) ↔
      ∃ bs, call = some (r, bs) ∧ next r bs = some (rs, tail) := by
  simp only [collectCall, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.exists,
    Prod.mk.injEq, List.cons.injEq]
  constructor
  · rintro ⟨_, bs, hc, _, _, hn, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨bs, hc, hn⟩
  · rintro ⟨bs, hc, hn⟩
    exact ⟨r, bs, hc, rs, tail, hn, ⟨rfl, rfl⟩, rfl⟩

/-- Execute consecutive charged calls in a bucket. `steps` bounds the number
of calls and `siteLeft` bounds their total startup and probe charges. -/
def runSiteLoop (P : Program w C) (fuel H boundary globalCap steps : ℕ) (c : Cut w)
    (siteLeft : ℕ) (bits : List Bool) : Option (List (Report w) × List Bool) :=
  if c.cost ≤ globalCap then
    match c.state with
    | none => some ([], bits)
    | some s =>
      if c.cost < boundary then
        match steps with
        | 0 => none
        | n + 1 =>
          collectCall (runChargedCall P fuel (P.start s) H (globalCap - c.cost) siteLeft bits).output
            (fun r bs => runSiteLoop P fuel H boundary globalCap n (c.advance [r])
              (siteLeft - (1 + r.probes)) bs)
      else some ([], bits)
  else none
termination_by structural steps

/-- The loop uses precisely the binary guesses of the successful reports. It
may return a running state only at or past the next bucket boundary. -/
theorem runSiteLoop_iff {P : Program w C} {fuel H boundary globalCap steps : ℕ} {c : Cut w}
    {siteLeft : ℕ} {bits tail : List Bool} {rs : List (Report w)} :
    runSiteLoop P fuel H boundary globalCap steps c siteLeft bits = some (rs, tail) ↔
      LocalSegment P fuel c.state rs ∧ RAMBuckets.StartsBefore Report.probes boundary c.cost rs ∧
      (∀ r ∈ rs, 1 + r.probes ≤ H) ∧ (c.advance rs).cost ≤ globalCap ∧
      RAMBuckets.cost Report.probes rs ≤ siteLeft ∧ rs.length ≤ steps ∧
      ((c.advance rs).state.isSome → boundary ≤ (c.advance rs).cost) ∧
      bits = rs.flatMap (fun r => guessBits r.events) ++ tail := by
  induction rs generalizing steps c siteLeft bits with
  | nil =>
    rw [runSiteLoop]
    simp only [Cut.advance_nil, LocalSegment, RAMBuckets.StartsBefore, RAMBuckets.cost,
      List.length_nil, List.flatMap_nil, List.nil_append, Nat.zero_le, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, true_and]
    by_cases hc : c.cost ≤ globalCap
    · cases c.state with
      | none => simp [hc]
      | some s =>
        by_cases hb : c.cost < boundary
        · cases steps <;> simp [hc, hb, collectCall_ne_nil, Nat.not_le.mpr hb]
        · simp [hc, hb, Nat.le_of_not_gt hb]
    · simp [hc]
  | cons r rs ih =>
    rw [runSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases c.state with
      | none => simp [hc, LocalSegment]
      | some s =>
        by_cases hb : c.cost < boundary
        · cases steps with
          | zero => simp [hc, hb]
          | succ n =>
            simp only [hc, hb, ↓reduceIte, collectCall_cons, runChargedCall_iff, ih,
              LocalSegment, RAMBuckets.StartsBefore, List.forall_mem_cons, List.length_cons,
              Nat.succ_le_succ_iff, List.flatMap_cons, List.append_assoc]
            simp only [Cut.advance, RAMBuckets.cost, Nat.add_zero, endState, Nat.add_assoc]
            constructor
            · rintro ⟨bs, ⟨hcall, hH, _, hsite, he⟩, hseg, hbefore, hcalls, hcap,
                hleft, hlen, hcross, hbs⟩
              exact ⟨⟨hcall, hseg⟩, ⟨trivial, hbefore⟩, ⟨hH, hcalls⟩, hcap,
                by omega, hlen, hcross, he.trans (congrArg (guessBits r.events ++ ·) hbs)⟩
            · rintro ⟨⟨hcall, hseg⟩, ⟨_, hbefore⟩, ⟨hH, hcalls⟩, hcap, hsite, hlen, hcross, he⟩
              exact ⟨_, ⟨hcall, hH, by omega, by omega, he⟩, hseg, hbefore, hcalls,
                hcap, by omega, hlen, hcross, rfl⟩
        · simp [hc, hb, RAMBuckets.StartsBefore]
    · have hn : ¬ (c.advance (r :: rs)).cost ≤ globalCap := by
        change ¬ c.cost + _ ≤ _
        omega
      simp [hc, hn]

end BurstRAM

end VPVNP
end Computability
end OAI
