import OAI.Computability.VPVNP.RAMLocalWork
import OAI.Computability.VPVNP.RAMSiteRun

/-!
# Work of the bucket's private call loop

The metered loop follows the same calls as `runSiteLoop`. It reserves a fixed
control charge on each visit, including the final check, and counts dispatches,
charged probes and reserved guess slots for each attempted call. On success it
uses the accumulated probe count to advance the cut in constant time.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- Result and word-work charge for one site’s private call loop, including paths that stop
with a failed check. -/
structure MeteredSiteRun (w : ℕ) where
  /-- On success, the site’s call reports in order and the suffix of the private bit stream
  left for later processing. -/
  output : Option (List (Report w) × List Bool)
  /-- Total charge for loop control, instruction dispatch, external probes, and private guesses
  on the simulated path. -/
  work : ℕ

/-- Meter the call loop on every input. The charge `controlCharge` covers a
fixed set of loop checks and counter updates per visit. The call charge covers
the instruction dispatch, one slot per charged probe, and the individual
binary guesses. -/
def meteredSiteLoop (P : Program w C) (controlCharge fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) : MeteredSiteRun w :=
  if c.cost ≤ globalCap then
    match c.state with
    | none => ⟨some ([], bits), controlCharge⟩
    | some s =>
      if c.cost < boundary then
        match steps with
        | 0 => ⟨none, controlCharge⟩
        | n + 1 =>
          let t := runChargedCall P fuel (P.start s) H (globalCap - c.cost) siteLeft bits
          let work := controlCharge + (t.instructions + t.probes + t.guessWork)
          match t.output with
          | none => ⟨none, work⟩
          | some (r, bs) =>
            let charge := 1 + t.probes
            let rest := meteredSiteLoop P controlCharge fuel H boundary globalCap n
              ⟨c.cost + charge, r.result⟩ (siteLeft - charge) bs
            ⟨rest.output.map (fun (rs, tail) => (r :: rs, tail)), work + rest.work⟩
      else ⟨some ([], bits), controlCharge⟩
  else ⟨none, controlCharge⟩
termination_by structural steps

/-- The counters, including the constant-time cost update, preserve the exact
result of the private choice stream. -/
theorem meteredSiteLoop_output_eq (P : Program w C) (controlCharge fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) :
    (meteredSiteLoop P controlCharge fuel H boundary globalCap steps c siteLeft bits).output =
      runSiteLoop P fuel H boundary globalCap steps c siteLeft bits := by
  induction steps generalizing c siteLeft bits with
  | zero =>
    rw [meteredSiteLoop, runSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases c.state <;> simp [hc]
      split <;> rfl
    · simp [hc]
  | succ n ih =>
    rw [meteredSiteLoop, runSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases hs : c.state with
      | none => simp [hc]
      | some s =>
        by_cases hb : c.cost < boundary
        · simp only [hc, hb, ↓reduceIte]
          let t := runChargedCall P fuel (P.start s) H (globalCap - c.cost) siteLeft bits
          change _ = t.output.bind (fun (r, bs) =>
              (runSiteLoop P fuel H boundary globalCap n (c.advance [r])
                (siteLeft - (1 + r.probes)) bs).map (fun (rs, tail) => (r :: rs, tail)))
          cases ht : t.output with
          | none => rfl
          | some z =>
            obtain ⟨r, bs⟩ := z
            have hp : t.probes = r.probes := runChargedCall_probes_eq ht
            dsimp only [t] at hp
            simp only [hp, Option.bind_some, ih, Cut.advance, RAMBuckets.cost, endState, Nat.add_zero]
        · simp [hc, hb]
    · simp [hc]

/-- Arbitrary incoming cuts and private bit streams satisfy the same bound,
including paths that reject after partially simulating a call. -/
theorem siteWork_le (P : Program w C) (controlCharge fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) :
    (meteredSiteLoop P controlCharge fuel H boundary globalCap steps c siteLeft bits).work ≤
      (steps + 1) * (controlCharge + 3 * fuel + w * H) := by
  let perVisit := controlCharge + 3 * fuel + w * H
  have hcontrol : controlCharge ≤ perVisit := by dsimp [perVisit]; omega
  have hbase (n : ℕ) : controlCharge ≤ (n + 1) * perVisit := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  induction steps generalizing c siteLeft bits with
  | zero =>
    rw [meteredSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases c.state <;> simp only [hc, ↓reduceIte]
      · exact hbase 0
      · split <;> exact hbase 0
    · simp only [hc, ↓reduceIte]
      exact hbase 0
  | succ n ih =>
    rw [meteredSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases hs : c.state with
      | none => simpa only [hc, ↓reduceIte] using hbase (n + 1)
      | some s =>
        by_cases hb : c.cost < boundary
        · simp only [hc, hb, ↓reduceIte]
          let t := runChargedCall P fuel (P.start s) H (globalCap - c.cost) siteLeft bits
          have hprobe : min H (min (globalCap - c.cost) siteLeft) - 1 ≤ H :=
            (Nat.sub_le _ _).trans (min_le_left _ _)
          have hcall := runChargedCall_totalWork_le P fuel (P.start s) H (globalCap - c.cost) siteLeft bits
          have hwork : controlCharge + (t.instructions + t.probes + t.guessWork) ≤ perVisit := by
            have := Nat.mul_le_mul_left w hprobe
            dsimp only [t, perVisit]
            dsimp only at hcall
            omega
          cases ht : (runChargedCall P fuel (P.start s) H (globalCap - c.cost) siteLeft bits).output with
          | none =>
            change controlCharge + _ ≤ (n + 1 + 1) * perVisit
            rw [Nat.add_mul, Nat.one_mul]
            exact hwork.trans (by omega)
          | some z =>
            obtain ⟨r, bs⟩ := z
            have htail := ih ⟨c.cost + (1 + t.probes), r.result⟩ (siteLeft - (1 + t.probes)) bs
            change controlCharge + _ + _ ≤ (n + 1 + 1) * perVisit
            rw [Nat.add_mul, Nat.one_mul]
            exact Nat.add_le_add hwork htail |>.trans_eq (Nat.add_comm _ _)
        · simpa only [hc, hb, ↓reduceIte] using hbase (n + 1)
    · simpa only [hc, ↓reduceIte] using hbase (n + 1)

/-- Scan each event once, counting the probes and the operations to advance
the cursor, inspect the tag and update the count. -/
private def countProbesWork : List (Event w) → ℕ × ℕ
  | [] => (0, 1)
  | e :: es =>
    let t := countProbesWork es
    (e.probeCharge + t.1, 4 + t.2)

private theorem countProbesWork_spec (es : List (Event w)) :
    countProbesWork es = (countProbes es, 4 * es.length + 1) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp [countProbesWork, ih, countProbes, Event.probeCharge] <;> omega

/-- Compute the outgoing cost and state in one pass over the reports and their
events. Six further operations per report cover advancing the cursor, reading
the persistent state, and updating the cost. -/
def meteredAdvance (c : Cut w) : List (Report w) → Cut w × ℕ
  | [] => (c, 1)
  | r :: rs =>
    let p := countProbesWork r.events
    let rest := meteredAdvance ⟨c.cost + (1 + p.1), r.result⟩ rs
    (rest.1, 6 + p.2 + rest.2)

theorem meteredAdvance_result (c : Cut w) (rs : List (Report w)) :
    (meteredAdvance c rs).1 = c.advance rs := by
  induction rs generalizing c with
  | nil => simp [meteredAdvance]
  | cons r rs ih =>
    simp [meteredAdvance, countProbesWork_spec, ih, Cut.advance, RAMBuckets.cost,
      Report.probes, endState, Nat.add_assoc]

theorem meteredAdvance_work_le (c : Cut w) (rs : List (Report w)) (fuel : ℕ)
    (h : ∀ r ∈ rs, r.events.length < fuel) :
    (meteredAdvance c rs).2 ≤ 1 + rs.length * (7 + 4 * fuel) := by
  induction rs generalizing c with
  | nil => simp [meteredAdvance]
  | cons r rs ih =>
    have hr := h r List.mem_cons_self
    have ht := ih ⟨c.cost + (1 + countProbes r.events), r.result⟩ (fun s hs => h s (List.mem_cons_of_mem _ hs))
    simp only [meteredAdvance, countProbesWork_spec, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The exact-use validator reserves a fixed control budget for the incoming
range test and outgoing comparisons. The cut scan starts only after exact
consumption of the private choices. -/
def meteredValidateSite (P : Program w C) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) : Option (List (Report w)) × ℕ :=
  if input.state.isSome → v * H ≤ input.cost ∧ input.cost < (v + 1) * H then
    let loop := meteredSiteLoop P 32 fuel H ((v + 1) * H) (S * H)
      (2 * H - 1) input (2 * H - 1) bits
    let base := 32 + loop.work
    match loop.output with
    | some (rs, []) =>
      let d := meteredAdvance input rs
      let accepted := match output with
        | some o => decide (o = d.1)
        | none => d.1.state.isNone
      (if accepted then some rs else none, base + d.2)
    | _ => (none, base)
  else (none, 32)

theorem meteredValidateSite_result (P : Program w C) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) :
    (meteredValidateSite P fuel S H v input output bits).1 =
      validateSite P fuel S H v input output bits := by
  unfold meteredValidateSite validateSite runSite
  split
  · dsimp only
    rw [meteredSiteLoop_output_eq]
    cases runSiteLoop P fuel H ((v + 1) * H) (S * H) (2 * H - 1) input (2 * H - 1) bits with
    | none => rfl
    | some z =>
      obtain ⟨rs, tail⟩ := z
      cases tail with
      | cons b bs => rfl
      | nil => cases output <;> simp [meteredAdvance_result]
  · rfl

/-- The work bound for the full private site validator, including incoming
format tests and the final cut scan, on arbitrary bit streams and cuts. -/
theorem meteredValidateSite_work_le (P : Program w C) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) (hH : 0 < H) :
    (meteredValidateSite P fuel S H v input output bits).2 ≤
      33 + 2 * H * (32 + 3 * fuel + w * H) + 2 * H * (7 + 4 * fuel) := by
  unfold meteredValidateSite
  split
  · dsimp only
    let loop := meteredSiteLoop P 32 fuel H ((v + 1) * H) (S * H)
      (2 * H - 1) input (2 * H - 1) bits
    have hloop : loop.work ≤ 2 * H * (32 + 3 * fuel + w * H) := by
      simpa only [show 2 * H - 1 + 1 = 2 * H by omega, loop] using
        siteWork_le P 32 fuel H ((v + 1) * H) (S * H) (2 * H - 1) input (2 * H - 1) bits
    cases hres : loop.output with
    | none => change 32 + loop.work ≤ _; omega
    | some z =>
      obtain ⟨rs, tail⟩ := z
      cases tail with
      | cons b bs => change 32 + loop.work ≤ _; omega
      | nil =>
        have hrun := (meteredSiteLoop_output_eq P 32 fuel H ((v + 1) * H) (S * H)
          (2 * H - 1) input (2 * H - 1) bits).symm.trans hres
        obtain ⟨hseg, _, _, _, _, hlen, _, _⟩ := runSiteLoop_iff.mp hrun
        have hscan := meteredAdvance_work_le input rs fuel (localSegment_event_bound hseg)
        have hsize := Nat.mul_le_mul_right (7 + 4 * fuel) (hlen.trans (Nat.sub_le _ _))
        change 32 + loop.work + (meteredAdvance input rs).2 ≤ _
        omega
  · dsimp only; omega

/-- A single product bounding the private validator. For the application's
fuel `n^u`, the hypothesis on the bucket follows from `H ≤ 2n` and `u ≥ 1`. -/
theorem meteredValidateSite_work_le_product (P : Program w C) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (bits : List Bool) (hH : 0 < H) (hf : H ≤ 2 * fuel) :
    (meteredValidateSite P fuel S H v input output bits).2 ≤
      64 * (H + 1) * (fuel + 1) * (w + 2) := by
  calc
    _ ≤ 33 + 2 * H * (32 + 3 * fuel + w * H) + 2 * H * (7 + 4 * fuel) :=
      meteredValidateSite_work_le P fuel S H v input output bits hH
    _ ≤ 33 + 2 * H * (32 + 3 * fuel + w * (2 * fuel)) + 2 * H * (7 + 4 * fuel) := by
      gcongr
    _ ≤ _ := by ring_nf; omega

end BurstRAM

end VPVNP
end Computability
end OAI
