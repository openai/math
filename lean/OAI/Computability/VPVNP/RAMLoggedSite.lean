import OAI.Computability.VPVNP.RAMLoggedCall
import OAI.Computability.VPVNP.RAMSiteWork

/-!
# Single-pass site loop with concrete private word work

A site starts every charged call with a fresh write log, records the call's
work in the same recursion that obtains its report, and uses its probe count
to advance the cut. The final loop check costs sixteen operations even when
no call can start.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open VPVNP.BurstRAM

variable {w p r k : ℕ}

/-- Charge startup against each remaining allowance before dispatching.
Every attempted call returns both the metered run and its word work. -/
def Machine.loggedChargedCall (M : Machine w p r k) (fuel : ℕ) (s : Word w)
    (callLeft globalLeft siteLeft : ℕ) (bits : List Bool) : LocalCallRun w × ℕ :=
  match min callLeft (min globalLeft siteLeft) with
  | 0 => (⟨none, 0, 0, 0⟩, 0)
  | a + 1 => M.meteredLoggedCall fuel (M.logProgram.start s) a bits

theorem Machine.loggedChargedCall_result (M : Machine w p r k) (fuel : ℕ) (s : Word w)
    (callLeft globalLeft siteLeft : ℕ) (bits : List Bool) :
    (M.loggedChargedCall fuel s callLeft globalLeft siteLeft bits).1 =
      runChargedCall M.program fuel (M.program.start s) callLeft globalLeft siteLeft bits := by
  cases h : min callLeft (min globalLeft siteLeft) with
  | zero => simp [Machine.loggedChargedCall, runChargedCall, h]
  | succ a => simp [Machine.loggedChargedCall, runChargedCall, h,
      Machine.meteredLoggedCall_result, Machine.logProgram_start]

/-- A single run returns the reports, unused suffix and total primitive work.
The sixteen control operations cover the cut tests, budget arithmetic and
collection of the returned reports. -/
def Machine.runLoggedSite (M : Machine w p r k) (fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) : MeteredSiteRun w :=
  if c.cost ≤ globalCap then
    match c.state with
    | none => ⟨some ([], bits), 16⟩
    | some s =>
      if c.cost < boundary then
        match steps with
        | 0 => ⟨none, 16⟩
        | n + 1 =>
          let t := M.loggedChargedCall fuel s H (globalCap - c.cost) siteLeft bits
          let work := 16 + t.2
          match t.1.output with
          | none => ⟨none, work⟩
          | some (report, tail) =>
            let charge := 1 + t.1.probes
            let rest := M.runLoggedSite fuel H boundary globalCap n
              ⟨c.cost + charge, report.result⟩ (siteLeft - charge) tail
            ⟨rest.output.map (fun (rs, bs) => (report :: rs, bs)), work + rest.work⟩
      else ⟨some ([], bits), 16⟩
  else ⟨none, 16⟩
termination_by structural steps

/-- The logged interpreter follows exactly the reports and binary choices
used in the validator's path-counting theorem. -/
theorem Machine.runLoggedSite_output (M : Machine w p r k) (fuel H boundary globalCap steps : ℕ)
    (c : Cut w) (siteLeft : ℕ) (bits : List Bool) :
    (M.runLoggedSite fuel H boundary globalCap steps c siteLeft bits).output =
      runSiteLoop M.program fuel H boundary globalCap steps c siteLeft bits := by
  rw [← meteredSiteLoop_output_eq M.program 16]
  induction steps generalizing c siteLeft bits with
  | zero =>
    rw [Machine.runLoggedSite, meteredSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases c.state <;> simp [hc]
    · simp [hc]
  | succ n ih =>
    rw [Machine.runLoggedSite, meteredSiteLoop]
    by_cases hc : c.cost ≤ globalCap
    · cases hs : c.state with
      | none => simp [hc]
      | some s =>
        by_cases hb : c.cost < boundary
        · simp only [hc, hb, ↓reduceIte, Machine.loggedChargedCall_result]
          cases (runChargedCall M.program fuel (M.program.start s) H
            (globalCap - c.cost) siteLeft bits).output with
          | none => rfl
          | some z => obtain ⟨report, tail⟩ := z; simp only [ih]
        · simp [hc, hb]
    · simp [hc]

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
