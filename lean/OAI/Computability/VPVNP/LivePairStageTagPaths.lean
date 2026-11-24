import OAI.Computability.VPVNP.LivePairStageTag

/-!
# Full path semantics of the pair tag-address calculation

Computing the stage address on each fresh call uses only private ticks.
Removing these ticks is an equivalence of the capped native branch streams,
with exactly the same memory, continuing word and branch choices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairTag
open BurstRAM BurstRAM.PrivateRAM

variable {p r w : ℕ} (T : Template p r 12) (pub : Fin 11 → Word w)

/-- Prepend the five private ticks spent computing the pair tag address to a source call
report. -/
def prefixReport (rep : Report w) : Report w := LiveStageLink.prependLog (List.replicate 5 .tick) rep

theorem prefix_effect (rep : Report w) (m : Memory w) :
    after m (prefixReport rep).events = after m rep.events ∧ (prefixReport rep).result = rep.result ∧
    choiceBits (prefixReport rep).events = choiceBits rep.events ∧ (prefixReport rep).probes = rep.probes ∧
    (prefixReport rep).events.length = 5+rep.events.length := by
  exact ⟨rfl,rfl,rfl,rfl,by simp [prefixReport,LiveStageLink.prependLog]; omega⟩

@[simp] theorem prefix_after (rep : Report w) (m : Memory w) :
    after m (prefixReport rep).events = after m rep.events := (prefix_effect rep m).1

@[simp] theorem prefix_result (rep : Report w) : (prefixReport rep).result = rep.result := rfl

theorem segment (f : ℕ) (st : Option (Word w)) (m : Memory w) (bits : List (List Bool)) :
    runSegment ((compile T).instantiate w pub).program (f+5) st m bits =
      (runSegment (T.instantiate w (data pub)).program f st m bits).map (List.map prefixReport) := by
  induction bits generalizing st m with
  | nil => rfl
  | cons b bs ih =>
    cases st with
    | none => rfl
    | some st =>
      rw [runSegment,runSegment,execute_start]
      cases h : execute (T.instantiate w (data pub)).program f ((T.instantiate w (data pub)).program.start st) m b with
      | none => rfl
      | some rep =>
        change (runSegment _ _ (prefixReport rep).result (after m (prefixReport rep).events) bs).map (prefixReport rep :: ·) = _
        rw [prefix_result,prefix_after,ih]
        let run := runSegment (T.instantiate w (data pub)).program f rep.result (after m rep.events) bs
        change (run.map (List.map prefixReport)).map (prefixReport rep :: ·) = (run.map (rep :: ·)).map (List.map prefixReport)
        cases run <;> rfl

@[simp] theorem end_prefix (st : Option (Word w)) (rs : List (Report w)) :
    endState st (rs.map prefixReport) = endState st rs := by
  induction rs generalizing st with
  | nil => rfl
  | cons r rs ih => exact ih r.result

@[simp] theorem after_prefix (m : Memory w) (rs : List (Report w)) :
    after m (eventLog (rs.map prefixReport)) = after m (eventLog rs) := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons,eventLog,List.flatMap_cons,after,List.foldl_append]
    exact ih (after m r.events)

/-- The branch strings are identical on both sides, and the predicate sees
the actually executed sequence of reports. -/
def pathEquiv (f : ℕ) (st : Word w) (m : Memory w) (cap : List (Report w) → Prop) :
    ActualPaths (T.instantiate w (data pub)).program f st m (fun rs => cap (rs.map prefixReport)) ≃
      ActualPaths ((compile T).instantiate w pub).program (f+5) st m cap :=
  Equiv.subtypeEquivRight fun bits => by
    constructor
    · rintro ⟨rs,hr,hh,hc⟩
      exact ⟨rs.map prefixReport,by rw [segment,hr]; rfl,(end_prefix _ _).trans hh,hc⟩
    · rintro ⟨es,hr,hh,hc⟩
      rw [segment,Option.map_eq_some_iff] at hr
      obtain ⟨rs,hr,rfl⟩ := hr
      exact ⟨rs,hr,(end_prefix _ _).symm.trans hh,hc⟩

end LiveProgram.PairTag

end VPVNP
end Computability
end OAI
