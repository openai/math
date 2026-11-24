import OAI.Computability.VPVNP.LiveProgramRouting
import OAI.Computability.VPVNP.LiveHeaderUnique
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# Removing a completed deterministic segment from a native group path

A canonical verified run can be a proper initial part of the group, ending
with a returned word. Exact-use choice strings force every accepting group
path to have precisely those initial bursts, including their full reports.
The remainder retains the original cap applied to the concatenated reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open BurstRAM

variable {w : ℕ} {C : Type*} {P : BurstRAM.Program w C} {fuel : ℕ}

/-- All accepting paths from a given optional call state. -/
abbrev PathsFrom (P : BurstRAM.Program w C) (fuel : ℕ) (st : Option (Word w)) (m : Memory w)
    (cap : List (Report w) → Prop) :=
  {bs : List (List Bool) // ∃ logs, runSegment P fuel st m bs = some logs ∧
    endState st logs = none ∧ cap logs}

/-- Every native accepting run beginning at the given state contains the
entire verified deterministic prefix in both its choice stream and its log. -/
theorem split_empty_segment {n : ℕ} {st : Option (Word w)} {m : Memory w} {prefixLogs logs : List (Report w)}
    {bs : List (List Bool)} (prefixRun : runSegment P fuel st m (List.replicate n []) = some prefixLogs)
    (run : runSegment P fuel st m bs = some logs) (halt : endState st logs = none) :
    ∃ rest tailLogs, bs = List.replicate n [] ++ rest ∧ logs = prefixLogs ++ tailLogs ∧
      runSegment P fuel (endState st prefixLogs) (after m (eventLog prefixLogs)) rest = some tailLogs := by
  induction n generalizing st m bs prefixLogs logs with
  | zero =>
    simp [runSegment] at prefixRun; subst prefixLogs
    exact ⟨bs,logs,rfl,rfl,run⟩
  | succ n ih =>
    simp only [List.replicate_succ] at prefixRun ⊢
    cases st with
    | none => contradiction
    | some st =>
      cases bs with
      | nil => simp [runSegment] at run; subst logs; contradiction
      | cons b bs =>
        rw [runSegment] at prefixRun run
        cases hp : BurstRAM.execute P fuel (P.start st) m [] with
        | none => simp [hp] at prefixRun
        | some r =>
          cases hb : BurstRAM.execute P fuel (P.start st) m b with
          | none => simp [hb] at run
          | some s =>
            obtain ⟨rfl,rfl⟩ := execute_empty_forces hp hb
            simp only [hp,Option.map_eq_some_iff] at prefixRun run
            obtain ⟨pr,hpr,rfl⟩ := prefixRun
            obtain ⟨rs,hrs,rfl⟩ := run
            obtain ⟨rest,tail,hb',hrs',hr⟩ := ih hpr hrs halt
            refine ⟨rest,tail,by simp [hb'],by simp [hrs'],?_⟩
            simpa only [endState,eventLog,List.flatMap_cons,after,List.foldl_append] using hr

/-- The equivalence is concatenation on branch strings, so even different
branch choices in the suffix with the same output state remain distinct. -/
noncomputable def emptySegmentEquiv {n : ℕ} {st : Option (Word w)} {m : Memory w} {prefixLogs : List (Report w)}
    (prefixRun : runSegment P fuel st m (List.replicate n []) = some prefixLogs) (cap : List (Report w) → Prop) :
    PathsFrom P fuel (endState st prefixLogs) (after m (eventLog prefixLogs)) (fun rs => cap (prefixLogs++rs)) ≃
      PathsFrom P fuel st m cap := by
  let add : PathsFrom P fuel (endState st prefixLogs) (after m (eventLog prefixLogs)) (fun rs => cap (prefixLogs++rs)) →
      PathsFrom P fuel st m cap := fun a => ⟨List.replicate n [] ++ a.val,by
    obtain ⟨tail,hr,hh,hc⟩ := a.property
    refine ⟨prefixLogs++tail,?_,?_,hc⟩
    · rw [PrimedSchedule.runSegment_append,prefixRun]; simp [hr]
    · simpa only [endState_append] using hh⟩
  apply Equiv.ofBijective add
  constructor
  · intro a b eq
    exact Subtype.ext (List.append_cancel_left (congrArg Subtype.val eq))
  · rintro ⟨bs,logs,hr,hh,hc⟩
    obtain ⟨rest,tail,rfl,rfl,ht⟩ := split_empty_segment prefixRun hr hh
    refine ⟨⟨rest,tail,ht,?_,hc⟩,rfl⟩
    rwa [endState_append] at hh

end LiveProgram

end VPVNP
end Computability
end OAI
