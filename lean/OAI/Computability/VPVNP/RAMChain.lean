import OAI.Computability.VPVNP.RAMExecution

/-!
# Successive calls with reset private memory and persistent external memory

A path is specified by its list of actual binary choices in each call. The
native run computes reads and addresses itself. A local replay uses the
reported values. Read consistency over the concatenated event log identifies
the two descriptions of a path, including when branches yield identical states.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

theorem correct_append (m : Memory w) (es fs : List (Event w)) :
    Correct m (es ++ fs) ↔ Correct m es ∧ Correct (after m es) fs := by
  induction es generalizing m with
  | nil => simp [Correct, after]
  | cons e es ih => cases e <;> simp [Correct, after, update, ih, and_assoc]

/-- Native execution of consecutive calls. Each entry supplies just the branch
choices of that call. After a halt a further call rejects. -/
def runSegment (P : Program w C) (fuel : ℕ) :
    Option (Word w) → Memory w → List (List Bool) → Option (List (Report w))
  | _, _, [] => some []
  | none, _, _ :: _ => none
  | some state, m, bs :: more =>
    match execute P fuel (P.start state) m bs with
    | none => none
    | some r => (runSegment P fuel r.result (after m r.events) more).map (r :: ·)

/-- The local processor validates the sequence of calls using their reported
read answers, propagating the returned persistent word. -/
def LocalSegment (P : Program w C) (fuel : ℕ) : Option (Word w) → List (Report w) → Prop
  | _, [] => True
  | none, _ :: _ => False
  | some state, r :: rest =>
    Guessed P fuel (P.start state) r.events r.result ∧ LocalSegment P fuel r.result rest

/-- The persistent state after a sequence of reports, given by the last report's result or the
incoming state for an empty sequence. -/
def endState : Option (Word w) → List (Report w) → Option (Word w)
  | s, [] => s
  | _, r :: rest => endState r.result rest

/-- Extract one list of actual binary branch choices from each call report, in call order. -/
def branchPaths (rs : List (Report w)) : List (List Bool) := rs.map (fun r => choiceBits r.events)

/-- Concatenate all calls' events in execution order for replay against external memory. -/
def eventLog (rs : List (Report w)) : List (Event w) := rs.flatMap Report.events

theorem endState_append (s : Option (Word w)) (rs ts : List (Report w)) :
    endState s (rs ++ ts) = endState (endState s rs) ts := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simpa [endState] using ih r.result

theorem localSegment_append (P : Program w C) (fuel : ℕ) (s : Option (Word w))
    (rs ts : List (Report w)) :
    LocalSegment P fuel s (rs ++ ts) ↔
      LocalSegment P fuel s rs ∧ LocalSegment P fuel (endState s rs) ts := by
  induction rs generalizing s with
  | nil => simp [LocalSegment, endState]
  | cons r rs ih => cases s <;> simp [LocalSegment, endState, ih, and_assoc]

theorem runSegment_iff (P : Program w C) (fuel : ℕ) (s : Option (Word w)) (m : Memory w)
    (bits : List (List Bool)) (rs : List (Report w)) :
    runSegment P fuel s m bits = some rs ↔
      LocalSegment P fuel s rs ∧ Correct m (eventLog rs) ∧ branchPaths rs = bits := by
  induction bits generalizing rs s m with
  | nil => cases rs <;> simp [runSegment, LocalSegment, eventLog, Correct, branchPaths]
  | cons bs bits ih =>
    cases s with
    | none =>
      cases rs <;> simp [runSegment, LocalSegment, branchPaths]
    | some s =>
      cases h : execute P fuel (P.start s) m bs with
      | none =>
        cases rs with
        | nil => simp [runSegment, h, branchPaths]
        | cons r rs =>
          simp only [runSegment, h, reduceCtorEq, LocalSegment,
            eventLog, List.flatMap_cons, correct_append, branchPaths, List.map_cons,
            List.cons.injEq, false_iff]
          rintro ⟨⟨hg, _⟩, ⟨hm, _⟩, hb, _⟩
          have hr := (execute_iff (r := r) (P := P) (c := P.start s)).mpr ⟨hg, hm, hb⟩
          rw [h] at hr
          contradiction
      | some t =>
        have ht := execute_spec h
        cases rs with
        | nil =>
          simp [runSegment, h, branchPaths, Option.map_eq_some_iff]
        | cons r rs =>
          simp only [runSegment, h, Option.map_eq_some_iff,
            List.cons.injEq, LocalSegment, eventLog,
            List.flatMap_cons, correct_append, branchPaths, List.map_cons]
          constructor
          · rintro ⟨l, hl, rfl, rfl⟩
            obtain ⟨hL, hM, hB⟩ := (ih _ _ _).mp hl
            exact ⟨⟨ht.1, hL⟩, ⟨ht.2.1, hM⟩, ht.2.2, hB⟩
          · rintro ⟨⟨hg, hL⟩, ⟨hm, hM⟩, hb, hB⟩
            have hr := (execute_iff (r := r) (P := P) (c := P.start s)).mpr ⟨hg, hm, hb⟩
            have he : t = r := Option.some.inj (h.symm.trans hr)
            subst r
            exact ⟨rs, (ih _ _ _).mpr ⟨hL, hM, hB⟩, rfl, rfl⟩

/-- Accepted native paths subject to a predicate on their computed reports.
This predicate will impose the exact global and per-call cost caps. -/
abbrev ActualPaths (P : Program w C) (fuel : ℕ) (initial : Word w) (m : Memory w)
    (withinCaps : List (Report w) → Prop) :=
  {bits : List (List Bool) // ∃ rs, runSegment P fuel (some initial) m bits = some rs ∧
    endState (some initial) rs = none ∧ withinCaps rs}

/-- Accepted local call reports, with correct reads over the whole memory
history. The sorted-record check is a local implementation of this last test. -/
abbrev VerifiedReports (P : Program w C) (fuel : ℕ) (initial : Word w) (m : Memory w)
    (withinCaps : List (Report w) → Prop) :=
  {rs : List (Report w) // LocalSegment P fuel (some initial) rs ∧
    Correct m (eventLog rs) ∧ endState (some initial) rs = none ∧ withinCaps rs}

private noncomputable def getReports {P : Program w C} {fuel initial m cap}
    (b : ActualPaths P fuel initial m cap) : VerifiedReports P fuel initial m cap :=
  ⟨b.property.choose, by
    obtain ⟨h, ha, hc⟩ := b.property.choose_spec
    obtain ⟨hl, hm, _⟩ := (runSegment_iff ..).mp h
    exact ⟨hl, hm, ha, hc⟩⟩

private def getChoices {P : Program w C} {fuel initial m cap}
    (r : VerifiedReports P fuel initial m cap) : ActualPaths P fuel initial m cap :=
  ⟨branchPaths r.val, r.val, (runSegment_iff ..).mpr ⟨r.property.1, r.property.2.1, rfl⟩,
    r.property.2.2⟩

/-- Parsimony before partitioning calls into sites. -/
noncomputable def reportEquiv (P : Program w C) (fuel : ℕ) (initial : Word w) (m : Memory w)
    (withinCaps : List (Report w) → Prop) :
    ActualPaths P fuel initial m withinCaps ≃ VerifiedReports P fuel initial m withinCaps where
  toFun := getReports
  invFun := getChoices
  left_inv b := Subtype.ext ((runSegment_iff ..).mp b.property.choose_spec.1).2.2
  right_inv r := by
    apply Subtype.ext
    have h := (runSegment_iff P fuel (some initial) m (branchPaths r.val) r.val).mpr
      ⟨r.property.1, r.property.2.1, rfl⟩
    exact Option.some.inj ((getChoices r).property.choose_spec.1.symm.trans h)

end BurstRAM

end VPVNP
end Computability
end OAI
