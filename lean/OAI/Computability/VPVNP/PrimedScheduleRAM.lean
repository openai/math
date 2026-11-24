import OAI.Computability.VPVNP.RAMSuccessor

/-!
# Composing successive calls of the primed coefficient counter

Each item of the two input scans, the site parses, and the final comparisons
has a fixed absolute call number. The machine passes that number in its
persistent word. The only possible successful execution on prescribed header
memory therefore has exactly one list of choices per item, and carries the
actual external memory through all phases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedSchedule

open BurstRAM

variable {w : ℕ} {C : Type*}

/-- Encode the absolute call index as the persistent width-`w` word. -/
def cursor (w i : ℕ) : Word w := Fin.ofNat _ i

@[simp] theorem cursor_value {i : ℕ} (h : i < 2^w) : (cursor w i).val = i := Nat.mod_eq_of_lt h

/-- A running call at item `i`, and the unique accepted state at the end. -/
def control (w U i : ℕ) : Option (Word w) := if i < U then some (cursor w i) else none

/-- Semantics of a scheduled counter call. Given its absolute index, incoming memory and choice
stream, it returns a report on success. -/
abbrev Item (w : ℕ) := ℕ → Memory w → List Bool → Option (Report w)

/-- Independent per-item semantics, with reports recording the actual reads
and writes. A supplied choice list after the last item is rejected. -/
def runItems (item : Item w) (U : ℕ) : ℕ → Memory w → List (List Bool) → Option (List (Report w))
  | _, _, [] => some []
  | i, m, b :: bs =>
    if i < U then
      match item i m b with
      | none => none
      | some r => (runItems item U (i+1) (after m r.events) bs).map (r :: ·)
    else none

/-- What the opcode proof for each phase must establish. Invariants may depend
on the cursor and the memory, so this applies to the parse stack, leaf marks,
and cumulative histogram throughout the counter. -/
structure ScheduleSpec (P : Program w C) (fuel U : ℕ) (item : Item w) (inv : ℕ → Memory w → Prop) : Prop where
  call_eq : ∀ i < U, ∀ m, inv i m → ∀ b,
    execute P fuel (P.start (cursor w i)) m b = item i m b
  progress : ∀ i < U, ∀ m, inv i m → ∀ b r, item i m b = some r →
    r.result = control w U (i+1) ∧ inv (i+1) (after m r.events)

/-- The actual reset-private-memory run computes the same reports as the
composition of the item semantics. -/
theorem native_eq_runItems {P : Program w C} {fuel U : ℕ} {item : Item w} {inv}
    (hs : ScheduleSpec P fuel U item inv) (i : ℕ) (m : Memory w) (hi : inv i m)
    (bs : List (List Bool)) :
    runSegment P fuel (control w U i) m bs = runItems item U i m bs := by
  induction bs generalizing i m with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : i < U
    · simp only [control, h, ↓reduceIte, runSegment, runItems, hs.call_eq i h m hi]
      cases he : item i m b with
      | none => rfl
      | some r =>
        obtain ⟨hr, hm⟩ := hs.progress i h m hi _ _ he
        dsimp only
        rw [hr, ih (i+1) _ hm]
    · simp [control, runSegment, runItems, h]

/-- At a successful partial run the next cursor and the number of consumed
choice lists agree, so splitting a sequence into individual items is unique. -/
theorem runItems_progress {P : Program w C} {fuel U : ℕ} {item : Item w} {inv}
    (hs : ScheduleSpec P fuel U item inv) (i : ℕ) (m : Memory w) (hi : inv i m) (hbound : i ≤ U)
    {bs : List (List Bool)} {rs : List (Report w)} (hr : runItems item U i m bs = some rs) :
    rs.length = bs.length ∧ i + bs.length ≤ U ∧
      endState (control w U i) rs = control w U (i+bs.length) := by
  induction bs generalizing i m rs with
  | nil => simp [runItems] at hr; subst rs; simp [endState, hbound]
  | cons b bs ih =>
    by_cases h : i < U
    · simp only [runItems, h, ↓reduceIte] at hr
      cases he : item i m b with
      | none => simp [he] at hr
      | some r =>
        simp only [he, Option.map_eq_some_iff] at hr
        obtain ⟨rs, ht, rfl⟩ := hr
        obtain ⟨hresult, hmem⟩ := hs.progress i h m hi _ _ he
        obtain ⟨hlen, hcap, hstate⟩ := ih (i+1) _ hmem h ht
        simp only [List.length_cons, endState, hresult, hlen]
        rw [hstate]
        exact ⟨trivial, by omega, by congr 1; omega⟩
    · simp [runItems, h] at hr

/-- Reports of adjacent phases compose with exact transfer of persistent
state, external memory, and branch lists. -/
theorem runSegment_append (P : Program w C) (fuel : ℕ) (s : Option (Word w)) (m : Memory w)
    (bs cs : List (List Bool)) :
    runSegment P fuel s m (bs++cs) =
      (runSegment P fuel s m bs).bind fun rs =>
        (runSegment P fuel (endState s rs) (after m (eventLog rs)) cs).map (rs++·) := by
  induction bs generalizing s m with
  | nil => simp [runSegment, endState, after, eventLog]
  | cons b bs ih =>
    cases s with
    | none => rfl
    | some s =>
      simp only [List.cons_append, runSegment]
      cases hx : execute P fuel (P.start s) m b with
      | none => rfl
      | some r =>
        dsimp only
        rw [ih]
        cases hy : runSegment P fuel r.result (after m r.events) bs with
        | none => rfl
        | some rs =>
          simp only [Option.bind_some, Option.map_some, eventLog, List.flatMap_cons, endState,
            after, List.foldl_append, List.cons_append]
          cases runSegment P fuel (endState r.result rs)
              ((List.flatMap Report.events rs).foldl update (r.events.foldl update m)) cs <;> rfl

/-- One exact branch list per scheduled item, including a possibly empty
list for deterministic input scans or final comparisons. -/
abbrev Choices (item : Item w) (U : ℕ) (m : Memory w) (cap : List (Report w) → Prop) :=
  {b : Fin U → List Bool // ∃ rs, runItems item U 0 m (List.ofFn b) = some rs ∧ cap rs}

private theorem initial_control {U : ℕ} (hU : 0 < U) : control w U 0 = some (cursor w 0) := by
  simp [control, hU]

private theorem actual_length {P : Program w C} {fuel U : ℕ} {item : Item w} {inv}
    (hs : ScheduleSpec P fuel U item inv) (hU : 0 < U) (m : Memory w) (hi : inv 0 m)
    (cap : List (Report w) → Prop) (b : ActualPaths P fuel (cursor w 0) m cap) : b.val.length = U := by
  obtain ⟨rs, hr, hhalt, _⟩ := b.property
  have he := native_eq_runItems hs 0 m hi b.val
  rw [initial_control hU] at he
  have hr := he.symm.trans hr
  obtain ⟨_, hle, hstate⟩ := runItems_progress hs _ _ hi (Nat.zero_le _) hr
  rw [initial_control hU, hhalt, Nat.zero_add] at hstate
  have hge : U ≤ b.val.length := by
    by_contra! h
    simp [control, h] at hstate
  omega

/-- Native accepting paths of the assembled machine and the fixed-index
per-item choices count the same executions. -/
def nativeScheduleEquiv {P : Program w C} {fuel U : ℕ} {item : Item w} {inv}
    (hs : ScheduleSpec P fuel U item inv) (hU : 0 < U) (m : Memory w) (hi : inv 0 m)
    (cap : List (Report w) → Prop) : ActualPaths P fuel (cursor w 0) m cap ≃ Choices item U m cap where
  toFun b := ⟨fun i => b.val[i.val]'(by rw [actual_length hs hU m hi cap b]; exact i.isLt), by
    have hbs : List.ofFn (fun i : Fin U => b.val[i.val]'(by rw [actual_length hs hU m hi cap b]; exact i.isLt))
        = b.val := List.ext_getElem (by rw [List.length_ofFn, actual_length hs hU m hi cap b])
          (by intros; simp)
    obtain ⟨rs, hr, _, hc⟩ := b.property
    rw [hbs, ← native_eq_runItems hs _ _ hi, initial_control hU]
    exact ⟨rs, hr, hc⟩⟩
  invFun b := ⟨List.ofFn b.val, by
    obtain ⟨rs, hr, hc⟩ := b.property
    obtain ⟨_, _, hs'⟩ := runItems_progress hs _ _ hi (Nat.zero_le _) hr
    simp only [Nat.zero_add, List.length_ofFn, control, hU, ↓reduceIte, Nat.lt_irrefl] at hs'
    have he := native_eq_runItems hs 0 m hi (List.ofFn b.val)
    rw [initial_control hU] at he
    exact ⟨rs, he.trans hr, hs', hc⟩⟩
  left_inv b := by
    apply Subtype.ext
    exact List.ext_getElem (by rw [List.length_ofFn, actual_length hs hU m hi cap b]) (by intros; simp)
  right_inv b := by apply Subtype.ext; funext i; simp

end PrimedSchedule

end VPVNP
end Computability
end OAI
