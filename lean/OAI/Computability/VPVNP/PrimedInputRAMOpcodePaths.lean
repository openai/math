import OAI.Computability.VPVNP.PrimedInputRAMRunEquiv

/-!
# Native path correspondence for the physical primed input passes

Each data call reads three supplied cut lengths before performing its scheduled item.
The physical machine may take extra private steps. Across the entire input stage its
branch choices, returned cursors and final memory agree with the schedule.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM

variable {w M : ℕ} {C : Type*}

/-- A successful call consumes its entire choice stream. Appending an unused
nonempty suffix to that same stream therefore rejects. -/
theorem execute_extra_choices {P : Program w C} {fuel : ℕ} {c : C} {m : Memory w}
    {bs : List Bool} {r : Report w} (hr : execute P fuel c m bs = some r)
    (extra : List Bool) (hne : extra ≠ []) : execute P fuel c m (bs ++ extra) = none := by
  induction fuel generalizing c m bs r with
  | zero => simp [execute] at hr
  | succ fuel ih =>
    cases hc : P.step c with
    | reject => simp [execute, hc] at hr
    | finish v =>
      cases bs with
      | nil => simp [execute, hc, hne]
      | cons => simp [execute, hc] at hr
    | branch next =>
      cases bs with
      | nil => simp [execute, hc] at hr
      | cons b tail =>
        obtain ⟨_, he, _⟩ := Option.map_eq_some_iff.mp (by simpa only [execute, hc] using hr)
        simp only [List.cons_append, execute, hc, ih he, Option.map_none]
    | localStep next | read _ next | write _ _ next =>
      obtain ⟨_, he, _⟩ := Option.map_eq_some_iff.mp (by simpa only [execute, hc] using hr)
      simp only [execute, hc, ih he, Option.map_none]

theorem only_item_choices {P : Program w C} {fuel : ℕ} {c : C} {m : Memory w}
    (op : Item w) (report : Bool → Report w)
    (ok : ∀ b, execute P fuel c m (op.bits b) = some (report b))
    {bs : List Bool} {r : Report w} (hr : execute P fuel c m bs = some r) :
    ∃ b, bs = op.bits b := by
  cases h : op.owns with
  | false =>
    have he : execute P fuel c m [] = some (report false) := by simpa [Item.bits,h] using ok false
    by_cases hn : bs = []
    · exact ⟨false, by simp [Item.bits,h,hn]⟩
    · have := execute_extra_choices he bs hn
      simp [hr] at this
  | true =>
    have he (b : Bool) : execute P fuel c m [b] = some (report b) := by simpa [Item.bits,h] using ok b
    cases bs with
    | nil =>
      have := execute_extra_choices hr [false] (by simp)
      simp [he] at this
    | cons b bs =>
      by_cases hn : bs = []
      · exact ⟨b, by simp [Item.bits,h,hn]⟩
      · have ha := execute_extra_choices (he b) bs hn
        simp [hr] at ha

private theorem invalid_choices {P : Program w C} {fuel : ℕ} {c : C} {m : Memory w}
    (op : Item w) (report : Bool → Report w)
    (ok : ∀ b, execute P fuel c m (op.bits b) = some (report b))
    {bs : List Bool} (bad : ¬ ∃ b, bs = op.bits b) : execute P fuel c m bs = none := by
  cases hx : execute P fuel c m bs with
  | none => rfl
  | some r => exact False.elim (bad (only_item_choices _ report ok hx))

/-- Local contract of the physical input-stage machine. Only prescribed input
streams need to be checked; exact use of bits rules out any other path. -/
structure PhysicalSchedule (P : Program w C) (fuel : ℕ) (ops : Fin M → Item w)
    (bitWord : Bool → Word w) (fit : M < 2^w) (Pre : Memory w → Prop) where
  /-- Native report for one scheduled data call at the given incoming memory and choice bit. -/
  report : Fin M → Memory w → Bool → Report w
  /-- Native report for the halt call at the cursor just beyond the final data item. -/
  last : Memory w → Report w
  data : ∀ i m b, Pre m → execute P fuel (P.start (cursor fit i.val i.isLt.le)) m ((ops i).bits b) =
    some (report i m b)
  result : ∀ i m b, Pre m → (report i m b).result = some (successor fit i)
  memory : ∀ i m b, Pre m → after m (report i m b).events = (ops i).memory bitWord m b
  probes : ∀ i m b, Pre m → (report i m b).probes = (ops i).probeCount + 3
  closed : ∀ i m b, Pre m → Pre ((ops i).memory bitWord m b)
  halt : ∀ m, Pre m → execute P fuel (P.start (cursor fit M le_rfl)) m [] = some (last m)
  halt_result : ∀ m, Pre m → (last m).result = none
  halt_memory : ∀ m, Pre m → after m (last m).events = m
  halt_probes : ∀ m, Pre m → (last m).probes = 0

/-- Agreement of two native histories, including their extra cut-length probes.
A returning data call incurs three extra probes; the terminal call incurs none. -/
inductive MatchedReports : Memory w → List (Report w) → List (Report w) → Prop
  | nil (m) : MatchedReports m [] []
  | cons {m a b xs ys}
      (result : a.result = b.result) (memory : after m a.events = after m b.events)
      (probes : a.probes = b.probes + (if b.result.isSome then 3 else 0))
      (tail : MatchedReports (after m b.events) xs ys) : MatchedReports m (a :: xs) (b :: ys)

namespace MatchedReports

theorem endState_eq {m : Memory w} {xs ys : List (Report w)} (h : MatchedReports m xs ys)
    (s : Option (Word w)) : endState s xs = endState s ys := by
  induction h generalizing s with
  | nil => rfl
  | cons he _ _ _ ih => simp only [endState, he, ih]

theorem after_eq {m : Memory w} {xs ys : List (Report w)} (h : MatchedReports m xs ys) :
    after m (eventLog xs) = after m (eventLog ys) := by
  induction h with
  | nil => rfl
  | cons _ hm _ _ ih =>
    simp only [eventLog, List.flatMap_cons, after, List.foldl_append] at hm ih ⊢
    rw [hm, ih]

theorem cost_eq {m : Memory w} {xs ys : List (Report w)} (h : MatchedReports m xs ys) :
    RAMBuckets.cost Report.probes xs = RAMBuckets.cost Report.probes ys +
      3 * (ys.filter fun r ↦ r.result.isSome).length := by
  induction h with
  | nil => rfl
  | @cons m a b xs ys _ _ hp _ ih =>
    cases he : b.result <;> simp [he, RAMBuckets.cost] at hp ⊢ <;> omega

theorem per_call {m : Memory w} {xs ys : List (Report w)} (h : MatchedReports m xs ys)
    (hy : ∀ b ∈ ys, 1 + b.probes ≤ 3) : ∀ a ∈ xs, 1 + a.probes ≤ 6 := by
  induction h with
  | nil => simp
  | @cons m a b xs ys _ _ hp _ ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · have h₀ := hy b (List.mem_cons_self ..)
      split at hp <;> omega
    · exact ih (fun t ht ↦ hy t (List.mem_cons_of_mem _ ht)) z hz

private theorem prepend {m : Memory w} {a b : Report w} {xs ys : Option (List (Report w))}
    (hr : a.result = b.result) (hm : after m a.events = after m b.events)
    (hp : a.probes = b.probes + (if b.result.isSome then 3 else 0))
    (h : Option.Rel (MatchedReports (after m b.events)) xs ys) :
    Option.Rel (MatchedReports m) (xs.map (a :: ·)) (ys.map (b :: ·)) := by
  cases h with
  | none => exact .none
  | some ht => exact .some (.cons hr hm hp ht)

end MatchedReports

namespace PhysicalSchedule

variable {P : Program w C} {fuel : ℕ} {ops : Fin M → Item w} {bitWord : Bool → Word w}
  {fit : M < 2^w} {Pre : Memory w → Prop}
variable (R : PhysicalSchedule P fuel ops bitWord fit Pre)

include R

/-- Run the physical and scheduled interpreters on the same sequence of streams.
They reject together, or return matching histories, from any valid cursor. -/
theorem run_matched (k : ℕ) (hk : k ≤ M) (m : Memory w) (hm : Pre m) (bs : List (List Bool)) :
    Option.Rel (MatchedReports m)
      (runSegment P fuel (some (cursor fit k hk)) m bs)
      (runSegment (scheduledProgram ops bitWord fit) 3 (some (cursor fit k hk)) m bs) := by
  induction bs generalizing k m with
  | nil => exact .some (.nil m)
  | cons bits more ih =>
    by_cases hi : k < M
    · let i : Fin M := ⟨k,hi⟩
      have hd (b : Bool) : execute P fuel (P.start (cursor fit k hk)) m ((ops i).bits b) =
          some (R.report i m b) := R.data i m b hm
      have hg (b : Bool) :
          execute (scheduledProgram ops bitWord fit) 3
            ((scheduledProgram ops bitWord fit).start (cursor fit k hk)) m ((ops i).bits b) =
          some ((ops i).report bitWord (successor fit i) m b) := by
        rw [show cursor fit k hk = cursor fit i.val i.isLt.le by rfl, start_item, execute_item]
      by_cases good : ∃ b, bits = (ops i).bits b
      · obtain ⟨b,rfl⟩ := good
        have step := R.memory i m b hm
        have next := R.result i m b hm
        have count := R.probes i m b hm
        simp only [runSegment, hd, hg, next, step, Item.report_result, Item.after_report]
        apply MatchedReports.prepend (next.trans (Item.report_result ..).symm)
          (step.trans (Item.after_report ..).symm) (by simp [count])
        rw [Item.after_report, show successor fit i = cursor fit (k+1) hi by rfl]
        exact ih (k+1) hi _ (R.closed i m b hm)
      · simp only [runSegment, invalid_choices _ _ hd good, invalid_choices _ _ hg good,
          Option.rel_none_none]
    · have he : k = M := by omega
      subst k
      have hp := R.halt m hm
      have gen : execute (scheduledProgram ops bitWord fit) 3
          ((scheduledProgram ops bitWord fit).start (cursor fit M le_rfl)) m [] = some (haltReport w) := by
        rw [start_halt]
        rfl
      cases bits with
      | nil =>
        cases more with
        | nil =>
          simp only [runSegment, hp, gen, Option.map_some, Option.rel_some_some]
          exact .cons (R.halt_result m hm) (R.halt_memory m hm) (R.halt_probes m hm) (.nil _)
        | cons =>
          simp only [runSegment, hp, gen, R.halt_result m hm, haltReport, Option.map_none,
            Option.rel_none_none]
      | cons b tail =>
        have hp' := execute_extra_choices hp (b::tail) (by simp)
        have hg' := execute_extra_choices gen (b::tail) (by simp)
        simp only [List.nil_append] at hp' hg'
        simp only [runSegment, hp', hg', Option.rel_none_none]

/-- Physical acceptance and schedule acceptance coincide before imposing budgets. -/
theorem accepts_iff (m : Memory w) (hm : Pre m) (bits : List (List Bool)) :
    (∃ rs, runSegment P fuel (some 0) m bits = some rs ∧ endState (some 0) rs = none) ↔
    ∃ rs, runSegment (scheduledProgram ops bitWord fit) 3 (some 0) m bits = some rs ∧
      endState (some 0) rs = none := by
  have hs := R.run_matched 0 (Nat.zero_le _) m hm bits
  change Option.Rel _ (runSegment P fuel (some 0) m bits)
    (runSegment (scheduledProgram ops bitWord fit) 3 (some 0) m bits) at hs
  cases hP : runSegment P fuel (some 0) m bits <;>
    cases hQ : runSegment (scheduledProgram ops bitWord fit) 3 (some 0) m bits <;>
    simp only [hP, hQ, Option.rel_some_some, Option.not_rel_some_none, Option.not_rel_none_some,
      Option.rel_none_none] at hs <;> try contradiction
  · simp
  · simp [hs.endState_eq (some 0)]

omit R in
private theorem returning_count (g : Fin M → Bool) (cells : List (Fin M)) (m : Memory w) :
    ((scheduledReports ops bitWord fit g cells m).filter fun r ↦ r.result.isSome).length =
      cells.length := by
  induction cells generalizing m with
  | nil => rfl
  | cons i xs ih => simp [scheduledReports, ih]

/-- A complete physical run for every bit assignment, with its exact final memory
and exact calls-plus-probes cost, including the terminal call. -/
theorem generated (m : Memory w) (hm : Pre m) (g : Fin M → Bool) :
    ∃ ps, runSegment P fuel (some 0) m
        ((List.finRange M).map (fun i ↦ (ops i).bits (g i)) ++ [[]]) = some ps ∧
      endState (some 0) ps = none ∧
      after m (eventLog ps) = scheduledMemory ops bitWord g (List.finRange M) m ∧
      RAMBuckets.cost Report.probes ps = scheduledCost ops + 3*M ∧
      ∀ p ∈ ps, 1 + p.probes ≤ 6 := by
  let bits := (List.finRange M).map (fun i ↦ (ops i).bits (g i)) ++ [[]]
  have hs := R.run_matched 0 (Nat.zero_le _) m hm bits
  change Option.Rel _ (runSegment P fuel (some 0) m bits)
    (runSegment (scheduledProgram ops bitWord fit) 3 (some 0) m bits) at hs
  rw [run_generated ops bitWord fit g m] at hs
  cases hP : runSegment P fuel (some 0) m bits with
  | none => simp [hP] at hs
  | some ps =>
    rw [hP, Option.rel_some_some] at hs
    refine ⟨ps, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hs.endState_eq, endState_append]
      rfl
    · rw [hs.after_eq]
      simp only [eventLog, List.flatMap_append, List.flatMap_cons, haltReport, List.flatMap_nil,
        List.append_nil]
      exact after_scheduledReports ..
    · rw [hs.cost_eq, generated_cost, List.filter_append]
      simp [haltReport, returning_count]
    · apply hs.per_call
      exact (scheduledReports_withinCaps ops bitWord fit g m (S := scheduledCost ops)
        (H := 3) (by decide) (by omega)).2

/-- For any accepting run, the interpreter's own reports carry the exact total
cost and respect the six-unit call bound. -/
theorem accepted_cost (m : Memory w) (hm : Pre m) (bits : List (List Bool)) {ps : List (Report w)}
    (hP : runSegment P fuel (some 0) m bits = some ps) (hend : endState (some 0) ps = none) :
    RAMBuckets.cost Report.probes ps = scheduledCost ops + 3*M ∧ ∀ p ∈ ps, 1 + p.probes ≤ 6 := by
  obtain ⟨g, rfl⟩ := (run_accepted_iff ops bitWord fit m bits).mp
    ((R.accepts_iff m hm bits).mp ⟨ps,hP,hend⟩)
  obtain ⟨ts, hr, _, _, hc, hcall⟩ := R.generated m hm g
  obtain rfl := Option.some.inj (hP.symm.trans hr)
  exact ⟨hc, hcall⟩

/-- Identity on the supplied per-call branch streams. Both the total budget and
the individual-call budget refer to the actual reports returned by each program. -/
def pathEquiv (m : Memory w) (hm : Pre m) {S H : ℕ} (hH : 6 ≤ H)
    (hTotal : scheduledCost ops + 3*M ≤ S*H) :
    ActualPaths P fuel 0 m (withinCaps S H) ≃
      ActualPaths (scheduledProgram ops bitWord fit) 3 0 m (withinCaps S H) := by
  apply Equiv.subtypeEquivRight
  intro bits
  constructor
  · rintro ⟨ps, hp, he, _⟩
    obtain ⟨g, rfl⟩ := (run_accepted_iff ops bitWord fit m bits).mp
      ((R.accepts_iff m hm bits).mp ⟨ps, hp, he⟩)
    exact ⟨_, run_generated ops bitWord fit g m, by rw [endState_append]; rfl,
      scheduledReports_withinCaps ops bitWord fit g m (by omega) (by omega)⟩
  · rintro ⟨qs, hq, he, _⟩
    obtain ⟨g, rfl⟩ := (run_accepted_iff ops bitWord fit m bits).mp ⟨qs, hq, he⟩
    obtain ⟨ps, hp, hend, _, hcost, hcall⟩ := R.generated m hm g
    exact ⟨ps, hp, hend, hcost.trans_le hTotal, fun p hmem ↦ (hcall p hmem).trans hH⟩

@[simp] theorem pathEquiv_val (m : Memory w) (hm : Pre m) {S H : ℕ} (hH : 6 ≤ H)
    (hTotal : scheduledCost ops + 3*M ≤ S*H) (p : ActualPaths P fuel 0 m (withinCaps S H)) :
    (R.pathEquiv m hm hH hTotal p).val = p.val := rfl

end PhysicalSchedule
end PrimedInputRAM

end VPVNP
end Computability
end OAI
