import OAI.Computability.VPVNP.LiveStageSegments
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Factoring native live-program paths at component completion

A stage may take a different number of calls on each branch. The first
accepting exit of its original opcode table still gives a unique split
of the linked machine's private choices. The stage tag is preserved on
continuing calls, and its accepting exit either writes a successor tag
or halts. Fuel accounts for the dispatcher and the final transfer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveStageLink

open BurstRAM BurstRAM.PrivateRAM

variable {w d r k : ℕ} {pcs : Fin d → ℕ}
variable (T : (s : Fin d) → Template (pcs s) r k) (next : Fin d → Option (Fin d))
variable (pub : Fin k → Word w) (addr : Word w) (s : Fin d)

/-- Burst-RAM program of a single source stage, obtained by instantiating that stage's
instruction template with the given public words. -/
abbrev sourceProgram := ((T s).instantiate w pub).program

/-- Linked burst-RAM program that reads the stage tag at the given address and follows the
successor map on component completion. -/
abbrev outerProgram := (machine T next pub addr).program

/-- The continuation starts from a fresh zero state after transfer. -/
def transferState (next : Fin d → Option (Fin d)) (s : Fin d) : Option (Word w) :=
  (next s).map (fun _ => 0)

/-- Each successful ordinary call leaves room for its linked exit. -/
def room (fuel : ℕ) (rep : Report w) : Prop := (exitReport next addr s rep).events.length < fuel

/-- The component may use scratch memory while preserving its outer stage
tag throughout all calls which continue this component. -/
def TagFrame (fuel : ℕ) (inv : Word w → Memory w → Prop) : Prop := ∀ st m bits rep st',
  inv st m → m addr.val = tagWord w s →
  execute (sourceProgram T pub s) fuel ((sourceProgram T pub s).start st) m bits = some rep →
  rep.result = some st' → inv st' (after m rep.events) ∧ after m rep.events addr.val = tagWord w s

/-- The exact first source-component completion with its final source memory.
This relation includes every private choice and native report in its order. -/
inductive Completion (fuel : ℕ) :
    Word w → Memory w → List (List Bool) → List (Report w) → Memory w → Prop
  | last {st m b rep}
      (call : execute (sourceProgram T pub s) fuel ((sourceProgram T pub s).start st) m b = some rep)
      (halt : rep.result = none) (fits : room next addr s fuel rep) :
      Completion fuel st m [b] [rep] (after m rep.events)
  | more {st m b rep st' bs reps m'}
      (call : execute (sourceProgram T pub s) fuel ((sourceProgram T pub s).start st) m b = some rep)
      (cont : rep.result = some st') (fits : room next addr s fuel rep)
      (tail : Completion fuel st' (after m rep.events) bs reps m') :
      Completion fuel st m (b :: bs) (rep :: reps) m'

variable {T next pub addr s}

theorem Completion.spec {fuel st m bs reps m'} (h : Completion T next pub addr s fuel st m bs reps m') :
    runSegment (sourceProgram T pub s) fuel (some st) m bs = some reps ∧
    endState (some st) reps = none ∧ after m (eventLog reps) = m' ∧ ∀ rep ∈ reps, room next addr s fuel rep := by
  induction h with
  | last hc ht hf => simp [runSegment, hc, endState, ht, eventLog, hf]
  | more hc ht hf _ ih =>
    refine ⟨by simp only [runSegment, hc, ht, ih.1, Option.map_some],
      by simpa only [endState, ht] using ih.2.1, ?_, List.forall_mem_cons.mpr ⟨hf, ih.2.2.2⟩⟩
    simpa only [eventLog, List.flatMap_cons, after, List.foldl_append] using ih.2.2.1

theorem completion_of_run {fuel st m bs reps}
    (h : runSegment (sourceProgram T pub s) fuel (some st) m bs = some reps)
    (halt : endState (some st) reps = none) (fits : ∀ rep ∈ reps, room next addr s fuel rep) :
    Completion T next pub addr s fuel st m bs reps (after m (eventLog reps)) := by
  induction bs generalizing st m reps with
  | nil =>
    simp [runSegment] at h
    subst reps
    contradiction
  | cons b bs ih =>
    rw [runSegment] at h
    cases hc : execute (sourceProgram T pub s) fuel ((sourceProgram T pub s).start st) m b with
    | none => simp [hc] at h
    | some rep =>
      rw [hc, Option.map_eq_some_iff] at h
      obtain ⟨rs, hr, rfl⟩ := h
      change endState rep.result rs = none at halt
      obtain ⟨hf,ht⟩ := List.forall_mem_cons.mp fits
      cases he : rep.result with
      | none =>
        rw [he] at hr
        cases bs with
        | nil =>
          simp [runSegment] at hr
          subst rs
          simpa [eventLog] using Completion.last hc he hf
        | cons _ _ => contradiction
      | some st' =>
        rw [he] at hr halt
        simpa only [eventLog, List.flatMap_cons, after, List.foldl_append] using
          Completion.more hc he hf (ih hr halt ht)

private theorem linked_ok {fuel st m b rep} (hfit : d ≤ 2^w)
    (htag : m addr.val = tagWord w s)
    (call : execute (sourceProgram T pub s) fuel ((sourceProgram T pub s).start st) m b = some rep)
    (fits : room next addr s fuel rep) :
    execute (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length)
      ((outerProgram T next pub addr).start st) m b = some (linkedReport next addr s rep) := by
  rw [execute_linked T next pub addr s hfit st fuel m htag b, call]
  simp [boundedExit, room] at fits ⊢
  exact ⟨fits, rfl⟩

private theorem linked_inv {fuel st m b out} (hfit : d ≤ 2^w)
    (htag : m addr.val = tagWord w s)
    (call : execute (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length)
      ((outerProgram T next pub addr).start st) m b = some out) :
    ∃ rep, execute (sourceProgram T pub s) fuel ((sourceProgram T pub s).start st) m b = some rep ∧
      room next addr s fuel rep ∧ out = linkedReport next addr s rep := by
  rw [execute_linked T next pub addr s hfit st fuel m htag b] at call
  cases hs : execute (sourceProgram T pub s) fuel ((sourceProgram T pub s).start st) m b with
  | none => simp [hs] at call
  | some rep =>
    refine ⟨rep,rfl,?_⟩
    simp only [hs, Option.bind_some, boundedExit] at call
    split at call
    · rename_i hf
      exact ⟨hf, (Option.some.inj call).symm⟩
    · contradiction

private theorem linked_continue {rep : Report w} {st : Word w} (h : rep.result = some st) :
    (linkedReport next addr s rep).result = some st := by simp [linkedReport, prependLog, exitReport, h]

private theorem linked_last {rep : Report w} (h : rep.result = none) :
    (linkedReport next addr s rep).result = transferState (w := w) next s := by
  cases hs : next s <;> simp [linkedReport, prependLog, exitReport, transferState, h, hs]

private theorem memory_last {rep : Report w} {m : Memory w} (h : rep.result = none) :
    after m (linkedReport next addr s rep).events = transferMemory addr (next s) (after m rep.events) := by
  rw [linkedReport_after]
  cases next s <;> simp [transferMemory, h]

/-- An ordinary completed stage splices into any continuation without adding
branch choices. Every native report of that stage gains its linker events. -/
theorem Completion.splice {fuel st m bs reps m'} (h : Completion T next pub addr s fuel st m bs reps m')
    (fit : d ≤ 2^w) {inv : Word w → Memory w → Prop} (frame : TagFrame T pub addr s fuel inv)
    (hi : inv st m) (htag : m addr.val = tagWord w s) (tail : List (List Bool)) :
    let P := outerProgram T next pub addr
    let cap := fuel+(dispatchEvents addr s).length
    runSegment P cap (some st) m (bs ++ tail) =
      (runSegment P cap (transferState next s) (transferMemory addr (next s) m') tail).map
        ((reps.map (linkedReport next addr s)) ++ ·) := by
  dsimp only
  induction h with
  | last hc hh hf =>
    simp only [List.singleton_append, runSegment, linked_ok fit htag hc hf, linked_last hh, memory_last hh,
      List.map_cons, List.map_nil, List.singleton_append]
  | more hc hh hf _ ih =>
    simp only [List.cons_append, runSegment, linked_ok fit htag hc hf, linked_continue hh, linkedReport_after, hh]
    obtain ⟨hi',ht'⟩ := frame _ _ _ _ _ hi htag hc hh
    rw [ih hi' ht']
    simp [Option.map_map, Function.comp_def]

/-- A halted linked path starting in this component must reach its first
ordinary accepting exit. The suffix has exactly the reset word and memory
specified by the transfer and can include any number of later stages. -/
theorem split_halted {fuel st m bs logs} (fit : d ≤ 2^w) {inv : Word w → Memory w → Prop}
    (frame : TagFrame T pub addr s fuel inv) (hi : inv st m) (htag : m addr.val = tagWord w s)
    (hr : runSegment (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length)
      (some st) m bs = some logs) (halt : endState (some st) logs = none) :
    ∃ first rest reps lastMem tailLogs,
      bs = first ++ rest ∧ logs = reps.map (linkedReport next addr s) ++ tailLogs ∧
      Completion T next pub addr s fuel st m first reps lastMem ∧
      runSegment (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length)
        (transferState next s) (transferMemory addr (next s) lastMem) rest = some tailLogs ∧
      endState (transferState next s) tailLogs = none := by
  induction bs generalizing st m logs with
  | nil =>
    simp only [runSegment, Option.some.injEq] at hr
    subst logs
    contradiction
  | cons b bs ih =>
    rw [runSegment] at hr
    cases hx : execute (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length)
        ((outerProgram T next pub addr).start st) m b with
    | none => simp [hx] at hr
    | some out =>
      rw [hx, Option.map_eq_some_iff] at hr
      obtain ⟨logs',hr,rfl⟩ := hr
      obtain ⟨rep,hc,hf,rfl⟩ := linked_inv fit htag hx
      change endState (linkedReport next addr s rep).result logs' = none at halt
      cases he : rep.result with
      | none =>
        rw [linked_last he, memory_last he] at hr
        rw [linked_last he] at halt
        exact ⟨[b],bs,[rep],after m rep.events,logs',rfl,rfl,.last hc he hf,hr,halt⟩
      | some st' =>
        rw [linked_continue he, linkedReport_after] at hr
        simp only [he] at hr
        rw [linked_continue he] at halt
        obtain ⟨hi',ht'⟩ := frame _ _ _ _ _ hi htag hc he
        obtain ⟨first,rest,reps,lastMem,tailLogs,rfl,rfl,comp,runTail,stop⟩ := ih hi' ht' hr halt
        exact ⟨b::first,rest,rep::reps,lastMem,tailLogs,rfl,rfl,.more hc he hf comp,runTail,stop⟩

/-- Determinism of native execution fixes the first completed component
inside a given complete sequence of choices. The source memory and reports
are fixed along with the position of the split. -/
theorem Completion.uniqueSplit {fuel st m first reps lastMem}
    (one : Completion T next pub addr s fuel st m first reps lastMem)
    {other reps' lastMem'} (two : Completion T next pub addr s fuel st m other reps' lastMem')
    {rest rest' : List (List Bool)} (eq : first ++ rest = other ++ rest') :
    first = other ∧ reps = reps' ∧ lastMem = lastMem' ∧ rest = rest' := by
  induction one generalizing other reps' lastMem' with
  | last hc he hf =>
    cases two with
    | last hc' he' hf' =>
      obtain ⟨rfl,rfl⟩ := List.cons.inj eq
      have hrep := Option.some.inj (hc.symm.trans hc')
      subst_vars
      exact ⟨rfl,rfl,rfl,rfl⟩
    | more hc' he' hf' ht =>
      obtain ⟨rfl,_⟩ := List.cons.inj eq
      have hrep := Option.some.inj (hc.symm.trans hc')
      rw [← hrep, he] at he'
      contradiction
  | more hc he hf _ ih =>
    cases two with
    | last hc' he' hf' =>
      obtain ⟨rfl,_⟩ := List.cons.inj eq
      have hrep := Option.some.inj (hc.symm.trans hc')
      rw [← hrep, he] at he'
      contradiction
    | more hc' he' hf' ht =>
      obtain ⟨rfl,htail⟩ := List.cons.inj eq
      obtain rfl := Option.some.inj (hc.symm.trans hc')
      obtain rfl := Option.some.inj (he.symm.trans he')
      obtain ⟨rfl,rfl,rfl,rfl⟩ := ih ht htail
      exact ⟨rfl,rfl,rfl,rfl⟩

variable (T next pub addr s)

/-- A full native branch of the component followed by a native branch of
the linked remainder. The cap is imposed on the actual concatenated reports. -/
@[ext] structure Parts (fuel : ℕ) (st : Word w) (m : Memory w) (cap : List (Report w) → Prop) where
  /-- Per-call choice tapes used through the current source stage's first accepting exit,
  including the tape for its final call. -/
  first : List (List Bool)
  /-- Choice tapes for the linked continuation starting with the state and memory produced by
  transfer out of the completed stage. -/
  rest : List (List Bool)
  /-- Source reports produced by the calls in the first part, in execution order before the
  linker's dispatcher and transfer events are added. -/
  reports : List (Report w)
  /-- Source-stage memory after the final call and before transfer to the successor stage. -/
  lastMem : Memory w
  /-- Linked reports produced by running the remaining tapes from the transferred state and
  memory until the outer program halts. -/
  tailReports : List (Report w)
  completed : Completion T next pub addr s fuel st m first reports lastMem
  tailRun : runSegment (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length)
    (transferState next s) (transferMemory addr (next s) lastMem) rest = some tailReports
  tailHalt : endState (transferState next s) tailReports = none
  within : cap (reports.map (linkedReport next addr s) ++ tailReports)

variable {T next pub addr s}

private theorem Completion.linkedEnd {fuel st m first reps lastMem}
    (one : Completion T next pub addr s fuel st m first reps lastMem) :
    endState (some st) (reps.map (linkedReport next addr s)) = transferState next s := by
  induction one with
  | last _ he _ => exact linked_last he
  | more _ he _ _ ih => simpa only [List.map_cons, endState, linked_continue he] using ih

/-- Concatenate the two native choice streams. -/
def Parts.join {fuel st m cap} (fit : d ≤ 2^w) {inv : Word w → Memory w → Prop}
    (frame : TagFrame T pub addr s fuel inv) (hi : inv st m) (htag : m addr.val = tagWord w s)
    (p : Parts T next pub addr s fuel st m cap) :
    ActualPaths (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length) st m cap :=
  ⟨p.first ++ p.rest, p.reports.map (linkedReport next addr s) ++ p.tailReports, by
    rw [p.completed.splice fit frame hi htag p.rest, p.tailRun, Option.map_some],
    by rw [endState_append, p.completed.linkedEnd, p.tailHalt], p.within⟩

private theorem join_injective {fuel st m cap} (fit : d ≤ 2^w) {inv : Word w → Memory w → Prop}
    (frame : TagFrame T pub addr s fuel inv) (hi : inv st m) (htag : m addr.val = tagWord w s) :
    Function.Injective (Parts.join (next := next) (cap := cap) fit frame hi htag) := by
  intro a b eq
  obtain ⟨af,ar,ap,am,at',ac,arun,ah,aw⟩ := a
  obtain ⟨bf,br,bp,bm,bt',bc,bt,bh,bw⟩ := b
  obtain ⟨rfl,rfl,rfl,rfl⟩ := ac.uniqueSplit bc (congrArg Subtype.val eq)
  obtain rfl := Option.some.inj (arun.symm.trans bt)
  rfl

/-- Native accepting paths at the selected tag are bijective to the ordered
choice of the first completed component and the accepted continuation. The
bijection remains valid for variable component lengths and resource caps
depending on the entire joined report sequence. -/
noncomputable def partsEquiv {fuel st m cap} (fit : d ≤ 2^w) {inv : Word w → Memory w → Prop}
    (frame : TagFrame T pub addr s fuel inv) (hi : inv st m) (htag : m addr.val = tagWord w s) :
    Parts T next pub addr s fuel st m cap ≃
      ActualPaths (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length) st m cap :=
  Equiv.ofBijective (Parts.join fit frame hi htag) ⟨join_injective fit frame hi htag, by
    intro a
    obtain ⟨bits,logs,hr,halt,hcap⟩ := a
    obtain ⟨first,rest,reps,lastMem,tailLogs,rfl,rfl,comp,runTail,stop⟩ :=
      split_halted fit frame hi htag hr halt
    exact ⟨⟨first,rest,reps,lastMem,tailLogs,comp,runTail,stop,hcap⟩,rfl⟩⟩

variable (T next pub addr s)

/-- Ordinary complete paths satisfying the linked stage's per-call clock. -/
abbrev Ordinary (fuel : ℕ) (st : Word w) (m : Memory w) :=
  ActualPaths (sourceProgram T pub s) fuel st m (fun rs => ∀ rep ∈ rs, room next addr s fuel rep)

variable {T next pub addr s}

/-- The report list of a completed ordinary source path, recovered from its successful run on
the path's own choice tapes. -/
noncomputable def ordinaryReports {fuel st m} (p : Ordinary T next pub addr s fuel st m) : List (Report w) :=
  p.property.choose

theorem ordinaryRun {fuel st m} (p : Ordinary T next pub addr s fuel st m) :
    runSegment (sourceProgram T pub s) fuel (some st) m p.val = some (ordinaryReports p) :=
  p.property.choose_spec.1

/-- Suffix choices carry the *joined* report cap. Their start memory is the
actual memory after the selected ordinary path and its transfer. -/
abbrev Remainder {fuel st m} (cap : List (Report w) → Prop) (p : Ordinary T next pub addr s fuel st m) :=
  {bits : List (List Bool) // ∃ logs,
    runSegment (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length) (transferState next s)
      (transferMemory addr (next s) (after m (eventLog (ordinaryReports p)))) bits = some logs ∧
    endState (transferState next s) logs = none ∧ cap ((ordinaryReports p).map (linkedReport next addr s) ++ logs)}

private noncomputable def pack {fuel st m cap} (p : Ordinary T next pub addr s fuel st m)
    (q : Remainder cap p) : Parts T next pub addr s fuel st m cap where
  first := p.val
  rest := q.val
  reports := ordinaryReports p
  lastMem := after m (eventLog (ordinaryReports p))
  tailReports := q.property.choose
  completed := completion_of_run (ordinaryRun p) p.property.choose_spec.2.1 p.property.choose_spec.2.2
  tailRun := q.property.choose_spec.1
  tailHalt := q.property.choose_spec.2.1
  within := q.property.choose_spec.2.2

/-- Factorization in ordinary stage-path types. Replaying the first path fixes
its source reports, final memory, and every argument to the continuation. -/
noncomputable def ordinaryEquiv {fuel st m cap} (fit : d ≤ 2^w) {inv : Word w → Memory w → Prop}
    (frame : TagFrame T pub addr s fuel inv) (hi : inv st m) (htag : m addr.val = tagWord w s) :
    (Σ p : Ordinary T next pub addr s fuel st m, Remainder cap p) ≃
      ActualPaths (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length) st m cap :=
  (Equiv.ofBijective (fun p : Σ a : Ordinary T next pub addr s fuel st m, Remainder cap a => pack p.1 p.2) ⟨by
    rintro ⟨p,q⟩ ⟨p',q'⟩ eq
    have hp : p = p' := Subtype.ext (congrArg Parts.first eq)
    subst p'
    exact congrArg (Sigma.mk p) (Subtype.ext (congrArg Parts.rest eq)), by
    intro a
    obtain ⟨first,rest,reps,lastMem,tailLogs,comp,runTail,stop,hcap⟩ := a
    obtain ⟨run,halt,memEq,roomEq⟩ := comp.spec
    let p : Ordinary T next pub addr s fuel st m := ⟨first,reps,run,halt,roomEq⟩
    have er : ordinaryReports p = reps := Option.some.inj ((ordinaryRun p).symm.trans run)
    let q : Remainder cap p := ⟨rest,tailLogs,by simpa only [er,memEq] using runTail,stop,
      by simpa only [er] using hcap⟩
    have et : q.property.choose = tailLogs := by
      apply Option.some.inj (q.property.choose_spec.1.symm.trans _)
      simpa only [er,memEq] using runTail
    refine ⟨⟨p,q⟩,?_⟩
    apply Parts.ext <;> first | rfl | exact er | exact et | exact (congrArg (fun rs => after m (eventLog rs)) er).trans memEq⟩).trans (partsEquiv fit frame hi htag)

/-- The exact finite sum used when successive live phases are counted. -/
theorem count_stage_remainders {fuel st m cap} (fit : d ≤ 2^w) {inv : Word w → Memory w → Prop}
    (frame : TagFrame T pub addr s fuel inv) (hi : inv st m) (htag : m addr.val = tagWord w s)
    [Fintype (Ordinary T next pub addr s fuel st m)]
    [∀ p : Ordinary T next pub addr s fuel st m, Finite (Remainder cap p)] :
    Nat.card (ActualPaths (outerProgram T next pub addr) (fuel+(dispatchEvents addr s).length) st m cap) =
      ∑ p : Ordinary T next pub addr s fuel st m, Nat.card (Remainder cap p) := by
  rw [Nat.card_congr (ordinaryEquiv fit frame hi htag).symm, Nat.card_sigma]

end LiveStageLink

end VPVNP
end Computability
end OAI
