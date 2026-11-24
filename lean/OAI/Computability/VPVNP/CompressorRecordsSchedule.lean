import OAI.Computability.VPVNP.CompressorRecordFrame
import OAI.Computability.VPVNP.LiveHeaderBoundedRun
import OAI.Computability.VPVNP.LiveStageLinkPaths
import OAI.Computability.VPVNP.CompressorRecordsCursorScan
import OAI.Computability.VPVNP.CompressorRecordRefreshRAM

/-!
# A fixed dispatcher for the compressor descriptor passes

The controller occupies tag zero. A worker has a finite native table and
its own public parameter format. On each worker call the active frame
supplies an exclusive cursor bound followed by the parameters. At the
bound the stage linker writes tag zero and returns to the controller. Thus
level counts and pass repetitions change memory and cursors while the
dispatcher table is fixed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

/-- A worker with its actual finite register and parameter arities. -/
structure Pass where
  /-- Number of instruction labels in the pass’s native RAM table. -/
  pcs : ℕ
  /-- Number of private registers available to instructions in this pass. -/
  regs : ℕ
  /-- Number of public operand words expected by the native pass. A scheduled call loads these
  words from the active frame after the stop word. -/
  params : ℕ
  /-- The pass’s native instruction table, indexed by its own instruction labels, private
  registers, and public operands. -/
  table : Template pcs regs params

/-- An indexed family of native passes. The dispatcher assigns the pass at index `i` to tag `i
+ 1` and reserves tag zero for the controller. -/
abbrev Catalog (d : ℕ) := Fin d → Pass

/-- Native pass that writes six cursor-incidence entries for one outgoing port and returns the
next port index in register zero. -/
def cursorPass : Pass := ⟨_,_,_,PrimedStackRAM.template CursorRAM.visit 0⟩
/-- Native pass that writes a segment’s outgoing and incoming offsets and incoming width,
updates the bundle total, and returns the next segment index. -/
def refreshPass : Pass := ⟨_,_,_,PrimedStackRAM.template RefreshRAM.visit 0⟩

/-- Small concrete catalog used to link the initial cursor and refresh scans. -/
def cursorRefresh : Catalog 2 := ![cursorPass,refreshPass]

/-- Maximum number of public operands among the catalog’s passes, or zero for an empty catalog.
This fixes the width of the directory’s parameter bank. -/
def arity {d : ℕ} (C : Catalog d) : ℕ := Finset.univ.sup fun i ↦ (C i).params

theorem params_le_arity {d : ℕ} (C : Catalog d) (i : Fin d) : (C i).params ≤ arity C :=
  Finset.le_sup (f := fun j ↦ (C j).params) (Finset.mem_univ i)

variable {w d p r : ℕ}

/-- The bounded-table library numbers its exclusive stop last. A directory
frame places it first, followed by the worker's original public words. -/
private def field {k : ℕ} : Fin (k+1) → Fin (k+1) := Fin.lastCases 0 Fin.succ

private def guarded (P : Pass) :=
  LiveStageLink.widen (LiveHeaderBounded.bounded P.table) (Function.Embedding.refl _) field

/-- Wrap a native pass in a frame loader and a cursor guard. Its sole public word points to the
frame, whose first word is the exclusive stop and whose remaining words supply the pass
operands. -/
def worker (P : Pass) : Pass := ⟨_,_,_,Frame.compile (guarded P)⟩

/-- Limit and original public words in the order seen by the running worker. -/
def stopWord (base : Word w) (m : Memory w) : Word w := m base.val

/-- Read native operand `j` at active-frame offset `j + 1`, immediately after the exclusive
stop stored at offset zero. -/
def parameters {k : ℕ} (base : Word w) (m : Memory w) (j : Fin k) : Word w :=
  Frame.data base m (j.succ : Fin (k+1))

private theorem fields_correct (P : Pass) (base : Word w) (m : Memory w) :
    (Frame.data base m : Fin (P.params+1) → Word w) ∘ field =
      LiveHeaderBounded.publicData (parameters base m) (stopWord base m) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [field, Frame.data, stopWord, LiveHeaderBounded.publicData ]
  | cast j => simp [field, parameters, LiveHeaderBounded.publicData ]

/-- Report for an active worker call. The frame loads and three cursor-guard ticks precede the
native pass events, and the call returns the native result. -/
def workerReport (P : Pass) (base : Word w) (m : Memory w) (rep : Report w) : Report w :=
  LiveStageLink.prependLog (Frame.loadEvents base m 0 (P.params+1))
    (LiveHeaderBounded.activeReport rep)

private theorem execute_guarded (P : Pass) (base state : Word w) (m : Memory w) (bits : List Bool)
    (f : ℕ) :
    let S := ((guarded P).instantiate w (Frame.data base m)).program
    let B := (LiveHeaderBounded.machine P.table (parameters base m) (stopWord base m)).program
    execute S f (S.start state) m bits = execute B f (B.start state) m bits := by
  dsimp only
  rw [show guarded P = LiveStageLink.widen (LiveHeaderBounded.bounded P.table)
    (Function.Embedding.refl _) field from rfl, LiveStageLink.execute_widen_start, fields_correct]

theorem execute_worker (P : Pass) (base state : Word w) (m : Memory w) (bits : List Bool)
    (hlt : state < stopWord base m) (fuel : ℕ) :
    let W := ((worker P).table.instantiate w (fun _ ↦ base)).program
    let S := (P.table.instantiate w (parameters base m)).program
    execute W (fuel+3+4*(P.params+1)) (W.start state) m bits =
      (execute S fuel (S.start state) m bits).map (workerReport P base m) := by
  dsimp only
  change execute (Frame.machine (guarded P) base).program _ ((Frame.machine (guarded P)
    base).program.start state) m bits = _
  rw [Frame.execute_frame (guarded P) base state (fuel+3) m bits, execute_guarded,
    LiveHeaderBounded.execute_active P.table (parameters base m) (stopWord base m) fuel state hlt,
    Option.map_map]
  rfl

private def stopReport (P : Pass) (base : Word w) (m : Memory w) :=
  LiveStageLink.prependLog (Frame.loadEvents base m 0 (P.params+1))
    (LiveHeaderBounded.closedReport w)

theorem execute_worker_stop (P : Pass) (base state : Word w) (m : Memory w) (bits : List Bool)
    (hle : stopWord base m ≤ state) (extra : ℕ) :
    let W := ((worker P).table.instantiate w (fun _ ↦ base)).program
    execute W (extra+4+4*(P.params+1)) (W.start state) m bits =
      if bits = [] then some (stopReport P base m) else none := by
  dsimp only
  change execute (Frame.machine (guarded P) base).program _ ((Frame.machine (guarded P)
    base).program.start state) m bits = _
  rw [Frame.execute_frame (guarded P) base state (extra+4) m bits, execute_guarded,
    LiveHeaderBounded.execute_closed P.table (parameters base m) (stopWord base m) extra state hle]
  cases bits <;> rfl

/-- Shared public words of the enclosing stage linker. The internal tag is
separate from the enclosing live program's stage tag. -/
structure Ports (w : ℕ) where
  /-- Base address of the active worker frame, which stores the exclusive cursor bound followed
  by the worker’s public operands. -/
  activeFrame : Word w
  /-- Base address of the descriptor directory from which the controller loads each scheduled
  row. -/
  directory : Word w
  /-- Address of the control cell holding the index of the next directory row to launch. -/
  ordinal : Word w
  /-- Address of the cell holding the directory row count. The controller finishes when the
  ordinal reaches this count. -/
  rows : Word w
  /-- Address of the internal dispatch tag. Zero selects the controller and tag `i + 1` selects
  worker `i`. -/
  tag : Word w

/-- The five shared public words in operand order are the active-frame base, directory base,
ordinal address, row-count address, and dispatch-tag address. -/
def Ports.data (ports : Ports w) : Fin 5 → Word w :=
    ![ports.activeFrame,ports.directory,ports.ordinal,ports.rows,ports.tag]

/-- A stage is widened only after its operand format and optional frame loader
have been chosen. This keeps the original worker register budgets independent. -/
structure Slot extends Pass where
  /-- Selects the shared public word for each operand of the slot. The controller uses all five
  words in order, and a framed worker uses only the active-frame base. -/
  publicIndex : Fin params → Fin 5

private def workerSlot (P : Pass) : Slot := ⟨worker P, fun _ ↦ 0⟩

variable (C : Catalog d) (controller : Template p r 5)

/-- Assign the controller to slot zero and the framed, guarded version of catalog pass `i` to
slot `i + 1`. -/
def slots : Fin (d+1) → Slot := Fin.cons ⟨⟨p,r,5,controller⟩,id⟩ (fun i ↦ workerSlot (C i))

private def registerCount : ℕ := Finset.univ.sup fun s ↦ (slots C controller s).regs

private def regEmbedding (s : Fin (d + 1)) :
    Fin (slots C controller s).regs ↪ Fin (registerCount C controller) :=
  Fin.castLEEmb (Finset.le_sup (f := fun t ↦ (slots C controller t).regs) (Finset.mem_univ s))

/-- Widen a slot’s native table to the largest register count among all slots and map its
public operands into the dispatcher’s five shared words. -/
def tables (s : Fin (d + 1)) : Template (slots C controller s).pcs (registerCount C controller)
    5 :=
  LiveStageLink.widen (slots C controller s).table (regEmbedding C controller s)
    (slots C controller s).publicIndex

/-- The controller explicitly writes the computed worker tag and returns
its initial cursor. An accepting worker transfers back to the controller. -/
def handoff : Fin (d+1) → Option (Fin (d+1)) := Fin.cons none (fun _ ↦ some 0)

/-- The linked dispatcher table for the controller and catalog workers. Accepting a worker
transfers control to slot zero, while accepting the controller finishes the schedule. -/
def template := LiveStageLink.linked (tables C controller) handoff

/-- Instantiate the linked dispatcher at word width `w` with the five port words and
`ports.tag` as the address from which the linker reads the active slot. -/
def machine (ports : Ports w) :=
  LiveStageLink.machine (tables C controller) handoff ports.data ports.tag

private theorem call_slot (ports : Ports w) (s : Fin (d + 1)) (state : Word w) (m : Memory w)
    (htag : m ports.tag.val = LiveStageLink.tagWord w s) (fits : d + 1 ≤ 2 ^ w)
    (bits : List Bool) {f cap : ℕ} (hcap : f + 2 * (d + 1) + 5 ≤ cap) {rep : Report w}
    (hsource : let S := ((slots C controller s).table.instantiate w (ports.data ∘
      (slots C controller s).publicIndex)).program
      execute S f (S.start state) m bits = some rep) :
    let D := (machine C controller ports).program
    execute D cap (D.start state) m bits = some (LiveStageLink.linkedReport handoff ports.tag s
      rep) := by
  apply LiveStageLink.execute_linked_of_stage _ _ _ _ s fits hcap _ _ htag bits rep
  rw [tables, LiveStageLink.execute_widen_start]
  exact hsource

/-- One successful call of a source worker inside the actual finite
descriptor dispatcher. Its incoming tag and guard are read from RAM. -/
theorem worker_active (ports : Ports w) (i : Fin d) (state : Word w) (m : Memory w)
    (bits : List Bool)
    (htag : m ports.tag.val = LiveStageLink.tagWord w i.succ) (fits : d + 1 ≤ 2 ^ w)
    (hlt : state < stopWord ports.activeFrame m) {f cap : ℕ}
    (hcap : f + 3 + 4 * ((C i).params + 1) + 2 * (d + 1) + 5 ≤ cap) (rep : Report w)
    (hsource : let S := ((C i).table.instantiate w (parameters ports.activeFrame m)).program
      execute S f (S.start state) m bits = some rep) :
    let D := (machine C controller ports).program
    execute D cap (D.start state) m bits = some
      (LiveStageLink.linkedReport handoff ports.tag i.succ (workerReport
        (C i) ports.activeFrame m rep)) := by
  apply call_slot C controller ports i.succ state m htag fits bits hcap
  change execute (((worker (C i)).table.instantiate w (fun _ ↦ ports.activeFrame)).program) _
    (((worker (C i)).table.instantiate w (fun _ ↦ ports.activeFrame)).program.start state) m bits
      = _
  rw [execute_worker _ _ _ _ _ hlt, hsource]
  rfl

/-- The single empty-choice call at the exclusive bound transfers back to
the controller, which can select another pass or the next level. -/
theorem worker_stop (ports : Ports w) (i : Fin d) (state : Word w) (m : Memory w)
    (htag : m ports.tag.val = LiveStageLink.tagWord w i.succ) (fits : d + 1 ≤ 2 ^ w)
    (hle : stopWord ports.activeFrame m ≤ state) {cap : ℕ} (hcap : 4 + 4 * ((C i).params + 1)
      + 2 * (d + 1) + 5
      ≤ cap) :
    let D := (machine C controller ports).program
    execute D cap (D.start state) m [] = some
      (LiveStageLink.linkedReport handoff ports.tag i.succ (stopReport
        (C i) ports.activeFrame m)) := by
  apply call_slot C controller ports i.succ state m htag fits [] hcap
  change execute (((worker (C i)).table.instantiate w (fun _ ↦ ports.activeFrame)).program) _
    (((worker (C i)).table.instantiate w (fun _ ↦ ports.activeFrame)).program.start state) m [] = _
  exact execute_worker_stop _ _ _ _ [] hle 0

/-- Any successful call of the controller is also a native call in the
descriptor dispatcher. The controller's accepting exit terminates the schedule. -/
theorem controller_call (ports : Ports w) (state : Word w) (m : Memory w) (bits : List Bool)
    (htag : m ports.tag.val = 0) (fits : d + 1 ≤ 2 ^ w) {f cap : ℕ} (hcap : f + 2 *
      (d + 1) + 5 ≤ cap)
    (rep : Report w) (hc : let S := (controller.instantiate w ports.data).program
      execute S f (S.start state) m bits = some rep) :
    let D := (machine C controller ports).program
    execute D cap (D.start state) m bits = some
      (LiveStageLink.linkedReport handoff ports.tag (0 : Fin (d+1)) rep) :=
  call_slot C controller ports 0 state m htag fits bits hcap hc

/-- Tagged reports of active data calls and of the single closing call. -/
def activeLinkedReport (i : Fin d) (ports : Ports w) (m : Memory w) (rep : Report w) : Report w :=
  LiveStageLink.linkedReport handoff ports.tag i.succ (workerReport (C i) ports.activeFrame m rep)

/-- Report of the closing call at or beyond worker `i`’s exclusive bound. It reads the dispatch
tag and frame, writes tag zero, and returns cursor zero to the controller. -/
def closedLinkedReport (i : Fin d) (ports : Ports w) (m : Memory w) : Report w :=
  LiveStageLink.linkedReport handoff ports.tag i.succ (stopReport (C i) ports.activeFrame m)

theorem activeLinkedReport_effect (i : Fin d) (ports : Ports w) (m : Memory w) (rep : Report w)
    {st : Word w} (h : rep.result = some st) :
    let out := activeLinkedReport C i ports m rep
    out.result = some st ∧ after m out.events = after m rep.events ∧
      choiceBits out.events = choiceBits rep.events ∧ out.probes = rep.probes +
        (C i).params + 2 := by
  let q := workerReport (C i) ports.activeFrame m rep
  have cost := Frame.frame_cost ports.activeFrame m 0 ((C i).params+1)
    (LiveHeaderBounded.activeReport rep)
  have hq : q.result = some st := h
  dsimp only
  change (LiveStageLink.linkedReport handoff ports.tag i.succ q).result = _ ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [LiveStageLink.linkedReport, LiveStageLink.prependLog, LiveStageLink.exitReport, hq]
  · rw [activeLinkedReport, LiveStageLink.linkedReport_after]
    rw [show workerReport (C i) ports.activeFrame m rep = q from rfl, hq]
    exact cost.2.2.2.1
  · rw [activeLinkedReport, LiveStageLink.linkedReport_choiceBits]
    exact cost.2.2.1
  · rw [activeLinkedReport, LiveStageLink.linkedReport_probes]
    change q.probes+1+(if q.result = none ∧ _ then 1 else 0) = _
    rw [hq]
    have hp : q.probes = (C i).params+1+rep.probes := cost.2.1
    simp [hp]
    omega

/-- Finishing a pass writes precisely the internal controller tag and returns
cursor zero. There are two tag probes plus one read per active-frame word. -/
theorem closedLinkedReport_effect (i : Fin d) (ports : Ports w) (m : Memory w) :
    let out := closedLinkedReport C i ports m
    out.result = some 0 ∧ after m out.events = writeMemory m ports.tag 0 ∧
      choiceBits out.events = [] ∧ out.probes = (C i).params + 3 := by
  let q := stopReport (C i) ports.activeFrame m
  have cost := Frame.frame_cost ports.activeFrame m 0 ((C i).params+1)
    (LiveHeaderBounded.closedReport w)
  have hq : q.result = none := rfl
  have hn : handoff i.succ = some (0 : Fin (d+1)) := Fin.cons_succ ..
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · change (LiveStageLink.linkedReport handoff ports.tag i.succ q).result = _
    simp [LiveStageLink.linkedReport, LiveStageLink.prependLog, LiveStageLink.exitReport, hq, hn]
  · rw [closedLinkedReport, LiveStageLink.linkedReport_after]
    rw [show stopReport (C i) ports.activeFrame m = q from rfl, hq, hn]
    have hm : after m q.events = m := cost.2.2.2.1
    change writeMemory (after m q.events) ports.tag (LiveStageLink.tagWord w (0 : Fin (d+1))) = _
    rw [hm]
    rfl
  · rw [closedLinkedReport, LiveStageLink.linkedReport_choiceBits]
    exact cost.2.2.1
  · rw [closedLinkedReport, LiveStageLink.linkedReport_probes]
    change q.probes+1+(if q.result = none ∧ _ then 1 else 0) = _
    rw [hq, hn]
    have hp : q.probes = (C i).params+1+0 := cost.2.1
    simp [hp]

/-- Active-frame and dispatcher cells that must survive an ordinary pass. -/
def Ready (i : Fin d) (ports : Ports w) (pub : Fin (C i).params → Word w) (bound : Word w)
    (m : Memory w) : Prop :=
  m ports.tag.val = LiveStageLink.tagWord w i.succ ∧
    stopWord ports.activeFrame m = bound ∧ parameters ports.activeFrame m = pub

/-- Each source report is below the stop and returns a new cursor. At the
end the native guard observes the stop. This allows arbitrary cursor steps. -/
def ValidTrace (i : Fin d) (ports : Ports w) (pub : Fin (C i).params → Word w) (bound : Word w) :
    Word w → Memory w → List (Report w) → Prop
  | st, m, [] => Ready C i ports pub bound m ∧ bound ≤ st
  | st, m, rep :: rs => Ready C i ports pub bound m ∧ st < bound ∧
      ∃ next, rep.result = some next ∧ ValidTrace i ports pub bound next (after m rep.events) rs

/-- Wrap each active source report in its dispatcher report in execution order. The frame for
each call is read from the memory left by the preceding source events. -/
def linkedRows (i : Fin d) (ports : Ports w) : Memory w → List (Report w) → List (Report w)
  | _, [] => []
  | m, r::rs => activeLinkedReport C i ports m r :: linkedRows i ports (after m r.events) rs

/-- Exact total charge of the linked data calls in an active source trace. -/
theorem linkedRows_cost (i : Fin d) (ports : Ports w) (pub : Fin (C i).params → Word w)
    (bound st : Word w) (m : Memory w) (rs : List (Report w)) (hv : ValidTrace C i ports pub bound
      st m rs) :
    RAMBuckets.cost Report.probes (linkedRows C i ports m rs) =
      RAMBuckets.cost Report.probes rs + rs.length*((C i).params+2) := by
  induction rs generalizing m st with
  | nil => simp [linkedRows, RAMBuckets.cost]
  | cons r rs ih =>
    obtain ⟨_,_,next,hn,hv'⟩ := hv
    rw [linkedRows, RAMBuckets.cost, RAMBuckets.cost, (activeLinkedReport_effect C i ports m r
      hn).2.2.2,
      ih next _ hv', List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Exact cost through the handoff, excluding the controller call that
prepared this row. A zero-length scan still executes its closing call. -/
theorem linkedPass_cost (i : Fin d) (ports : Ports w) (pub : Fin (C i).params → Word w)
    (bound st : Word w) (m : Memory w) (rs : List (Report w)) (hv : ValidTrace C i ports pub bound
      st m rs) :
    RAMBuckets.cost Report.probes
      (linkedRows C i ports m rs ++ [closedLinkedReport C i ports (after m (eventLog rs))]) =
      RAMBuckets.cost Report.probes rs + rs.length*((C i).params+2) + ((C i).params+4) := by
  rw [RAMBuckets.cost_append, linkedRows_cost C i ports pub bound st m rs hv, RAMBuckets.cost,
    (closedLinkedReport_effect C i ports _).2.2.2]
  change _ + ((1 + ((C i).params+3))+0) = _
  omega

/-- Execute a verified source pass inside the finite dispatcher, consume its
closing call, and resume any remaining level schedule at controller tag zero.
The frame is loaded once per call, independently of the source's private work. -/
theorem worker_segment (i : Fin d) (ports : Ports w) (pub : Fin (C i).params → Word w)
    (bound st : Word w) (m : Memory w) (bits : List (List Bool)) (rs : List (Report w))
    (f cap : ℕ) (hf : 0 < f) (fits : d + 1 ≤ 2 ^ w)
    (hcap : f + 3 + 4 * ((C i).params + 1) + 2 * (d + 1) + 5 ≤ cap)
    (hr : runSegment ((C i).table.instantiate w pub).program f (some st) m bits = some rs)
    (hv : ValidTrace C i ports pub bound st m rs) (tail : List (List Bool)) :
    let D := (machine C controller ports).program
    let finalMem := after m (eventLog rs)
    runSegment D cap (some st) m (bits ++ [] :: tail) =
      (runSegment D cap (some 0) (writeMemory finalMem ports.tag 0) tail).map
        (fun more ↦ linkedRows C i ports m rs ++ closedLinkedReport C i ports finalMem ::
          more) := by
  dsimp only
  induction bits generalizing st m rs with
  | nil =>
    obtain rfl : rs = [] := (Option.some.inj hr).symm
    obtain ⟨⟨htag, hbound, _⟩, hle⟩ := hv
    have hstop := worker_stop C controller ports i st m htag fits (hbound ▸ hle) (cap := cap)
      (by omega)
    have hclosed := closedLinkedReport_effect C i ports m
    change runSegment _ _ _ _ ([] :: tail) = _
    rw [runSegment, hstop]
    change (runSegment _ _ (closedLinkedReport C i ports m).result (after m
      (closedLinkedReport C i ports m).events)
      tail).map _ = _
    rw [hclosed.1,hclosed.2.1]
    rfl
  | cons bs rest ih =>
    rw [runSegment] at hr
    let S := ((C i).table.instantiate w pub).program
    cases hs : execute S f (S.start st) m bs with
    | none => rw [hs] at hr; contradiction
    | some rep =>
      rw [hs] at hr
      obtain ⟨reps,hr',rfl⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨⟨htag, hbound, hpub⟩,hlt,next,hn,hv'⟩ := hv
      have hsource : let P := ((C i).table.instantiate w (parameters ports.activeFrame m)).program
          execute P f (P.start st) m bs = some rep := by rw [hpub]; exact hs
      have hcall := worker_active C controller ports i st m bs htag fits (hbound ▸ hlt)
        hcap rep hsource
      have hlinked := activeLinkedReport_effect C i ports m rep hn
      rw [List.cons_append, runSegment, hcall]
      change (runSegment _ _ (activeLinkedReport C i ports m rep).result
        (after m (activeLinkedReport C i ports m rep).events) _).map _ = _
      rw [hlinked.1, hlinked.2.1, ih next (after m rep.events) reps (hn ▸ hr') hv']
      simp only [linkedRows, List.cons_append, Option.map_map, Function.comp_def, eventLog,
        List.flatMap_cons, after, List.foldl_append]
      rfl

end CompressorRecords.Schedule

end VPVNP
end Computability
end OAI
