import OAI.Computability.VPVNP.PairVertexAscendingPaths
import OAI.Computability.VPVNP.PairSimulationWorkerPhaseEquiv
import OAI.Computability.VPVNP.PairSimulationTerminalProgram
import OAI.Computability.VPVNP.PairTerminalVertexFrameLinked

/-!
# The completed physical vertex phase

The terminal controller's two writes preserve the vertex frame. Recover each
source call from its reduced physical clock and advance its natural ordinal.
This proves the read footprint on arbitrary completed physical traces.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM CompressorRecords SourceTransport TerminalLink
open LiveProgram (PairTable)
open scoped Fin.CommRing

variable {w n g cap base grammar : ℕ} {pub : Fin 11 → Word w} {D : IndexedSites n g}
    {workers : Stage → PairTable} {stage : Stage} {Frame : ℕ → Memory w → Prop}

private theorem classifyCall
    (H : ActiveCalls D (source workers stage pub) cap base grammar Frame)
    (close : Closes (source workers stage pub) cap n pub Frame) (room : (TerminalLink.header pub).val+32 ≤ 2^w)
    (checks : ∀ i m, Frame i.val m → ∀ (x : D.Choice i) r,
      execute (source workers stage pub) cap ((source workers stage pub).start (i.val : Word w)) m (D.encode i x) =
        some r → Reads (workerCell (TerminalLink.header pub)) r.events)
    {j : ℕ} (le : j ≤ n) {m : Memory w} (ready : Frame j m)
    {bs : List Bool} {raw : Report w}
    (run : execute (source workers stage pub) cap ((source workers stage pub).start (j : Word w)) m bs = some raw) :
    Reads (workerCell (TerminalLink.header pub)) raw.events ∧
      (∀ st, raw.result = some st → st = ((j+1 : ℕ) : Word w) ∧ j+1 ≤ n ∧ Frame (j+1) (after m raw.events)) := by
  rcases lt_or_eq_of_le le with lt | rfl
  · let i : Fin n := ⟨j,lt⟩
    obtain ⟨x,rfl⟩ := H.recover i m ready bs raw run
    obtain ⟨rep,call,next,mem⟩ := H.emit i m ready x
    obtain rfl := Option.some.inj (run.symm.trans call)
    refine ⟨checks i m ready x raw run, fun st returned => ?_⟩
    exact ⟨Option.some.inj (returned.symm.trans next),lt,mem ▸ H.preserve i m ready x⟩
  · rw [close m ready] at run
    split at run
    · obtain rfl := Option.some.inj run
      exact ⟨(closingReport_checks pub m room).1, fun _ h => nomatch h⟩
    · contradiction

/-- Classify all successful raw calls in a completed physical phase, with the
two controller writes applied before classifying the next call. -/
theorem ordinal_phase_reads
    (H : ActiveCalls D (source workers stage pub) cap base grammar Frame)
    (close : Closes (source workers stage pub) cap n pub Frame) (room : (TerminalLink.header pub).val+32 ≤ 2^w)
    (checks : ∀ i m, Frame i.val m → ∀ (x : D.Choice i) r,
      execute (source workers stage pub) cap ((source workers stage pub).start (i.val : Word w)) m (D.encode i x) =
        some r → Reads (workerCell (TerminalLink.header pub)) r.events)
    (post : ∀ j e m raw, Frame j (after m raw.events) →
      Frame j (after m (TerminalLink.report (TerminalLink.header pub) e raw).events))
    {e m bs ls final} (ph : Phase workers pub cap e m bs ls final)
    (hs : e.stage = stage) {j : ℕ} (state : e.state = (j : Word w)) (le : j ≤ n) (hm : Frame j m) :
    Reads (workerCell (TerminalLink.header pub)) (eventLog (ls.map Prod.snd)) := by
  have head {e : Entry w} {j : ℕ} {m b r} (hs : e.stage = stage) (state : e.state = (j : Word w))
      (le : j ≤ n) (hm : Frame j m)
      (called : execute (source workers e.stage pub) (rawFuel pub cap e)
        ((source workers e.stage pub).start e.state) m b = some r) :
      Reads (workerCell (TerminalLink.header pub)) r.events ∧
        (∀ st, r.result = some st → st = ((j+1 : ℕ) : Word w) ∧ j+1 ≤ n ∧ Frame (j+1) (after m r.events)) := by
    have full := execute_extend called (cap - rawFuel pub cap e)
    have hle : rawFuel pub cap e ≤ cap := Nat.sub_le ..
    rw [Nat.add_sub_of_le hle,hs,state] at full
    exact classifyCall H close room checks le hm full
  induction ph generalizing j with
  | last call _ _ =>
    simpa only [List.map_cons, List.map_nil, eventLog, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using (head hs state le hm call).1
  | @more e m b bs raw x ls final call _ returned _ ih =>
    obtain ⟨read,step⟩ := head hs state le hm call
    obtain ⟨rfl,next,frame⟩ := step x returned
    intro a v ha
    change Event.read a v ∈ raw.events ++ eventLog (ls.map Prod.snd) at ha
    rcases List.mem_append.mp ha with hh | ht
    · exact read a v hh
    · exact ih hs rfl next (post _ e m raw frame) a v ht

variable {geometry rootFields leaf shrink refresh : Segment}
local notation "segments₀" => segments geometry rootFields leaf shrink refresh

/-- The same stored final ordinal closes the vertex phase before and after
any number of physical histogram updates and terminal dispatches. -/
theorem linked_finalSites (reference : Memory w) (room : (TerminalLink.header pub).val + 32 ≤ 2^w)
    (below : base + grammar + g ≤ (TerminalLink.header pub).val)
    (sites : reference (TerminalLink.header pub + 7).val = (n : Word w))
    (m : Memory w) (frame : VertexFrame.Linked (TerminalLink.header pub) base grammar g reference n m) :
    m (TerminalSiteStart.headerWord pub + 7).val = (n : Word w) := by
  rw [headerWord_eq_header]
  exact (frame.header room below 7 (by decide) (by decide)).trans sites

/-- Construct the vertex worker's relocation proof from the per-ordinal source
facts, using the actual physical frame at every call on the reverse path. -/
theorem ordinalWorkerFrame
    (F : DescriptorSpace.Shape) (limit : ℕ) (ref src phy : Memory w)
    (H : ActiveCalls D (((template segments₀).instantiate w pub).program) cap base grammar
      (VertexFrame.Linked (TerminalLink.header pub) base grammar g ref))
    (close : Closes (((template segments₀).instantiate w pub).program) cap n pub
      (VertexFrame.Linked (TerminalLink.header pub) base grammar g ref))
    (room : (TerminalLink.header pub).val + 32 ≤ 2^w) (clock : 45 ≤ cap)
    (checks : ∀ i m, VertexFrame.Linked (TerminalLink.header pub) base grammar g ref i.val m →
      ∀ (x : D.Choice i) r,
        execute (((template segments₀).instantiate w pub).program) cap
          (((template segments₀).instantiate w pub).program.start (i.val : Word w)) m (D.encode i x) = some r →
        Reads (workerCell (TerminalLink.header pub)) r.events ∧ r.events.length + 1 ≤ cap-30)
    (hs : VertexFrame.Linked (TerminalLink.header pub) base grammar g ref 0 src)
    (hp : VertexFrame.Linked (TerminalLink.header pub) base grammar g ref 0 phy)
    (agree : Agree (workerCell (TerminalLink.header pub)) src phy) :
    WorkerFrame (TerminalProgram.workers F limit segments₀) pub cap (.resume Stage.vertices 0) src phy := by
  have safe (p : ActualPaths (((template segments₀).instantiate w pub).program) cap 0 src (fun _ => True)) :=
    ascending_report_checks H close room (by omega : 15 ≤ cap-30) checks src hs
      p.property.choose_spec.1 p.property.choose_spec.2.1
  refine ⟨by omega,agree,fun p => (safe p).1, fun p r hr => (safe p).2 r hr, ?_⟩
  intro q
  apply ordinal_phase_reads (stage := Stage.vertices) (D := D) H close room
    (fun i m h x r run => (checks i m h x r run).1)
    (fun _ e _ _ h => VertexFrame.Linked.after_report e h) q.property rfl (j := 0)
    (by simp [Entry.state]) (Nat.zero_le _) hp

section PhysicalSites

open NetworkKernel LocalHistory

variable {R : Type*} [CommRing R] {Label : Type} [Fintype Label] {κ : Label → R}
    {N : Network} (parsers : SiteParsers κ N) (order : Fin n ≃ N.Site)
    (labels : Fin g ≃ Label) (half : ∀ v, N.Half v)
    (F : DescriptorSpace.Shape) (limit : ℕ) (src phy : Memory w)
    (native : ActiveCalls (siteOrdinals parsers order labels half)
      (((template (segments geometry rootFields leaf shrink refresh)).instantiate w pub).program)
      cap base grammar Frame)
    (clock : 15 ≤ cap) (ready : Frame 0 src)
    (stored : ∀ m, Frame n m → m (TerminalSiteStart.headerWord pub + 7).val = (n : Word w))
    (transport : WorkerFrame (TerminalProgram.workers F limit (segments geometry rootFields leaf shrink refresh))
      pub cap (.resume Stage.vertices 0) src phy)

/-- Choose one final-site monomial at every vertex and obtain exactly the
completed physical vertex block on the fixed shared assignment. -/
noncomputable def sitePhysical (native : ActiveCalls (siteOrdinals parsers order labels half)
    (((template (segments geometry rootFields leaf shrink refresh)).instantiate w pub).program)
    cap base grammar Frame) (clock : 15 ≤ cap) (ready : Frame 0 src)
    (stored : ∀ m, Frame n m → m (TerminalSiteStart.headerWord pub + 7).val = (n : Word w))
    (transport : WorkerFrame (TerminalProgram.workers F limit segments₀) pub cap (.resume Stage.vertices 0) src phy) :
    (∀ v, (parsers.witnesses v (half v)).Choice) ≃ CompletedPhase (TerminalProgram.workers F limit segments₀)
      pub cap (.resume Stage.vertices 0) phy :=
  (sitePathsEquiv parsers order labels half native clock stored src ready).trans transport.sourceBlockEquiv

theorem physicalSite_calls (x : ∀ v, (parsers.witnesses v (half v)).Choice) :
    (sitePhysical parsers order labels half F limit src phy native clock ready stored transport x).val.choices =
      (List.ofFn fun j => (parsers.read (order j) (half (order j))).encode (x (order j))) ++ [[]] := rfl

/-- Exact terminal memory agreement on all worker addresses. In particular
each counter cell contains its old value plus the sum of the selected powers. -/
theorem physicalSite_memory (x : ∀ v, (parsers.witnesses v (half v)).Choice) :
    Agree (workerCell (TerminalLink.header pub)) ((siteOrdinals parsers order labels half).finalMemory
      base grammar src (fun j => x (order j)))
      (sitePhysical parsers order labels half F limit src phy native clock ready stored transport x).val.memory := by
  let p := sitePathsEquiv parsers order labels half native clock stored src ready x
  have same : Agree (workerCell (TerminalLink.header pub)) (after src (eventLog p.property.choose))
      (transport.sourceBlockEquiv p).val.memory := transport.sourceBlock_memory p
  obtain ⟨rs, _, run, _, mem⟩ := ascending_reports native (template_closes clock stored) src ready (fun j => x (order j))
  have hr := Option.some.inj (p.property.choose_spec.1.symm.trans run)
  rw [hr,mem] at same
  exact same

theorem physicalSite_histogram (x : ∀ v, (parsers.witnesses v (half v)).Choice) (l : Fin g)
    (cell : workerCell (TerminalLink.header pub) (base + grammar + l)) :
    (sitePhysical parsers order labels half F limit src phy native clock ready stored transport x).val.memory
      (base + grammar + l) = src (base + grammar + l) +
        ((∑ v, (parsers.witnesses v (half v)).exponents (x v) (labels l) : ℕ) : Word w) := by
  rw [← physicalSite_memory parsers order labels half F limit src phy native clock ready stored transport x _ cell,
    IndexedSites.finalMemory_at (siteOrdinals parsers order labels half) base grammar src (fun j => x (order j)) l]
  exact congrArg (fun k : ℕ => src (base + grammar + l) + (k : Word w))
    (order.sum_comp fun v => (parsers.witnesses v (half v)).exponents (x v) (labels l))

/-- When the accumulated count fits the word, reading its natural value gives
the integer sum of the occurrence exponents. -/
theorem physicalSite_histogram_val (x : ∀ v, (parsers.witnesses v (half v)).Choice) (l : Fin g)
    (cell : workerCell (TerminalLink.header pub) (base + grammar + l))
    (fit : (src (base + grammar + l)).val +
      ∑ v, (parsers.witnesses v (half v)).exponents (x v) (labels l) < 2 ^ w) :
    ((sitePhysical parsers order labels half F limit src phy native clock ready stored transport x).val.memory
      (base + grammar + l)).val = (src (base + grammar + l)).val +
        ∑ v, (parsers.witnesses v (half v)).exponents (x v) (labels l) := by
  have part : (∑ v, (parsers.witnesses v (half v)).exponents (x v) (labels l)) < 2 ^ w := by omega
  rw [physicalSite_histogram parsers order labels half F limit src phy native clock ready stored transport x l cell,
    Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt part, Nat.mod_eq_of_lt fit]

end PhysicalSites

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
