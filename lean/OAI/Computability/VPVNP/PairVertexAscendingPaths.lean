import OAI.Computability.VPVNP.PairVertexSiteSegments
import OAI.Computability.VPVNP.PairSimulationHistoryBounds
import OAI.Computability.VPVNP.PairSimulationTerminalSplice

/-!
# Ascending calls of the final vertex worker

Each physical vertex ordinal consumes one occurrence tape and adds the occurrence's
exponents to the external histogram. A final empty call checks the exhausted ordinal.
This fold retains the actual reports and excludes incomplete or overlong call lists.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM LocalHistory NetworkKernel
open scoped Fin.CommRing

variable {w n g : ℕ} {C : Type*}

/-- Occurrence types, tapes and dense exponent coordinates in physical site order. -/
structure IndexedSites (n g : ℕ) where
  /-- The type of local computation choices at each final site ordinal. -/
  Choice : Fin n → Type
  /-- Encode a choice at one site as the part of the choice tape consumed by that vertex. -/
  encode : (i : Fin n) → Choice i → List Bool
  injective : ∀ i, Function.Injective (encode i)
  /-- Histogram exponents contributed by a site's choice, indexed by the common parameter
  labels. -/
  powers : (i : Fin n) → Choice i → Fin g → ℕ

/-- Native facts for one active ordinal on the fixed arc assignment. The frame
carries the descriptor words and the invariant needed for the next call. -/
structure ActiveCalls (D : IndexedSites n g) (P : BurstRAM.Program w C) (fuel base grammar : ℕ)
    (Frame : ℕ → Memory w → Prop) : Prop where
  emit : ∀ i m, Frame i.val m → ∀ x : D.Choice i, ∃ rep,
    execute P fuel (P.start (i.val : Word w)) m (D.encode i x) = some rep ∧
    rep.result = some ((i.val + 1 : ℕ) : Word w) ∧
    after m rep.events = Counters.addHistogram base grammar (D.powers i x) m
  recover : ∀ i m, Frame i.val m → ∀ bs rep,
    execute P fuel (P.start (i.val : Word w)) m bs = some rep → ∃ x, bs = D.encode i x
  preserve : ∀ i m, Frame i.val m → ∀ x, Frame (i.val + 1)
    (Counters.addHistogram base grammar (D.powers i x) m)

/-- Report produced by the equal-ordinal branch, including its header read. -/
def closingReport (pub : Fin 11 → Word w) (m : Memory w) : Report w :=
  ⟨TerminalSiteStart.guardTrace m (TerminalSiteStart.headerWord pub) ++ [.tick], none⟩

theorem closingReport_after (pub : Fin 11 → Word w) (m : Memory w) :
    after m (closingReport pub m).events = m := rfl

variable {D : IndexedSites n g} {P : BurstRAM.Program w C} {fuel base grammar : ℕ}
    {Frame : ℕ → Memory w → Prop} (H : ActiveCalls D P fuel base grammar Frame)
    {pub : Fin 11 → Word w}

/-- The native sentinel's unique tape and report at the specified call clock. -/
def Closes (P : BurstRAM.Program w C) (fuel n : ℕ) (pub : Fin 11 → Word w)
    (Frame : ℕ → Memory w → Prop) : Prop :=
  ∀ m, Frame n m → ∀ bs, execute P fuel (P.start (n : Word w)) m bs =
    if bs = [] then some (closingReport pub m) else none

variable {geometry rootFields leaf shrink refresh : Segment}
local notation "S" => segments geometry rootFields leaf shrink refresh

/-- The assembled worker's bootstrap supplies the closing call at every fuel ≥ 15. -/
theorem template_closes (room : 15 ≤ fuel)
    (stored : ∀ m, Frame n m → m (TerminalSiteStart.headerWord pub + 7).val = (n : Word w)) :
    Closes (((template S).instantiate w pub).program) fuel n pub Frame := by
  intro m hm bs
  let M := (template S).instantiate w pub
  let A := placement S
  let c := M.program.start (n : Word w)
  have eqn := TerminalSiteStart.equal_run
    (boot_startLinked A M (template_contains S pub)) m c rfl (stored m hm).symm (fuel - 15) bs
  dsimp only at eqn
  rw [Nat.sub_add_cancel room] at eqn
  rw [eqn]
  split <;> rfl

private def closedRun (P : BurstRAM.Program w C) (fuel ord : ℕ) (m : Memory w)
    (bs : List (List Bool)) (rs : List (Report w)) (last : Memory w) : Prop :=
  runSegment P fuel (some (ord : Word w)) m bs = some rs ∧
  endState (some (ord : Word w)) rs = none ∧ after m (eventLog rs) = last

private theorem closedRun_cons {i : ℕ} {m last : Memory w} {b : List Bool}
    {bs : List (List Bool)} {r : Report w} {rs : List (Report w)}
    (call : execute P fuel (P.start (i : Word w)) m b = some r)
    (next : r.result = some ((i + 1 : ℕ) : Word w))
    (tail : closedRun P fuel (i + 1) (after m r.events) bs rs last) :
    closedRun P fuel i m (b :: bs) (r :: rs) last := by
  obtain ⟨run,halt,mem⟩ := tail
  refine ⟨by simp only [runSegment, call, next, run, Option.map_some], by simpa only [endState, next] using halt, ?_⟩
  change after m (r.events ++ eventLog rs) = last
  exact (List.foldl_append ..).trans mem

include H in
private theorem emit_suffix (close : Closes P fuel n pub Frame)
    (ok : Report w → Prop)
    (checks : ∀ i m, Frame i.val m → ∀ (x : D.Choice i) r,
      execute P fuel (P.start (i.val : Word w)) m (D.encode i x) = some r → ok r)
    {k start : ℕ} (site : Fin k → Fin n)
    (aligned : ∀ j, (site j).val = start + j.val) (endOrd : start + k = n)
    (m : Memory w) (hm : Frame start m) (x : ∀ j, D.Choice (site j)) :
    let last := Counters.visit base grammar id (List.ofFn fun j => D.powers (site j) (x j)) m
    ∃ rs : List (Report w), rs.length = k ∧ (∀ r ∈ rs, ok r) ∧ closedRun P fuel start m
      ((List.ofFn fun j => D.encode (site j) (x j)) ++ [[]]) (rs ++ [closingReport pub last]) last := by
  induction k generalizing start m with
  | zero =>
    simp only [Nat.add_zero] at endOrd
    subst start
    have call := close m hm []
    simp only [ite_true] at call
    exact ⟨[],rfl,by simp,by simp [closedRun,runSegment,call,endState,eventLog,Counters.visit,closingReport_after]; rfl⟩
  | succ k ih =>
    have hz : (site 0).val = start := by simpa using aligned 0
    obtain ⟨rep,call,next,mem⟩ := H.emit (site 0) m (hz ▸ hm) (x 0)
    have accepted := checks (site 0) m (hz ▸ hm) (x 0) rep call
    rw [hz] at call next
    have step := H.preserve (site 0) m (hz ▸ hm) (x 0)
    rw [hz, ← mem] at step
    obtain ⟨rs,hlen,checked,run⟩ := ih (fun j => site j.succ)
      (fun j => by rw [aligned, Fin.val_succ]; omega) (by omega) (after m rep.events) step (fun j => x j.succ)
    refine ⟨rep :: rs,by simp [hlen],List.forall_mem_cons.mpr ⟨accepted,checked⟩,?_⟩
    simp only [List.ofFn_succ, List.cons_append, Counters.visit, List.foldl_cons, id_eq]
    rw [← mem]
    exact closedRun_cons call next run

include H in
private theorem recover_suffix (close : Closes P fuel n pub Frame)
    {k start : ℕ} (site : Fin k → Fin n)
    (aligned : ∀ j, (site j).val = start + j.val) (endOrd : start + k = n)
    (m : Memory w) (hm : Frame start m) {bs : List (List Bool)} {rs : List (Report w)}
    (run : runSegment P fuel (some (start : Word w)) m bs = some rs)
    (halt : endState (some (start : Word w)) rs = none) :
    ∃ x : ∀ j, D.Choice (site j), bs = (List.ofFn fun j => D.encode (site j) (x j)) ++ [[]] := by
  induction k generalizing start m bs rs with
  | zero =>
    simp only [Nat.add_zero] at endOrd
    subst start
    cases bs with
    | nil =>
      obtain rfl : rs = [] := (Option.some.inj run).symm
      contradiction
    | cons b bs =>
      rw [runSegment, close m hm] at run
      by_cases empty : b = []
      · subst b
        simp only [ite_true] at run
        cases bs with
        | nil => exact ⟨fun j => Fin.elim0 j, by simp⟩
        | cons c cs => contradiction
      · simp [empty] at run
  | succ k ih =>
    cases bs with
    | nil =>
      obtain rfl : rs = [] := (Option.some.inj run).symm
      contradiction
    | cons b bs =>
      cases call : execute P fuel (P.start (start : Word w)) m b with
      | none => simp only [runSegment,call,reduceCtorEq] at run
      | some rep =>
        rw [runSegment,call,Option.map_eq_some_iff] at run
        obtain ⟨rs,tail,rfl⟩ := run
        change endState rep.result rs = none at halt
        have hz : (site 0).val = start := by simpa using aligned 0
        obtain ⟨x₀,rfl⟩ := H.recover (site 0) m (hz ▸ hm) b rep (hz ▸ call)
        obtain ⟨out,exec,next,mem⟩ := H.emit (site 0) m (hz ▸ hm) x₀
        rw [hz] at exec next
        obtain rfl := Option.some.inj (exec.symm.trans call)
        have step := H.preserve (site 0) m (hz ▸ hm) x₀
        rw [hz, ← mem] at step
        rw [next] at tail halt
        obtain ⟨xs,hs⟩ := ih (fun j => site j.succ)
          (fun j => by rw [aligned, Fin.val_succ]; omega) (by omega) _ step tail halt
        refine ⟨Fin.cons x₀ xs,?_⟩
        simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.cons_append]
        exact congrArg (_ :: ·) hs

/-- All site tapes in order, followed by the mandatory exhausted call. -/
def IndexedSites.calls (D : IndexedSites n g) (x : ∀ j, D.Choice j) : List (List Bool) :=
  (List.ofFn fun j => D.encode j (x j)) ++ [[]]

/-- External memory after all active ordinals. -/
def IndexedSites.finalMemory (D : IndexedSites n g) (base grammar : ℕ)
    (m : Memory w) (x : ∀ j, D.Choice j) : Memory w :=
  Counters.visit base grammar id (List.ofFn fun j => D.powers j (x j)) m

theorem IndexedSites.finalMemory_at (D : IndexedSites n g) (base grammar : ℕ)
    (m : Memory w) (x : ∀ j, D.Choice j) (l : Fin g) :
    D.finalMemory base grammar m x (base + grammar + l) =
      m (base + grammar + l) + ((∑ j, D.powers j (x j) l : ℕ) : Word w) := by
  rw [IndexedSites.finalMemory, Counters.visit_at, List.map_ofFn, List.sum_ofFn]
  rfl

include H in
/-- The native report list has one active call per site and the exact final
header report. Its external effect is the sum of the selected exponent vectors. -/
theorem ascending_reports (close : Closes P fuel n pub Frame)
    (m : Memory w) (hm : Frame 0 m) (x : ∀ j, D.Choice j) :
    let last := D.finalMemory base grammar m x
    ∃ rs : List (Report w), rs.length = n ∧
      runSegment P fuel (some 0) m (D.calls x) = some (rs ++ [closingReport pub last]) ∧
      endState (some 0) (rs ++ [closingReport pub last]) = none ∧
      after m (eventLog (rs ++ [closingReport pub last])) = last := by
  obtain ⟨rs, len, _, run⟩ := emit_suffix H close (fun _ => True) (fun _ _ _ _ _ _ => trivial)
    id (fun _ => by simp) (Nat.zero_add n) m hm x
  exact ⟨rs, len, by simpa only [Nat.cast_zero, id_eq, closedRun, IndexedSites.finalMemory, IndexedSites.calls] using run⟩

include H in
/-- A bijection with the accepted native tapes at a fixed shared arc assignment. -/
noncomputable def ascendingEquiv (close : Closes P fuel n pub Frame)
    (m : Memory w) (hm : Frame 0 m) :
    (∀ j, D.Choice j) ≃ ActualPaths P fuel 0 m (fun _ => True) := by
  let path (x : ∀ j, D.Choice j) : ActualPaths P fuel 0 m (fun _ => True) :=
    ⟨D.calls x, by obtain ⟨rs, _, run, halt, _⟩ := ascending_reports H close m hm x
                   exact ⟨_, run, halt, trivial⟩⟩
  refine Equiv.ofBijective path ⟨?_,?_⟩
  · intro x y h
    have ht := List.ofFn_inj.mp (List.append_cancel_right (congrArg Subtype.val h))
    exact funext fun i => D.injective i (congrFun ht i)
  · intro q
    obtain ⟨rs,run,halt,_⟩ := q.property
    obtain ⟨x,hx⟩ := recover_suffix H close id (fun _ => by simp) (Nat.zero_add n) m hm
      (by simpa using run) (by simpa using halt)
    exact ⟨x,Subtype.ext hx.symm⟩

theorem ascendingEquiv_calls (close : Closes P fuel n pub Frame) (m : Memory w)
    (hm : Frame 0 m) (x : ∀ j, D.Choice j) :
    (ascendingEquiv H close m hm x).val = D.calls x := rfl

open CompressorRecords.SourceTransport TerminalLink

theorem headerWord_eq_header (pub : Fin 11 → Word w) :
    TerminalSiteStart.headerWord pub = TerminalLink.header pub := by
  dsimp only [TerminalSiteStart.headerWord, TerminalLink.header]
  exact congrArg (fun k : Word w => _ - k) (Nat.cast_add (R := Word w) 16 16).symm

/-- The only exhausted-call read is header field seven, and the clock charge is fifteen. -/
theorem closingReport_checks (pub : Fin 11 → Word w) (m : Memory w)
    (room : (TerminalLink.header pub).val + 32 ≤ 2 ^ w) :
    Reads (workerCell (TerminalLink.header pub)) (closingReport pub m).events ∧
      (closingReport pub m).events.length + 1 = 15 := by
  refine ⟨?_,rfl⟩
  intro a v ha
  simp only [closingReport, TerminalSiteStart.guardTrace, TerminalSiteStart.fieldTrace,
    List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil, Event.read.injEq,
    reduceCtorEq, and_false, false_or, or_false] at ha
  obtain ⟨rfl,_⟩ := ha
  rw [headerWord_eq_header]
  have offset (k : ℕ) (hk : k < 32) : (TerminalLink.header pub + (k : Word w)).val = (TerminalLink.header pub).val + k := by
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (show k < 2^w by omega),
      Nat.mod_eq_of_lt (by omega)]
  change (TerminalLink.header pub + 7).val ≠ (TerminalLink.header pub).val ∧ (TerminalLink.header pub + 7).val ≠ (TerminalLink.header pub + 31).val
  rw [show (TerminalLink.header pub + 7).val = _ from offset 7 (by decide),
    show (TerminalLink.header pub + 31).val = _ from offset 31 (by decide)]
  omega

include H in
/-- Reads and clock bounds on the encoded site calls hold on every closed native
source path, including its exhausted call. The report list is the computed one. -/
theorem ascending_report_checks (close : Closes P fuel n pub Frame) {clock : ℕ}
    (room : (TerminalLink.header pub).val + 32 ≤ 2 ^ w) (minClock : 15 ≤ clock)
    (checks : ∀ i m, Frame i.val m → ∀ (x : D.Choice i) r,
      execute P fuel (P.start (i.val : Word w)) m (D.encode i x) = some r →
        Reads (workerCell (TerminalLink.header pub)) r.events ∧ r.events.length + 1 ≤ clock)
    (m : Memory w) (hm : Frame 0 m) {bs rs}
    (run : runSegment P fuel (some 0) m bs = some rs) (halt : endState (some 0) rs = none) :
    Reads (workerCell (TerminalLink.header pub)) (eventLog rs) ∧ ∀ r ∈ rs, r.events.length + 1 ≤ clock := by
  obtain ⟨x,rfl⟩ := recover_suffix H close id (fun _ => by simp) (Nat.zero_add n) m hm
    (by simpa using run) (by simpa using halt)
  obtain ⟨active,_,safe,calls,_,_⟩ := emit_suffix H close
    (fun r => Reads (workerCell (TerminalLink.header pub)) r.events ∧ r.events.length + 1 ≤ clock) checks
    id (fun _ => by simp) (Nat.zero_add n) m hm x
  rw [Nat.cast_zero] at calls
  obtain rfl := Option.some.inj (run.symm.trans calls)
  have each : ∀ r ∈ active ++ [closingReport pub (D.finalMemory base grammar m x)],
      Reads (workerCell (TerminalLink.header pub)) r.events ∧ r.events.length + 1 ≤ clock := by
    intro r hr
    rcases List.mem_append.mp hr with ha | hc
    · exact safe r ha
    · obtain rfl := List.mem_singleton.mp hc
      have ⟨read,len⟩ := closingReport_checks pub (D.finalMemory base grammar m x) room
      exact ⟨read,len ▸ minClock⟩
  refine ⟨?_,fun r hr => (each r hr).2⟩
  intro a v hv
  obtain ⟨r,hr,hit⟩ := List.mem_flatMap.mp hv
  exact (each r hr).1 a v hit

section SiteParsers

variable {R : Type*} [CommRing R] {Label : Type} [Fintype Label] {κ : Label → R}
    {N : Network} (parsers : SiteParsers κ N) (order : Fin n ≃ N.Site)
    (labels : Fin g ≃ Label) (half : ∀ v, N.Half v)

/-- Index the actual monomial occurrences and their readers by the worker's ordinals. -/
def siteOrdinals : IndexedSites n g where
  Choice j := (parsers.witnesses (order j) (half (order j))).Choice
  encode j := (parsers.read (order j) (half (order j))).encode
  injective j _ _ eqn := (parsers.read (order j) _).completeEquiv.injective (Subtype.ext eqn)
  powers j x l := (parsers.witnesses (order j) (half (order j))).exponents x (labels l)

local notation "sites" => siteOrdinals parsers order labels half
local notation "worker" => Machine.program (Template.instantiate (template S) w pub)

variable (active : ActiveCalls (siteOrdinals parsers order labels half)
      (((template (segments geometry rootFields leaf shrink refresh)).instantiate w pub).program) fuel base grammar Frame)
    (room : 15 ≤ fuel)
    (stored : ∀ m, Frame n m → m (TerminalSiteStart.headerWord pub + 7).val = (n : Word w))

/-- Visit the monomial choices in physical ordinal order and close the actual vertex template. -/
noncomputable def sitePathsEquiv (active : ActiveCalls (sites) (worker) fuel base grammar Frame)
    (room : 15 ≤ fuel) (stored : ∀ m, Frame n m →
      m (TerminalSiteStart.headerWord pub + 7).val = (n : Word w)) (m : Memory w) (hm : Frame 0 m) :
    (∀ v, (parsers.witnesses v (half v)).Choice) ≃ ActualPaths (worker) fuel 0 m (fun _ => True) := by
  exact (Equiv.piCongrLeft (fun v => (parsers.witnesses v (half v)).Choice) order).symm.trans
    (ascendingEquiv active (template_closes room stored) m hm)

theorem sitePathsEquiv_calls (m : Memory w) (hm : Frame 0 m) (x : ∀ v, (parsers.witnesses v (half v)).Choice) :
    (sitePathsEquiv parsers order labels half active room stored m hm x).val =
      (List.ofFn fun j => (parsers.read (order j) (half (order j))).encode (x (order j))) ++ [[]] := rfl

include active room stored in
/-- Read back a selected histogram from the source worker's own event log. -/
theorem sitePaths_histogram (m : Memory w) (hm : Frame 0 m) (x : ∀ v, (parsers.witnesses v (half v)).Choice) :
    let path := sitePathsEquiv parsers order labels half active room stored m hm x
    ∃ rs, runSegment (worker) fuel (some 0) m path.val = some rs ∧
      (∀ l : Fin g, after m (eventLog rs) (base + grammar + l) = m (base + grammar + l) +
        ((∑ v, (parsers.witnesses v (half v)).exponents (x v) (labels l) : ℕ) : Word w)) ∧
      ∀ a, a < base + grammar ∨ base + grammar + g ≤ a → after m (eventLog rs) a = m a := by
  obtain ⟨rs,_,run,_,mem⟩ := ascending_reports active (template_closes room stored) m hm (fun j => x (order j))
  refine ⟨_,run,?_,?_⟩
  · intro l
    rw [mem, IndexedSites.finalMemory_at (sites) base grammar m (fun j => x (order j)) l]
    exact congrArg (fun e : ℕ => m (base + grammar + l) + (e : Word w))
      (order.sum_comp fun v => (parsers.witnesses v (half v)).exponents (x v) (labels l))
  · intro a ha
    rw [mem]
    exact Counters.visit_outside _ _ _ _ _ _ ha

end SiteParsers

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
