import OAI.Computability.VPVNP.CompressorOnlineBranchCut
import OAI.Computability.VPVNP.CompressorSourceBankFrame

/-! # Native branch cuts through the six-word online workspace frame

The framing prologue reads the installed pointer bank at each call. The
inverse below uses the actual choice stream up to the worker's closing
guard. Each successful active call preserves the pointer bank before the
next prologue reads it. The remaining calls can use arbitrary choice bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OnlineWorkspace

open BurstRAM Schedule BranchSegments

variable {w d initial phases : ℕ} {C : Catalog d} (plan : Online.Config C initial phases)
variable (pub : Fin 11 → Word w)
local notation "pt" => ports (C := C) pub
local notation "q" => initial+phases
local notation "inner" => Online.program plan pt
local notation "outer" => program plan pub
local notation "installed" => Workspace.Installed (arity C) (pub 2)

variable {cap : ℕ} {st : Option (Word w)} {m : Memory w}

/-- Lift a verified sequence of calls with its full report log. -/
def framedSegment (s : Segment inner cap st m) (bank : Banks (arity C) (pub 2) m s.logs) :
    Segment outer (cap+24) st m :=
  ⟨s.bits, framed (pub 2) m s.logs, run_framed plan pub cap st m s.bits s.logs s.run bank⟩

@[simp] theorem framedSegment_state (s : Segment inner cap st m) (bank : Banks (arity C) (pub 2) m s.logs) :
    (framedSegment plan pub s bank).state = s.state := (framed_effect _ _ _ _).1

@[simp] theorem framedSegment_memory (s : Segment inner cap st m) (bank : Banks (arity C) (pub 2) m s.logs) :
    (framedSegment plan pub s bank).memory = s.memory := (framed_effect _ _ _ st).2.1

/-- A successful source call from a reachable active cursor preserves the
six pointers that the next physical call reads. -/
def WorkerBanks (i : Fin d) (data : Fin (C i).params → Word w) (bound : Word w)
    (cap : ℕ) (inv : Word w → Memory w → Prop) : Prop :=
  let P := ((C i).table.instantiate w data).program
  ∀ cursor mem bs rep, inv cursor mem → cursor < bound → installed mem →
    execute P cap (P.start cursor) mem bs = some rep → installed (after mem rep.events)

/-- A successful prefix either ends inside the worker with every visited
call preserving the low addresses, or contains an entire valid term row. -/
theorem workerPrefixCases (i : Fin d) (data : Fin (C i).params → Word w)
    (bound : Word w) (cap f : ℕ) (inv : Word w → Memory w → Prop)
    (step : Online.WorkerStep pt i data bound cap f inv) (bankStep : WorkerBanks pub i data bound cap inv)
    (lo : ℕ) (keep : let P := ((C i).table.instantiate w data).program
      ∀ st mem bs rep, inv st mem → st < bound → execute P cap (P.start st) mem bs = some rep →
        ∀ x < lo, after mem rep.events x = mem x)
    (fits : Online.N d q ≤ 2^w) (cursor : Word w) (mem : Memory w)
    (ready : Schedule.Ready C i pt data bound mem) (hinv : inv cursor mem) (bank : installed mem)
    (bits : List (List Bool)) (logs : List (Report w))
    (run : runSegment outer (cap+24) (some cursor) mem bits = some logs) :
    let P := ((C i).table.instantiate w data).program
    (SourceBankFrame.Stable lo mem logs ∧ (endState (some cursor) logs).isSome) ∨
      ∃ dataBits tail raw, bits = dataBits ++ [] :: tail ∧
      runSegment P f (some cursor) mem dataBits = some raw ∧ ValidTrace C i pt data bound cursor mem raw := by
  intro P
  induction bits generalizing cursor mem logs with
  | nil =>
    change some [] = some logs at run
    obtain rfl := Option.some.inj run
    exact Or.inl ⟨trivial,rfl⟩
  | cons b bs ih =>
    rw [runSegment, execute_dispatch plan pub cursor mem b _ bank, Nat.add_sub_cancel] at run
    cases first : execute inner cap ((inner).start cursor) mem b with
    | none => simp [first] at run
    | some actual =>
      simp only [first,Option.map_some,Option.map_eq_some_iff] at run
      obtain ⟨rest,suffix,rfl⟩ := run
      obtain ⟨_,_,_,hm,hs⟩ := Workspace.report_effect (pub 2) mem actual
      rw [hm,hs] at suffix
      by_cases live : cursor < bound
      · have guard : cursor < stopWord (pt).activeFrame mem := ready.2.1.symm ▸ live
        obtain ⟨_,rep,source,he⟩ := (Online.worker_active_iff plan pt i cursor mem b ready.1 fits guard cap actual).mp first
        rw [ready.2.2] at source
        obtain ⟨small,next,returned,ready',inv'⟩ := step cursor mem b rep ready hinv live source
        have bank' := bankStep cursor mem b rep hinv live bank source
        have eqn : actual = Online.activeReport C q pt i mem rep := he
        obtain ⟨res,memory,_⟩ := Online.active_effect (initial := initial) (phases := phases) (C := C) pt i mem rep returned
        rw [eqn,res,memory] at suffix
        rcases ih next (after mem rep.events) ready' inv' bank' rest suffix with ⟨stable,cont⟩ | ⟨db,tail,raw,hbits,hraw,hvalid⟩
        · left
          rw [SourceBankFrame.Stable,endState,hm,hs,eqn,res,memory]
          exact ⟨⟨keep cursor mem b rep hinv live source,stable⟩,cont⟩
        · right
          refine ⟨b::db,tail,rep::raw,congrArg (List.cons b) hbits,?_,⟨ready,live,next,returned,hvalid⟩⟩
          have short : execute P f (P.start cursor) mem b = some rep := execute_at_cap source small
          simp only [runSegment,short,returned,hraw,Option.map_some]
      · have closed : stopWord (pt).activeFrame mem ≤ cursor := ready.2.1.symm ▸ Nat.le_of_not_gt live
        obtain ⟨_,rfl,_⟩ := (Online.worker_stop_iff plan pt i cursor mem b ready.1 fits closed cap actual).mp first
        exact Or.inr ⟨[],bs,[],rfl,rfl,ready,Nat.le_of_not_gt live⟩

variable {state : Word w} {I : Type*}

/-- Invert the three forced descriptor calls and the physical term worker on
an arbitrary accepting tape, up to the return to the level calendar. -/
def selectorCut (bounds : Online.Run.ControlBounds plan cap (w := w))
    (htag : m (pt).tag.val = LiveStageLink.tagWord w (Online.calendarIndex d q))
    (entry : Online.Run.RowStart plan pt cap m) (active : m (pt).ordinal.val < m (pt).rows.val)
    (prepBanks : Banks (arity C) (pub 2) m (Online.preparation plan pt m entry.phase))
    (preparedBank : installed (Directory.prepared C pt (Online.rowInput plan pt m entry.phase)))
    (workerBank : let x := Online.rowInput plan pt m entry.phase
      WorkerBanks pub entry.worker (Directory.words C pt entry.worker x) (Directory.bound C pt x) cap entry.invariant)
    (rows : I → Online.Run.Step d q w) (valid : ∀ i, (rows i).Valid plan pt cap m)
    (rowBanks : ∀ i, Banks (arity C) (pub 2) m (Online.rowLog plan pt m (rows i).phase (rows i).row))
    (decode : ∀ s : Online.Run.Step d q w, s.Valid plan pt cap m → s.phase = entry.phase →
      s.row.worker = entry.worker → s.row.fuel = entry.fuel → ∃ i, s.row.choices = (rows i).row.choices)
    (count : ℕ) (lengths : ∀ i, (rows i).row.choices.length = count)
    (unique : Function.Injective fun i => (rows i).row.choices) :
    Cut outer (cap+24) (some state) m I where
  part i := framedSegment plan pub (Online.Run.oneRow plan pt bounds htag (rows i) (valid i)) (rowBanks i)
  separate := (Online.Run.selectorCut plan pt bounds htag entry active rows valid decode count lengths unique
    (state := state)).separate
  cover bits logs run halt := by
    let x := Online.rowInput plan pt m entry.phase
    have prep : runSegment inner cap (some state) m (List.replicate 3 []) = some (Online.preparation plan pt m entry.phase) := by
      change runSegment _ _ _ _ ([] :: [] :: [] :: []) = _
      rw [Online.prepare_segment plan pt state m entry.phase htag bounds.tags active entry.calendarPhase entry.liveRow
        bounds.calendar entry.recipeCap bounds.launch []]
      simp [runSegment]
    have hp := run_framed plan pub cap (some state) m _ _ prep prepBanks
    obtain ⟨tail,reps,hbits,rfl,suffix⟩ := LiveProgram.split_empty_segment hp run halt
    obtain ⟨st,mem⟩ := Online.preparation_effect plan pt state m entry.phase
    obtain ⟨st',mem',_⟩ := framed_effect (pub 2) m (Online.preparation plan pt m entry.phase) (some state)
    rw [st',mem',st,mem] at suffix
    rw [endState_append,st',st] at halt
    have hw := workerPrefixCases plan pub entry.worker _ _ cap entry.fuel entry.invariant entry.dataStep workerBank
      0 (fun _ _ _ _ _ _ _ _ hx => (Nat.not_lt_zero _ hx).elim) bounds.tags _ _ entry.ready entry.initialInv
      preparedBank tail reps suffix
    obtain ⟨db,rest,raw,hb,hr,hv⟩ := hw.resolve_left (fun h => by simpa [halt] using h.2)
    let s : Online.Run.Step d q w := ⟨entry.phase, ⟨x, entry.worker, entry.fuel, db, raw⟩⟩
    have valid' : s.Valid plan pt cap m := ⟨entry.calendarPhase,active,rfl,
      ⟨by simp [s,x,Online.rowInput,writeMemory],entry.liveRow,entry.positiveFuel,hr,hv⟩,entry.recipeCap,entry.dataCap⟩
    obtain ⟨i, selected⟩ := decode s valid' rfl rfl rfl
    change db = (rows i).row.choices at selected
    exact ⟨i,rest,by simpa [Online.rowChoices,framedSegment,Online.Run.oneRow,hb,selected] using hbits⟩

end CompressorRecords.OnlineWorkspace

end VPVNP
end Computability
end OAI
