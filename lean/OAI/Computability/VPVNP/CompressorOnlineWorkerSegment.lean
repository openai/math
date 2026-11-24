import OAI.Computability.VPVNP.CompressorOnlineWorkerInversion

/-! # Extracting the source pass from an arbitrary accepting online run

Each active worker call contributes its original choice tape and complete
source report. After its closing guard, the remaining native calls run from
the calendar with precisely the memory produced by the recovered pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online

open BurstRAM BurstRAM.PrivateRAM

variable {d initial phases w : ℕ} {C : Catalog d} (plan : Config C initial phases)
local notation "q₀" => initial+phases
local notation "D₀" => N d q₀

/-- The source pass preserves its public frame and returns a live cursor on
each active step. A caller may keep a stronger data-memory invariant and a
smaller source cap. No restriction is placed on the choice list. -/
def WorkerStep (ports : Ports w) (i : Fin d) (pub : Fin (C i).params → Word w) (bound : Word w)
    (cap f : ℕ) (inv : Word w → Memory w → Prop) : Prop :=
  let P := ((C i).table.instantiate w pub).program
  ∀ st m bits rep, Ready C i ports pub bound m → inv st m → st < bound →
    execute P cap (P.start st) m bits = some rep → rep.events.length < f ∧
      ∃ next, rep.result = some next ∧ Ready C i ports pub bound (after m rep.events) ∧
        inv next (after m rep.events)

/-- Recover one whole pass and the actual suffix, including the empty closing
call. A zero-length pass still consumes exactly that closing call. -/
theorem recover_worker_segment (ports : Ports w) (i : Fin d) (pub : Fin (C i).params → Word w)
    (bound : Word w) (cap f : ℕ) (inv : Word w → Memory w → Prop)
    (step : WorkerStep ports i pub bound cap f inv) (fits : D₀ ≤ 2^w)
    (st : Word w) (m : Memory w) (bits : List (List Bool)) (out : List (Report w))
    (ready : Ready C i ports pub bound m) (hInv : inv st m)
    (run : runSegment (program plan ports) cap (some st) m bits = some out) (halted : endState (some st) out = none) :
    let P := ((C i).table.instantiate w pub).program
    ∃ before tail raw more,
      let finalMem := after m (eventLog raw)
      bits = before ++ []::tail ∧ out = workerRows C q₀ ports i m raw ++ stopReport C q₀ ports i finalMem :: more ∧
        runSegment P f (some st) m before = some raw ∧ ValidTrace C i ports pub bound st m raw ∧
        runSegment (program plan ports) cap (some 0)
          (writeMemory finalMem ports.tag (LiveStageLink.tagWord w (calendarIndex d q₀))) tail = some more ∧
        endState (some 0) more = none := by
  intro P
  induction bits generalizing st m out with
  | nil =>
    change some [] = some out at run
    obtain rfl := Option.some.inj run
    contradiction
  | cons b bs ih =>
    cases first : execute (program plan ports) cap ((program plan ports).start st) m b with
    | none => simp [runSegment,first] at run
    | some actual =>
      simp only [runSegment,first,Option.map_eq_some_iff] at run
      obtain ⟨remaining,suffix,rfl⟩ := run
      change endState actual.result remaining = none at halted
      by_cases active : st < bound
      · have guard : st < stopWord ports.activeFrame m := ready.2.1.symm ▸ active
        obtain ⟨_,rep,source,linkedEq⟩ :=
          (worker_active_iff plan ports i st m b ready.1 fits guard cap actual).mp first
        rw [ready.2.2] at source
        obtain ⟨small,next,returned,valid',inv'⟩ := step st m b rep ready hInv active source
        have source' := execute_at_cap source small
        have eq : actual = activeReport C q₀ ports i m rep := linkedEq
        obtain ⟨res,mem,_⟩ := active_effect (initial := initial) (phases := phases) (C := C) ports i m rep returned
        rw [eq,res,mem] at suffix
        rw [eq,res] at halted
        obtain ⟨before,tail,raw,more,hb,hr,rs,vt,rest,stop⟩ :=
          ih next (after m rep.events) remaining valid' inv' suffix halted
        have finalEq : after m (eventLog (rep::raw)) = after (after m rep.events) (eventLog raw) := by
          simp only [eventLog,List.flatMap_cons,after,List.foldl_append]
        refine ⟨b::before,tail,rep::raw,more,congrArg (List.cons b) hb,?_,?_,?_,?_,stop⟩
        · simp only [workerRows,List.cons_append,finalEq,eq,hr]
        · change execute P f (P.start st) m b = some rep at source'
          simp only [runSegment,source',returned,rs,Option.map_some]
        · exact ⟨ready,active,next,returned,vt⟩
        · exact finalEq.symm ▸ rest
      · have closed : stopWord ports.activeFrame m ≤ st := ready.2.1.symm ▸ Nat.le_of_not_gt active
        obtain ⟨_,rfl,eq⟩ := (worker_stop_iff plan ports i st m b ready.1 fits closed cap actual).mp first
        obtain ⟨res,mem,_⟩ := stop_effect (initial := initial) (phases := phases) (C := C) ports i m
        rw [eq,res,mem] at suffix
        rw [eq,res] at halted
        exact ⟨[],bs,[],remaining,rfl,congrArg (· :: remaining) eq,rfl,⟨ready,Nat.le_of_not_gt active⟩,suffix,halted⟩

end CompressorRecords.Schedule.Online

end VPVNP
end Computability
end OAI
