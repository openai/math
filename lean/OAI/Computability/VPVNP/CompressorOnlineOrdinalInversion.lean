import OAI.Computability.VPVNP.CompressorOnlineWorkerSegment
import OAI.Computability.VPVNP.CompressorRecordsOrdinalRun

/-! # Recovering exactly the scheduled number of data-worker calls

The ordinal invariant determines when the guarded pass can close. Every
accepting online execution therefore runs the required number of source calls,
including when that number is zero. Its final data memory satisfies the last
ordinal invariant and preserves the descriptor control cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online

open BurstRAM OrdinalRun

variable {d initial phases w : ℕ} {C : Catalog d} (plan : Config C initial phases)
local notation "q₀" => initial+phases

private theorem exact_length {Q : Type*} (P : BurstRAM.Program w Q) (f : ℕ) (ports : Ports w) (i : Fin d)
    (pub : Fin (C i).params → Word w) (bound : Word w) (cursor : ℕ → Word w) (N : ℕ) (I : ℕ → Memory w → Prop)
    (active : ∀ j < N, cursor j < bound) (closed : bound ≤ cursor N)
    (advance : ∀ j < N, ∀ mem, I j mem → ∀ bits rep, execute P f (P.start (cursor j)) mem bits = some rep →
      rep.result = some (cursor (j+1)) ∧ I (j+1) (after mem rep.events))
    (j : ℕ) (hj : j ≤ N) (m : Memory w) (hinv : I j m) (bits : List (List Bool)) (rs : List (Report w))
    (run : runSegment P f (some (cursor j)) m bits = some rs) (valid : ValidTrace C i ports pub bound (cursor j) m rs) :
    j+bits.length = N := by
  induction bits generalizing j m rs with
  | nil =>
    change some [] = some rs at run
    cases Option.some.inj run
    obtain ⟨_,stopped⟩ := valid
    have : ¬ j<N := fun h => (Nat.not_lt.mpr stopped) (active j h)
    simp; omega
  | cons b bs ih =>
    cases hs : execute P f (P.start (cursor j)) m b with
    | none => simp [runSegment,hs] at run
    | some rep =>
      simp only [runSegment,hs,Option.map_eq_some_iff] at run
      obtain ⟨tail,rest,rfl⟩ := run
      obtain ⟨_,live,next,returned,hv⟩ := valid
      have hlt : j<N := lt_of_le_of_ne hj (by rintro rfl; exact (not_lt_of_ge closed) live)
      obtain ⟨eq,hnext⟩ := advance j hlt m hinv b rep hs
      rw [eq] at returned rest
      cases Option.some.inj returned
      have h := ih (j+1) hlt (after m rep.events) hnext tail rest hv
      simp only [List.length_cons]; omega

/-- The recovered source runs at its own cap, its call count is exactly
the selected ordinal interval, and its original data memory remains available
at the handoff to the calendar. -/
theorem recover_ordinal_worker (ports : Ports w) (i : Fin d) (pub : Fin (C i).params → Word w) (bound : Word w)
    (cap f N : ℕ) (cursor : ℕ → Word w) (I : ℕ → Memory w → Prop) (fits : Online.N d q₀ ≤ 2^w)
    (active : ∀ j < N, cursor j < bound) (closed : bound ≤ cursor N)
    (short : let P := ((C i).table.instantiate w pub).program
      ∀ j < N, ∀ mem, I j mem → ∀ bits rep, execute P cap (P.start (cursor j)) mem bits = some rep → rep.events.length < f)
    (advance : let P := ((C i).table.instantiate w pub).program
      ∀ j < N, ∀ mem, I j mem → ∀ bits rep, execute P f (P.start (cursor j)) mem bits = some rep →
        rep.result = some (cursor (j+1)) ∧ I (j+1) (after mem rep.events) ∧
          Preserved (C i).params ports mem (after mem rep.events))
    (m : Memory w) (bits : List (List Bool)) (out : List (Report w))
    (ready : Ready C i ports pub bound m) (initialInv : I 0 m)
    (run : runSegment (program plan ports) cap (some (cursor 0)) m bits = some out)
    (halt : endState (some (cursor 0)) out = none) :
    let P := ((C i).table.instantiate w pub).program
    ∃ before tail raw more,
      let finalMem := after m (eventLog raw)
      before.length = N ∧ bits = before ++ []::tail ∧
        out = workerRows C q₀ ports i m raw ++ stopReport C q₀ ports i finalMem :: more ∧
        runSegment P f (some (cursor 0)) m before = some raw ∧ ValidTrace C i ports pub bound (cursor 0) m raw ∧
        I N finalMem ∧ Preserved (C i).params ports m finalMem ∧
        runSegment (program plan ports) cap (some 0)
          (writeMemory finalMem ports.tag (LiveStageLink.tagWord w (calendarIndex d q₀))) tail = some more ∧
        endState (some 0) more = none := by
  intro P
  let inv (st : Word w) (mem : Memory w) := ∃ j ≤ N, st = cursor j ∧ I j mem
  have step : WorkerStep ports i pub bound cap f inv := by
    rintro st mem choice rep frame ⟨j,hj,rfl,good⟩ live source
    have hlt : j<N := lt_of_le_of_ne hj (by rintro rfl; exact (not_lt_of_ge closed) live)
    have hs := short j hlt mem good choice rep source
    obtain ⟨hnext,hgood,stable⟩ := advance j hlt mem good choice rep (execute_at_cap source hs)
    exact ⟨hs,cursor (j+1),hnext,ready_of_preserved C i ports frame stable, j+1,hlt,rfl,hgood⟩
  obtain ⟨before,tail,raw,more,hb,ho,rs,vt,remain,ended⟩ :=
    recover_worker_segment plan ports i pub bound cap f inv step fits (cursor 0) m bits out ready
      ⟨0,Nat.zero_le _,rfl,initialInv⟩ run halt
  have size := exact_length P f ports i pub bound cursor N I active closed
    (fun j hj mem h b rep hs => ⟨(advance j hj mem h b rep hs).1,(advance j hj mem h b rep hs).2.1⟩)
    0 (Nat.zero_le _) m initialInv before raw rs vt
  obtain ⟨_,good,stable⟩ := OrdinalRun.validTrace C i ports P f pub bound cursor N I active closed advance
    0 before m raw size initialInv ready rs
  exact ⟨before,tail,raw,more,by simpa using size,hb,ho,rs,vt,good,stable,remain,ended⟩

end CompressorRecords.Schedule.Online

end VPVNP
end Computability
end OAI
