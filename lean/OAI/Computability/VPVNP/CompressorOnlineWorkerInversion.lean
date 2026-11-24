import OAI.Computability.VPVNP.CompressorRecordsOnline
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-! # Recovering a scheduled worker call on its actual choice stream

A successful active call executes the source pass on precisely the same
choice bits. Its report includes the observed frame reads, active guard and
stage link. The closing call has a unique empty choice string and transfers
back to the calendar. These statements allow arbitrary instruction caps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- The trace itself determines the number of instructions required for
a successful call, including the final return instruction. -/
theorem Guessed.at_cap {P : Program w C} {f : ℕ} {c : C} {es : List (Event w)} {out : Option (Word w)}
    (h : Guessed P f c es out) {cap : ℕ} (hl : es.length < cap) : Guessed P cap c es out := by
  induction h generalizing cap with
  | done hs =>
    cases cap with | zero => simp at hl | succ _ => exact .done hs
  | step hs _ ih =>
    cases cap with | zero => simp at hl | succ _ => exact .step hs (ih (by simpa using hl))
  | branch hs _ ih =>
    cases cap with | zero => simp at hl | succ _ => exact .branch hs (ih (by simpa using hl))
  | read hs _ ih =>
    cases cap with | zero => simp at hl | succ _ => exact .read hs (ih (by simpa using hl))
  | write hs _ ih =>
    cases cap with | zero => simp at hl | succ _ => exact .write hs (ih (by simpa using hl))

theorem execute_at_cap {P : Program w C} {f cap : ℕ} {c : C} {m : Memory w} {bits : List Bool} {out : Report w}
    (h : execute P f c m bits = some out) (hl : out.events.length < cap) : execute P cap c m bits = some out := by
  obtain ⟨run,valid,tape⟩ := execute_spec h
  exact execute_iff.mpr ⟨run.at_cap hl,valid,tape⟩

end BurstRAM

namespace CompressorRecords.Schedule.Online

open BurstRAM BurstRAM.PrivateRAM

variable {d initial phases w : ℕ} {C : Catalog d} (plan : Config C initial phases)
local notation "q₀" => initial+phases
local notation "D₀" => N d q₀

/-- Recover a successful source stage at an arbitrary padded cap. Padding
only reconstructs the existing report and retains the original choice bits. -/
theorem recover_slot (ports : Ports w) (s : Fin D₀) (state : Word w) (m : Memory w) (bits : List Bool)
    (htag : m ports.tag.val = LiveStageLink.tagWord w s) (fits : D₀ ≤ 2^w) {cap : ℕ} {out : Report w}
    (physical : execute (program plan ports) cap ((program plan ports).start state) m bits = some out)
    (pad : ℕ) :
    let slot := slots plan s
    let P := (slot.table.instantiate w (ports.data ∘ slot.publicIndex)).program
    ∃ source, execute P (cap+pad) (P.start state) m bits = some source ∧ out = linked ports s source := by
  intro slot P
  have extra := execute_extend physical (pad+(LiveStageLink.dispatchEvents ports.tag s).length)
  rw [← Nat.add_assoc] at extra
  have exec := LiveStageLink.execute_linked (tables plan) (handoff d q₀) ports.data ports.tag s fits
    state (cap+pad) m htag bits
  simp only [program] at extra
  dsimp only at exec
  rw [exec] at extra
  obtain ⟨exit,hit,eq⟩ := Option.map_eq_some_iff.mp extra
  obtain ⟨source,hsource,hout⟩ := Option.bind_eq_some_iff.mp hit
  refine ⟨source,?_,?_⟩
  · rw [tables, LiveStageLink.execute_widen_start] at hsource
    exact hsource
  · dsimp only [LiveStageLink.boundedExit] at hout
    split at hout
    · exact eq.symm.trans (congrArg (LiveStageLink.prependLog (LiveStageLink.dispatchEvents ports.tag s))
        (Option.some.inj hout).symm)
    · contradiction

theorem worker_active_iff (ports : Ports w) (i : Fin d) (state : Word w) (m : Memory w) (bits : List Bool)
    (htag : m ports.tag.val = LiveStageLink.tagWord w i.succ) (fits : D₀ ≤ 2^w)
    (guard : state < stopWord ports.activeFrame m) (cap : ℕ) (out : Report w) :
    execute (program plan ports) cap ((program plan ports).start state) m bits = some out ↔
      let S := ((C i).table.instantiate w (parameters ports.activeFrame m)).program
      out.events.length < cap ∧ ∃ rep, execute S cap (S.start state) m bits = some rep ∧
        out = linked ports (workerIndex q₀ i) (workerReport (C i) ports.activeFrame m rep) := by
  dsimp only
  constructor
  · intro physical
    obtain ⟨wrapped,hw,hout⟩ := recover_slot plan ports (workerIndex q₀ i) state m bits htag fits physical
      (3+4*((C i).params+1))
    have hslot : slots plan (workerIndex q₀ i) = (⟨worker (C i),fun _ => 0⟩ : Slot) := by
      simp only [slots,workerIndex,Fin.addCases_left,Fin.cons_succ]
      rfl
    rw [hslot] at hw
    change execute (((worker (C i)).table.instantiate w (fun _ => ports.activeFrame)).program) _
      (((worker (C i)).table.instantiate w (fun _ => ports.activeFrame)).program.start state) m bits = _ at hw
    rw [← Nat.add_assoc,execute_worker _ _ _ _ _ guard, Option.map_eq_some_iff] at hw
    obtain ⟨rep,run,heq⟩ := hw
    exact ⟨(execute_spec physical).1.length_lt, rep, run, heq.symm ▸ hout⟩
  · rintro ⟨hl,rep,hr,rfl⟩
    have call := worker_active plan ports i state m bits htag fits guard (le_refl _) rep hr
    exact execute_at_cap call hl

theorem worker_stop_iff (ports : Ports w) (i : Fin d) (state : Word w) (m : Memory w) (bits : List Bool)
    (htag : m ports.tag.val = LiveStageLink.tagWord w i.succ) (fits : D₀ ≤ 2^w)
    (guard : stopWord ports.activeFrame m ≤ state) (cap : ℕ) (out : Report w) :
    execute (program plan ports) cap ((program plan ports).start state) m bits = some out ↔
      out.events.length < cap ∧ bits=[] ∧ out=stopReport C q₀ ports i m := by
  have closed := worker_stop plan ports i state m htag fits guard (le_refl _)
  constructor
  · intro physical
    exact ⟨(execute_spec physical).1.length_lt,execute_empty_forces_anyFuel closed physical⟩
  · rintro ⟨hl,rfl,rfl⟩
    exact execute_at_cap closed hl

end CompressorRecords.Schedule.Online

end VPVNP
end Computability
end OAI
