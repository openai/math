import OAI.Computability.VPVNP.CompressorOnlineRowInverse

/-! # Completeness of the physical online descriptor trace

At an active ordinal the fixed calendar must emit the current row, and every
successful data call is governed by its worker's invariant. Each extracted
row consumes the three control calls and its closing call. Induction on the
remaining physical calls therefore recovers all rows from an arbitrary
accepting path, including schedules with no active rows. The equivalence
keeps the path's original list of branch tapes and hence its multiplicity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online.Run

open BurstRAM

variable {d initial phases w : ℕ} {C : Catalog d} (plan : Config C initial phases) (ports : Ports w)
local notation "q₀" => initial+phases
local notation "D₀" => N d q₀

/-- At each reachable calendar boundary, supply the physical row's frame
and single-call invariant. On completion of that source row the next memory
again satisfies the boundary invariant. -/
structure RowInvariant (cap : ℕ) (I : Memory w → Prop) where
  /-- Recover the phase, worker, and execution bounds for the next live row from the memory
  invariant. -/
  next : ∀ m, I m → m ports.ordinal.val < m ports.rows.val → RowStart plan ports cap m
  advance : ∀ m (h : I m) (live : m ports.ordinal.val < m ports.rows.val) (s : Step d q₀ w),
    s.Valid plan ports cap m → s.phase = (next m h live).phase → s.row.worker = (next m h live).worker →
    s.row.fuel = (next m h live).fuel → I (post C q₀ ports s.row)

/-- Recover every chronological source row and its exact native reports.
Induction on the supplied stream length does not require a bound on the
number of selector choices available to a worker. -/
theorem recover_trace {cap : ℕ} {I : Memory w → Prop} (inv : RowInvariant plan ports cap I)
    (fits : D₀ ≤ 2^w) (calCap : 30+2*q₀+2*D₀+5 ≤ cap) (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap)
    (bits : List (List Bool)) (m : Memory w) (state : Word w) (hm : I m)
    (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀)) (logs : List (Report w))
    (run : runSegment (program plan ports) cap (some state) m bits = some logs) (halt : endState (some state) logs = none) :
    ∃ stages, Valid plan ports cap m stages ∧ choices stages = bits ∧ reports plan ports m stages = logs ∧
      I (finalMemory (C := C) ports m stages) := by
  induction bits using (measure List.length).wf.induction generalizing m state logs with
  | h bits ih =>
    by_cases live : m ports.ordinal.val < m ports.rows.val
    · let entry := inv.next m hm live
      obtain ⟨s,tail,more,valid,hp,hw,hf,hbits,hlogs,rs,hend⟩ := recover_row plan ports entry htag fits live
        calCap launchCap run halt
      have shorter : (measure List.length).rel tail bits := by
        change tail.length < bits.length
        rw [hbits,List.length_append]
        simp [rowChoices]
      have nextInv := inv.advance m hm live s valid hp hw hf
      have nextTag : post C q₀ ports s.row ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀) := by
        simp [post,writeMemory]
      obtain ⟨rest,hv,hb,hl,hI⟩ := ih tail shorter _ 0 nextInv nextTag more rs hend
      refine ⟨s::rest,⟨valid,hv⟩,?_,?_,hI⟩
      · rw [hbits,← hb]; simp only [choices, List.flatMap_cons, List.append_assoc]
      · rw [hlogs,← hl]; rfl
    · have hs := le_of_not_gt live
      obtain ⟨hb,hl⟩ := recover_terminal plan ports htag fits hs (by omega) run halt
      exact ⟨[],hs,hb.symm,hl.symm,hm⟩

/-- A tape list and its resource predicate can be checked on the actual
chronological rows. Different proofs of row invariants carry no path weight. -/
abbrev RowTapes (cap : ℕ) (m : Memory w) (allow : List (Report w) → Prop) :=
  {bs : List (List Bool) // ∃ stages : List (Step d q₀ w), Valid plan ports cap m stages ∧
    choices stages = bs ∧ allow (reports plan ports m stages)}

/-- Bijection between accepting online program paths and valid row tapes satisfying the same
report filter. -/
def acceptedEquiv {cap : ℕ} {I : Memory w → Prop} (inv : RowInvariant plan ports cap I)
    (fits : D₀ ≤ 2^w) (calCap : 30+2*q₀+2*D₀+5 ≤ cap) (launchCap : 20+6*(arity C+1)+2*D₀+5 ≤ cap)
    (m : Memory w) (state : Word w) (hm : I m) (htag : m ports.tag.val = LiveStageLink.tagWord w (calendarIndex d q₀))
    (allow : List (Report w) → Prop) :
    LiveProgram.PathsFrom (program plan ports) cap (some state) m allow ≃ RowTapes plan ports cap m allow :=
  Equiv.subtypeEquivRight fun bs => by
    constructor
    · rintro ⟨logs,run,halt,allowed⟩
      obtain ⟨stages,hv,hb,hl,_⟩ := recover_trace plan ports inv fits calCap launchCap bs m state hm htag logs run halt
      exact ⟨stages,hv,hb,hl ▸ allowed⟩
    · rintro ⟨stages,hv,rfl,allowed⟩
      exact ⟨_, execute plan ports stages m state cap htag fits calCap launchCap hv,
        (effect plan ports stages m state hv).2,allowed⟩

end CompressorRecords.Schedule.Online.Run

end VPVNP
end Computability
end OAI
