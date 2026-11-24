import OAI.Computability.VPVNP.CompressorScanProgress
import OAI.Computability.VPVNP.CompressorSourceSequence

/-!
# Using ordinal scan certificates in online source packets

An ordinal trace gives the scheduler's strict cursor test until the exclusive
stop and its closed test at the stop. Each source scan's access intervals are
included in the persistent level region. A single instruction cap can account
for every finite recipe and the frame overhead of every worker in the script.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM SourceTransport BlockPlanner DescriptorSpace Schedule
open scoped Fin.CommRing

namespace SourceOnline

variable {w : ℕ} {A : Script} {L : Layout} {cap first N : ℕ}
variable {p : SourceWalk.Packet (SourceOnline.Visit A w) w}
local notation "dispatch" => Online.N A.size A.size

/-- Convert an actual stage's raw ordinal and address evidence to the packet
checked by the online source sequence. The controller prefix is below the
level base, so the read and write inclusions are sufficient for replay. -/
theorem Checked.ofScanned {readable writable : ℕ → Prop}
    (positiveFuel : 0 < p.stage.fuel)
    (recipeClock : (A.plan.recipes p.stage.phase).2.code.length+1+2*dispatch+5 ≤ cap)
    (dataClock : p.stage.fuel+3+4*((A.catalog p.stage.phase).params+1)+2*dispatch+5 ≤ cap)
    (start : p.stage.start = (first : Word w)) (stop : p.stage.stop = (N : Word w))
    (fit : N < 2^w) (shape : StageFrame.Scanned first N p.reports)
    (rd : Reads readable (eventLog p.reports)) (wr : Writes writable (eventLog p.reports))
    (readAt : ∀ x, readable x → levelStart L 0 ≤ x) (writeAt : ∀ x, writable x → levelStart L 0 ≤ x) :
    Checked A L cap p := by
  refine ⟨positiveFuel,recipeClock,dataClock,?_,fun a v h ↦ readAt _ (rd a v h),
    fun a v h ↦ writeAt _ (wr a v h)⟩
  rw [stop,start]
  exact shape.toProgress fit

/-- The planner part is fixed with the program text. Only the bound for the
native worker calls may depend on the live word width. -/
def scanCap (A : Script) (maxFuel : ℕ) : ℕ :=
  max (Finset.univ.sup fun i ↦ (A.plan.recipes i).2.code.length+1+2*Online.N A.size A.size+5)
    (maxFuel+3+4*(Schedule.arity A.catalog+1)+2*Online.N A.size A.size+5)

/-- Uniform overhead for a fixed compiled script. -/
theorem scanCap_le (A : Script) (maxFuel : ℕ) : scanCap A maxFuel ≤ maxFuel+scanCap A 0 := by
  unfold scanCap
  omega

theorem scanCap_clocks (maxFuel : ℕ) (hp : p.stage.fuel ≤ maxFuel) (hc : scanCap A maxFuel ≤ cap) :
    (A.plan.recipes p.stage.phase).2.code.length+1+2*dispatch+5 ≤ cap ∧
    p.stage.fuel+3+4*((A.catalog p.stage.phase).params+1)+2*dispatch+5 ≤ cap := by
  have hr := Finset.le_sup (f := fun i ↦ (A.plan.recipes i).2.code.length+1+2*dispatch+5)
    (Finset.mem_univ p.stage.phase)
  have ar := params_le_arity A.catalog p.stage.phase
  exact ⟨hr.trans ((le_max_left _ _).trans hc),
    (show p.stage.fuel+3+4*((A.catalog p.stage.phase).params+1)+2*dispatch+5 ≤
      maxFuel+3+4*(Schedule.arity A.catalog+1)+2*dispatch+5 by omega).trans ((le_max_right _ _).trans hc)⟩

/-- Apply the native worker to its own packet inputs and tape. The result
is a checked packet and the worker's exact terminal memory invariant. -/
theorem Checked.ofScanRun (maxFuel : ℕ) (positive : 0 < p.stage.fuel)
    (fuel : p.stage.fuel ≤ maxFuel) (capFits : scanCap A maxFuel ≤ cap)
    (start : p.stage.start = (first : Word w)) (stop : p.stage.stop = (N : Word w))
    (tapes : p.stage.choices = List.replicate (N-first) []) (first_le : first ≤ N) (fit : N < 2^w)
    (I : ℕ → Memory w → Prop) (events : Memory w → Word w → List (Event w))
    (readable writable : ℕ → Prop)
    (readAt : ∀ x, readable x → levelStart L 0 ≤ x) (writeAt : ∀ x, writable x → levelStart L 0 ≤ x)
    (native : let M := ((A.catalog p.stage.phase).table.instantiate w p.stage.params).program
      ∀ j, first ≤ j → j < N → ∀ m, execute M p.stage.fuel (M.start (j : Word w)) m [] =
        some ⟨events m (j : Word w),some ((j : Word w)+1)⟩)
    (step : ∀ j, first ≤ j → j < N → ∀ m, I j m → I (j+1) (after m (events m (j : Word w))) ∧
      Reads readable (events m (j : Word w)) ∧ Writes writable (events m (j : Word w)))
    (initial : I first p.input) (run : p.stage.Runs p.input p.reports) :
    Checked A L cap p ∧ I N p.output := by
  obtain ⟨rc,dc⟩ := scanCap_clocks maxFuel fuel capFits
  rw [Visit.Runs,start,tapes] at run
  obtain ⟨shape,final,rd,wr⟩ := StageFrame.scan _ p.stage.fuel first N I events readable writable
    native step first_le p.input p.reports initial run
  exact ⟨Checked.ofScanned positive rc dc start stop fit shape rd wr readAt writeAt,final⟩

end SourceOnline
end CompressorRecords

end VPVNP
end Computability
end OAI
