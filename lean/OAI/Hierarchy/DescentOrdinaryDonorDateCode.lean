import OAI.Hierarchy.DescentNamedMatchedDonor
import OAI.Hierarchy.DescentPublicMeterCalendar

namespace OAI
/-! # The public ordinary date with its true four-stage private update -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentPacking.PackedMatch.Local.Stage.Dated
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

/-- Starting at the original caller's floor, all later addresses follow from
the fixed matcher geometry, including its six published truth and rotation results. -/
def code {F : Type} [Field F] (d : DonorDate) (gadget : PoweredGadget F)
    (positive : 0<d.exponent) (payload seats board floor header w : ℕ) (input : Operands) (v : Measures) :
    DateCode w :=
  let a:=d.schedule payload seats board
  let base:=a.rotationEnd input.roster floor
  let printed:=d.afterMatcher payload seats input board floor w
  let meter:=d.counter payload base header
  .ordinary ((a.program gadget positive input v w floor).seq printed.program)
    (a.ticks gadget positive input v w floor+printed.ticks) (meter.program w) meter.ticks

/-- The exact equality used by the chronology when adding an ordinary row to its
public calendar. All data-dependent words are in the memories of the phases. -/
theorem code_of_issued {F : Type} [Field F] (d : DonorDate) (gadget : PoweredGadget F)
    (positive : 0<d.exponent) (payload seats board floor header w : ℕ) (input : Operands) (v : Measures)
    (prior installed venue gather : NativePhase w) (store : Procedure w) (storeTicks : ℕ)
    («matching» : prior.program=(d.schedule payload seats board).program gadget positive input v w floor)
    (clock : prior.ticks=(d.schedule payload seats board).ticks gadget positive input v w floor)
    (emits : (installed.seq venue).seq gather=d.afterMatcher payload seats input board floor w)
    (writes : store=(d.counter payload ((d.schedule payload seats board).rotationEnd input.roster floor) header).program w)
    (last : storeTicks=(d.counter payload ((d.schedule payload seats board).rotationEnd input.roster floor) header).ticks) :
    d.code gadget positive payload seats board floor header w input v=
      .ordinary (prior.seq ((installed.seq venue).seq gather)).program
        (prior.seq ((installed.seq venue).seq gather)).ticks store storeTicks := by
  rw [emits]
  simp only [code,NativePhase.seq,«matching»,clock,writes,last]

/-- Insert the public successor-field emitter after the donor gather and before the meter. -/
def codeAfter {F : Type} [Field F] (d : DonorDate) (gadget : PoweredGadget F)
    (positive : 0<d.exponent) (payload seats board floor header w : ℕ) (input : Operands) (v : Measures)
    (finish : Procedure w) (finishTicks : ℕ) : DateCode w :=
  let a:=d.schedule payload seats board
  let base:=a.rotationEnd input.roster floor
  let printed:=d.afterMatcher payload seats input board floor w
  let meter:=d.counter payload base header
  .ordinary (((a.program gadget positive input v w floor).seq printed.program).seq finish)
    ((a.ticks gadget positive input v w floor+printed.ticks)+finishTicks) (meter.program w) meter.ticks

theorem codeAfter_of_issued {F : Type} [Field F] (d : DonorDate) (gadget : PoweredGadget F)
    (positive : 0<d.exponent) (payload seats board floor header w : ℕ) (input : Operands) (v : Measures)
    (prior installed venue gather finish : NativePhase w) (extra store : Procedure w) (extraTicks storeTicks : ℕ)
    («matching» : prior.program=(d.schedule payload seats board).program gadget positive input v w floor)
    (clock : prior.ticks=(d.schedule payload seats board).ticks gadget positive input v w floor)
    (emits : (installed.seq venue).seq gather=d.afterMatcher payload seats input board floor w)
    (successor : finish.program=extra) (successorClock : finish.ticks=extraTicks)
    (writes : store=(d.counter payload ((d.schedule payload seats board).rotationEnd input.roster floor) header).program w)
    (last : storeTicks=(d.counter payload ((d.schedule payload seats board).rotationEnd input.roster floor) header).ticks) :
    d.codeAfter gadget positive payload seats board floor header w input v extra extraTicks=
      .ordinary ((prior.seq ((installed.seq venue).seq gather)).seq finish).program
        ((prior.seq ((installed.seq venue).seq gather)).seq finish).ticks store storeTicks := by
  rw [emits]
  simp only [codeAfter,NativePhase.seq,«matching»,clock,successor,successorClock,writes,last]


/-- The compact profile loader executes before any match field is read. The meter remains
after the successor geometry, at the same published addresses as in the ordinary executable. -/
def codeLoadedAfter {F : Type} [Field F] (d : DonorDate) (gadget : PoweredGadget F)
    (positive : 0<d.exponent) (payload seats board floor header w : ℕ) (input : Operands) (v : Measures)
    (load : Procedure w) (loadTicks : ℕ) (finish : Procedure w) (finishTicks : ℕ) : DateCode w :=
  let a:=d.schedule payload seats board
  let base:=a.rotationEnd input.roster floor
  let printed:=d.afterMatcher payload seats input board floor w
  let meter:=d.counter payload base header
  .ordinary (((load.seq (a.program gadget positive input v w floor)).seq printed.program).seq finish)
    (((loadTicks+a.ticks gadget positive input v w floor)+printed.ticks)+finishTicks) (meter.program w) meter.ticks

theorem codeLoadedAfter_of_issued {F : Type} [Field F] (d : DonorDate) (gadget : PoweredGadget F)
    (positive : 0<d.exponent) (payload seats board floor header w : ℕ) (input : Operands) (v : Measures)
    (loader prior installed venue gather finish : NativePhase w) (load extra store : Procedure w)
    (loadTicks extraTicks storeTicks : ℕ) (loadCode : loader.program=load) (loadClock : loader.ticks=loadTicks)
    («matching» : prior.program=(d.schedule payload seats board).program gadget positive input v w floor)
    (clock : prior.ticks=(d.schedule payload seats board).ticks gadget positive input v w floor)
    (emits : (installed.seq venue).seq gather=d.afterMatcher payload seats input board floor w)
    (successor : finish.program=extra) (successorClock : finish.ticks=extraTicks)
    (writes : store=(d.counter payload ((d.schedule payload seats board).rotationEnd input.roster floor) header).program w)
    (last : storeTicks=(d.counter payload ((d.schedule payload seats board).rotationEnd input.roster floor) header).ticks) :
    d.codeLoadedAfter gadget positive payload seats board floor header w input v load loadTicks extra extraTicks=
      .ordinary (((loader.seq prior).seq ((installed.seq venue).seq gather)).seq finish).program
        (((loader.seq prior).seq ((installed.seq venue).seq gather)).seq finish).ticks store storeTicks := by
  rw [emits]
  simp only [codeLoadedAfter,NativePhase.seq,«matching»,clock,loadCode,loadClock,successor,successorClock,writes,last]

end
end Hierarchy.DescentSixParty.Chronology.DonorDate


namespace Hierarchy.DescentSixParty.Chronology.MeterCalendar
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z₀ D₀ z D z' D' wire hist w header : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k 0 z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist} {path : Path start source}
variable (cal : MeterCalendar start header w path) {u : ℝ} {he : 0≤ε}
variable {T : StageInput W G u ε} {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist}

/-- A same-date public code equality extends the actual calendar by all five phases. -/
theorem scheduled_after (ticket : OrdinaryLink source he T c n target) (port : MeterPort source)
    (prepare install venue gather finish : NativePhase w) (date : ℕ→DateCode w) (prior : cal.Scheduled date)
    (current : date i=.ordinary ((prepare.seq ((install.seq venue).seq gather)).seq finish).program
      ((prepare.seq ((install.seq venue).seq gather)).seq finish).ticks (MeterPort.program ticket port header w)
      (MeterPort.ticks ticket port header)) :
    (cal.ordinary ticket port ((prepare.seq ((install.seq venue).seq gather)).seq finish)).Scheduled date :=
  ⟨prior,current⟩
end
end Hierarchy.DescentSixParty.Chronology.MeterCalendar

end OAI
