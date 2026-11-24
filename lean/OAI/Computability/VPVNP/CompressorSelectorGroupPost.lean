import OAI.Computability.VPVNP.CompressorDeterministicGroup

/-! # Identifying the selected physical branch with its source packet

The packet's source run and recipe at the current ordinal produce one valid
online row. Its calendar, recipe, launcher, worker and closing calls consume
the selected branch's exact tapes. Determinism at the private clock identifies
the two logs and hence their post-memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM BlockPlanner DescriptorSpace Schedule SourceTransport
open scoped Fin.CommRing

variable {w cap small ordinal total : ℕ} {A : Script} {L : Layout} {I : Type*}
variable {pub : Fin 11 → Word w} {m raw : Memory w} {state : Word w}

local notation "pt" => Workspace.ports (arity A.catalog) (pub 2)
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex A.size A.size)

/-- The memory and private communication charge of this particular choice
follow from its real source packet. -/
theorem selectorGroupPost (out : SelectorInterval A pub cap small (some state) m I) (i : I)
    (pkt : SourceOnline.Packet A w) (group : SourceOnline.Group A L (pub 2) small ordinal total raw [pkt])
    (bits : (out.cut.part i).bits = [] :: [] :: [] :: (pkt.stage.choices ++ [[]]))
    (bounds : Online.Run.ControlBounds A.plan small (w := w))
    (arityEq : arity A.catalog = L.shape.arity) (baseEq : (pub 2).val = L.base)
    (fit : levelStart L 0 < 2^w) (count : ordinal < total) (room : total ≤ directoryRows L)
    (agree : Agree (levelStart L 0 ≤ ·) raw m) (bank : Workspace.Installed (arity A.catalog) (pub 2) m)
    (htag : m (pt).tag.val = tag) (ord : (m (pt).ordinal.val).val = ordinal)
    (rows : (m (pt).rows.val).val = total) (stride : m ((pt).directory-1).val = (levelWords L : Word w)) :
    let mem := (out.cut.part i).memory
    Agree (levelStart L 0 ≤ ·) pkt.output mem ∧
      Workspace.Installed (arity A.catalog) (pub 2) mem ∧ mem (pt).tag.val = tag ∧
      (mem (pt).ordinal.val).val = ordinal+1 ∧ (mem (pt).rows.val).val = total ∧
      mem ((pt).directory-1).val = (levelWords L : Word w) ∧
      RAMBuckets.cost Report.probes (out.source i).logs ≤ groupCost A [pkt] := by
  intro mem
  obtain ⟨input,run,_⟩ := group.chronological
  have matchData : Agree (levelStart L 0 ≤ ·) pkt.input m := input.symm ▸ agree
  have prepared : SourceOnline.Prepared A L (pub 2) ordinal total pkt := by simpa using group.prepared 0
  obtain ⟨phase,launch⟩ := prepared m matchData ord rows htag stride
  have checked := group.checked pkt List.mem_cons_self
  have active : m (pt).ordinal.val < m (pt).rows.val := Fin.lt_def.mpr (ord.symm ▸ rows.symm ▸ count)
  have space : (m (pt).ordinal.val).val < directoryRows L := ord.symm ▸ count.trans_le room
  obtain ⟨valid,ag,position,bound⟩ := SourceOnline.packet A L (pub 2) arityEq baseEq fit pkt.stage pkt.input m
    pkt.reports small matchData (ord.symm ▸ phase) active space launch checked.positiveFuel
    checked.recipeClock checked.dataClock run checked.progress checked.read checked.write
  let step : Online.Run.Step A.size A.size w := ⟨pkt.stage.phase,pkt.stage.row pt m pkt.reports⟩
  let actual := Online.Run.oneRow A.plan pt (state := state) bounds htag step valid
  have sameBits : (out.cut.part i).bits = actual.bits := bits
  have physical := (out.source i).run
  rw [sameBits] at physical
  have sameLogs : (out.source i).logs = actual.logs := Option.some.inj (physical.symm.trans actual.run)
  have sameMemory : mem = Online.post A.catalog A.size pt step.row := by
    rw [show mem = after m (eventLog (out.source i).logs) from (out.source i).memory.symm,sameLogs]
    exact Online.Run.oneRow_memory A.plan pt (state := state) bounds htag step valid
  have installed := (out.frame.parts i).installed bank (out.cut.part i).logs.length
  rw [List.take_length] at installed
  have pitch := SourceOnline.pitch_packet A L (pub 2) arityEq baseEq fit pkt.stage m pkt.reports space checked.write
  refine ⟨sameMemory.symm ▸ ag,installed,?_,sameMemory.symm ▸ position.trans (congrArg (·+1) ord),
    sameMemory.symm ▸ (congrArg Fin.val bound).trans rows,sameMemory.symm ▸ pitch.trans stride,?_⟩
  · rw [sameMemory]
    simp [Online.post,writeMemory]
  · have cost := Online.Run.interval_cost_bound A.plan pt [step] m (cap := small) ⟨valid,trivial⟩
    rw [sameLogs]
    change RAMBuckets.cost Report.probes (Online.rowLog A.plan pt m step.phase step.row) ≤ _
    simpa only [Online.Run.intervalLog, List.append_nil, Online.Run.sourceCost_eq_flatMap,
      List.flatMap_cons, List.flatMap_nil, groupCost, List.length_cons, List.length_nil, step, SourceOnline.Visit.row] using cost

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
