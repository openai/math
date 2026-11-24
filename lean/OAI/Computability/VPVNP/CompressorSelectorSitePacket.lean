import OAI.Computability.VPVNP.PairSimulationWorkspaceSelectorPost
import OAI.Computability.VPVNP.PairSimulationWorkerRebase

/-! # Installing a native selector from its prepared source visit

The source worker carries the demand rows in the data suffix. The calendar
and launcher write their own fields below that suffix, so the worker can
use the actual prepared memory at this occurrence. Comparing the launch
with the evaluated recipe identifies all four public address parameters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace.SelectorSite

open BurstRAM Compression DescriptorSpace Schedule SourceTransport PairSimulation.LocalHistory
open SelectedTerms BlockPlanner
open scoped Fin.CommRing
attribute [local irreducible] BlockProgram.script

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
    {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
    {a g b n w : ℕ} {X : State a g} {p : StatePass R X b n}
    {o : PassOrigin B f hf p} {L : Layout} {pub : Fin 11 → Word w}
    {cap small ordinal total : ℕ} {m raw : Memory w}

local notation "script" => BlockProgram.script B
local notation "pt" => Workspace.ports (arity (Script.catalog (BlockProgram.script B))) (pub 2)
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex (Script.size (BlockProgram.script B))
  (Script.size (BlockProgram.script B)))
local notation "H" => levelStart L 0

/-- Physical worker information for one source packet, independent of the
live calendar memory at which the corresponding row will be installed. -/
structure SourceWorker (I : WorkerInput o w) (L : Layout) (pkt : SourceOnline.Packet script w) : Prop where
  code : (script).catalog pkt.stage.phase =
    TermWorker.motifPass (grid o).block (grid o).demandOrder.entries (grid o).e
  start : pkt.stage.start = 0
  stop : pkt.stage.stop.val = o.motifCount
  params : ∀ j, pkt.stage.params j = TermWorker.catalogWords (grid o).block
    (grid o).demandOrder.entries (grid o).supplyOrder.entries (script).catalog pkt.stage.phase I.addr code j
  fuel : pkt.stage.fuel = I.fuel
  width : SelectedTermWorker.fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w
  readable : ∀ i, levelStart L 0 ≤ (I.layout.source i).val
  writable : ∀ i, levelStart L 0 ≤ (I.layout.base i).val
  inputs : Agree (levelStart L 0 ≤ ·) I.memory pkt.input

/-- A prepared recipe suffices even at a selector for which there is no
accepting term. No completed choice run is needed to install its table. -/
noncomputable def ofPrepared (I : WorkerInput o w) (pkt : SourceOnline.Packet script w)
    (worker : SourceWorker I L pkt) (prepared : SourceOnline.Prepared script L (pub 2) ordinal total pkt)
    (recipeClock : ((script).plan.recipes pkt.stage.phase).2.code.length+1+2*Online.N (script).size (script).size+5 ≤ small)
    (dataClock : pkt.stage.fuel+3+4*(((script).catalog pkt.stage.phase).params+1)+2*Online.N (script).size (script).size+5 ≤ small)
    (clock : small ≤ cap) (hg : arity (script).catalog = L.shape.arity) (hb : (pub 2).val = L.base)
    (fit : H < 2^w) (count : ordinal < total) (room : total ≤ directoryRows L)
    (agree : Agree (H ≤ ·) pkt.input m) (htag : m (pt).tag.val = tag)
    (ord : (m (pt).ordinal.val).val = ordinal) (rows : (m (pt).rows.val).val = total)
    (stride : m ((pt).directory-1).val = (levelWords L : Word w)) : SelectorSite o L pub cap small m := by
  let j := pkt.stage.phase
  let physical := Directory.prepared (script).catalog pt (Online.rowInput (script).plan pt m j)
  have live : m (pt).ordinal.val < m (pt).rows.val := Fin.lt_def.mpr (ord.symm ▸ rows.symm ▸ count)
  have atRow : (m (pt).ordinal.val).val < directoryRows L := ord.symm ▸ count.trans_le room
  have preserve : Agree (H ≤ ·) m physical := OnlineFootprint.prepared script L (pub 2) hg hb fit m j atRow
  let mounted := I.rebase physical H worker.readable (fun x hx => (worker.inputs x hx).trans ((agree x hx).trans (preserve x hx)))
  obtain ⟨phase,launch⟩ := prepared m agree ord rows htag stride
  have evaluated := SourceOnline.evaluated_launch script (pub 2) L hg hb fit m j pkt.stage.fuel pkt.stage.choices atRow live
  have start : (script).operand (pub 2) m j ((script).visit j).initial = 0 :=
    evaluated.start.symm.trans (launch.start.trans worker.start)
  have stop : ((script).operand (pub 2) m j ((script).visit j).stop).val = o.motifCount :=
    (congrArg Fin.val (evaluated.stop.symm.trans launch.stop)).trans worker.stop
  have args (z) : (script).operand (pub 2) m j (((script).visit j).params z) =
      TermWorker.catalogWords (grid o).block (grid o).demandOrder.entries (grid o).supplyOrder.entries
        (script).catalog j mounted.addr worker.code z :=
    (congrFun evaluated.params z).symm.trans ((congrFun launch.params z).trans (worker.params z))
  have fuel : mounted.fuel+3+4*(((script).catalog j).params+1)+2*Online.N (script).size (script).size+5 ≤ small :=
    worker.fuel ▸ dataClock
  let boundary := mounted.selectorStart script L (pub 2) hg hb fit m j worker.code worker.width
    worker.readable worker.writable start stop args (ord.symm ▸ phase) atRow live
    (recipeClock.trans clock) (fuel.trans clock) rfl
  refine ⟨mounted,j,boundary,worker.writable,?_,?_⟩
  · rw [boundary.phase]
    exact recipeClock
  · rw [boundary.fuel,boundary.worker]
    exact fuel

/-- Extract the recipe and the two instruction bounds from an actual
singleton packet group, and mount its worker on the supplied live boundary. -/
noncomputable def ofPacket (I : WorkerInput o w) (pkt : SourceOnline.Packet script w)
    (worker : SourceWorker I L pkt) (group : SourceOnline.Group script L (pub 2) small ordinal total raw [pkt])
    (clock : small ≤ cap) (hg : arity (script).catalog = L.shape.arity) (hb : (pub 2).val = L.base)
    (fit : H < 2^w) (count : ordinal < total) (room : total ≤ directoryRows L)
    (agree : Agree (H ≤ ·) raw m) (htag : m (pt).tag.val = tag)
    (ord : (m (pt).ordinal.val).val = ordinal) (rows : (m (pt).rows.val).val = total)
    (stride : m ((pt).directory-1).val = (levelWords L : Word w)) : SelectorSite o L pub cap small m :=
  ofPrepared I pkt worker (by simpa using group.prepared 0)
    (group.checked pkt List.mem_cons_self).recipeClock (group.checked pkt List.mem_cons_self).dataClock
    clock hg hb fit count room (group.chronological.1.symm ▸ agree) htag ord rows stride

/-- The installation callback used to join the prefix, selector and tail of
the native pass. The source packet and its worker are fixed before the live
memory at which the prefix returns. -/
theorem install_from_packet (I : WorkerInput o w) (pkt : SourceOnline.Packet script w)
    (worker : SourceWorker I L pkt) (group : SourceOnline.Group script L (pub 2) small ordinal total raw [pkt])
    (clock : small ≤ cap) (hg : arity (script).catalog = L.shape.arity) (hb : (pub 2).val = L.base)
    (fit : H < 2^w) (count : ordinal < total) (room : total ≤ directoryRows L) :
    ∀ mid : Memory w, Agree (H ≤ ·) raw mid →
      Workspace.Installed (arity (script).catalog) (pub 2) mid → mid (pt).tag.val = tag →
      (mid (pt).ordinal.val).val = ordinal → (mid (pt).rows.val).val = total →
      mid ((pt).directory-1).val = (levelWords L : Word w) → Nonempty (SelectorSite o L pub cap small mid) :=
  fun _ agree _ htag ord rows stride =>
    ⟨ofPacket I pkt worker group clock hg hb fit count room agree htag ord rows stride⟩

end CompressorRecords.ScheduledTrace.SelectorSite

end VPVNP
end Computability
end OAI
