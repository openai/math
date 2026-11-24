import OAI.Computability.VPVNP.CompressorPassRunIntervals
import OAI.Computability.VPVNP.CompressorGroupBoundary
import OAI.Computability.VPVNP.CompressorSelectorGroupPost
import OAI.Computability.VPVNP.CompressorSelectorSitePacket
import OAI.Computability.VPVNP.CompressorDefaultSelection

/-! # Realizing one mathematical pass from its actual packet groups

The prefix group runs independently of the existence of an admitted term.
At its actual output memory, the selector site installs the finite motif
worker. Each term's singleton source packet then identifies the exact live
post-memory from which its own deterministic suffix executes. The selected
history and current graph are transported from the raw source into that
specific final memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression BlockPlanner DescriptorSpace Schedule SourceTransport PassTimeline PairSimulation.LocalHistory
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {R : Type*} [CommRing R]
  {f : B.Entry → R} {hf : B.IsSolution f} {w small cap total rate : ℕ} {pub : Fin 11 → Word w}
  {L : Layout} {resident : Resident B f hf w} {loc : Located S.steps}
  {a g b n : ℕ} {X : State a g} {p : StatePass R X b n} {o : PassOrigin B f hf p}
  {encode : p.step.Choice → List Bool} {past : List (SelectedLevel B f hf)} {raw m : Memory w}
local notation "A" => BlockProgram.script B
set_option quotPrecheck false in
local notation "pt" => Workspace.ports (arity (BlockProgram.script B).catalog) (pub 2)
set_option quotPrecheck false in
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex (BlockProgram.script B).size (BlockProgram.script B).size)

/-- When the prefix already provides the descriptor's static operands, the
caller can mount the real selector directly in the reached live memory. -/
theorem PassRun.ofInstalledPacketGroups (pre : List (SourceOnline.Packet (A) w)) (term : p.step.Choice → SourceOnline.Packet (A) w)
    (tail : p.step.Choice → List (SourceOnline.Packet (A) w))
    (first : SourceOnline.Group (A) L (pub 2) small (loc.first B) total raw pre)
    (middle : ∀ i, SourceOnline.Group (A) L (pub 2) small (loc.first B+pre.length) total
      (SourceOnline.post raw pre) [term i])
    (last : ∀ i, SourceOnline.Group (A) L (pub 2) small (loc.first B+pre.length+1) total (term i).output (tail i))
    (emptyPre : ∀ e ∈ pre, e.stage.choices = List.replicate e.stage.choices.length [])
    (emptyTail : ∀ i, ∀ e ∈ tail i, e.stage.choices = List.replicate e.stage.choices.length [])
    (termBits : ∀ i, (term i).stage.choices = List.ofFn (workerTapes o w i))
    (clock : small ≤ cap) (big : Online.Run.ControlBounds (A).plan cap (w := w))
    (bounds : Online.Run.ControlBounds (A).plan small (w := w))
    (arityEq : arity (A).catalog = L.shape.arity) (baseEq : (pub 2).val = L.base) (fit : levelStart L 0 < 2^w)
    (preFits : loc.first B+pre.length < total) (endFits : loc.finish B ≤ total)
    (lengths : ∀ i, loc.first B+pre.length+1+(tail i).length = loc.finish B)
    (room : total ≤ directoryRows L) (agree : Agree (levelStart L 0 ≤ ·) raw m)
    (ready : Boundary resident pub (levelWords L : Word w) total (loc.first B) past X m)
    (install : ∀ mid : Memory w, Agree (levelStart L 0 ≤ ·) (SourceOnline.post raw pre) mid →
      Workspace.Installed (arity (A).catalog) (pub 2) mid → mid (pt).tag.val = tag →
      (mid (pt).ordinal.val).val = loc.first B+pre.length → (mid (pt).rows.val).val = total →
      mid ((pt).directory-1).val = (levelWords L : Word w) → Nonempty (SelectorSite o L pub cap small mid))
    (stored : ∀ i, resident (past++[level o encode i]) (p.next i) (SourceOnline.post (term i).output (tail i)))
    (transfer : ∀ i u v, Agree (levelStart L 0 ≤ ·) u v →
      resident (past++[level o encode i]) (p.next i) u → resident (past++[level o encode i]) (p.next i) v)
    (charges : ∀ i, groupCost (A) pre + groupCost (A) [term i] + groupCost (A) (tail i) ≤ rate) :
    Nonempty (PassRun resident pub (levelWords L : Word w) total cap small rate loc o encode past m) := by
  classical
  obtain ⟨before,agree',bank,tag',ord,rows,stride,charge₀⟩ := deterministicGroup first emptyPre clock bounds
    arityEq baseEq fit preFits.le room agree ready.bank ready.tag ready.ordinalValue ready.totalValue ready.stride
  let site := (install before.segment.memory agree' bank tag' ord rows stride).some
  have live : before.segment.memory (pt).ordinal.val < before.segment.memory (pt).rows.val :=
    Fin.lt_def.mpr (by rw [ord,rows]; exact preFits)
  have inside : (before.segment.memory (pt).ordinal.val).val < directoryRows L := ord ▸ preFits.trans_le room
  let selected := site.interval big bounds arityEq baseEq fit bank tag' live inside
  have mid i := selectorGroupPost selected i (term i) (middle i)
    (by rw [termBits]; exact site.interval_bits big bounds arityEq baseEq fit bank tag' live inside i)
    bounds arityEq baseEq fit preFits room agree' bank tag' ord rows stride
  have doneTail (i : p.step.Choice) : ∃ out : QuietInterval (A) pub cap small (some 0) (selected.cut.part i).memory,
      Boundary resident pub (levelWords L : Word w) total (loc.finish B) (past++[level o encode i])
        (p.next i) out.segment.memory ∧ RAMBuckets.cost Report.probes out.source.logs ≤ groupCost (A) (tail i) := by
    obtain ⟨data,inst,tag₂,ord₂,total₂,stride₂,_⟩ := mid i
    obtain ⟨out,next,_,charge⟩ := boundary_of_group (last i) (emptyTail i) clock bounds arityEq baseEq fit
      ((lengths i).le.trans endFits) room data inst tag₂ ord₂ total₂ stride₂ (stored i) (transfer i)
    exact ⟨out,lengths i ▸ next,charge⟩
  choose after next charge₂ using doneTail
  refine ⟨PassRun.ofIntervals before selected after (fun i => ?_) next⟩
  have charge₁ := (mid i).2.2.2.2.2.2
  exact (Nat.add_le_add (Nat.add_le_add charge₀ charge₁) (charge₂ i)).trans (charges i)

/-- The genuine source worker on the default admitted term suffices to
install that same physical selector for every reached prefix memory. -/
theorem PassRun.ofPacketGroups (pre : List (SourceOnline.Packet (A) w)) (term : p.step.Choice → SourceOnline.Packet (A) w)
    (tail : p.step.Choice → List (SourceOnline.Packet (A) w))
    (first : SourceOnline.Group (A) L (pub 2) small (loc.first B) total raw pre)
    (middle : ∀ i, SourceOnline.Group (A) L (pub 2) small (loc.first B+pre.length) total
      (SourceOnline.post raw pre) [term i])
    (last : ∀ i, SourceOnline.Group (A) L (pub 2) small (loc.first B+pre.length+1) total (term i).output (tail i))
    (emptyPre : ∀ e ∈ pre, e.stage.choices = List.replicate e.stage.choices.length [])
    (emptyTail : ∀ i, ∀ e ∈ tail i, e.stage.choices = List.replicate e.stage.choices.length [])
    (termBits : ∀ i, (term i).stage.choices = List.ofFn (workerTapes o w i))
    (clock : small ≤ cap) (big : Online.Run.ControlBounds (A).plan cap (w := w))
    (bounds : Online.Run.ControlBounds (A).plan small (w := w))
    (arityEq : arity (A).catalog = L.shape.arity) (baseEq : (pub 2).val = L.base) (fit : levelStart L 0 < 2^w)
    (preFits : loc.first B+pre.length < total) (endFits : loc.finish B ≤ total)
    (lengths : ∀ i, loc.first B+pre.length+1+(tail i).length = loc.finish B)
    (room : total ≤ directoryRows L) (agree : Agree (levelStart L 0 ≤ ·) raw m)
    (ready : Boundary resident pub (levelWords L : Word w) total (loc.first B) past X m)
    (worker : WorkerInput o w) (operands : SelectorSite.SourceWorker worker L (term (defaultSelection o)))
    (stored : ∀ i, resident (past++[level o encode i]) (p.next i) (SourceOnline.post (term i).output (tail i)))
    (transfer : ∀ i u v, Agree (levelStart L 0 ≤ ·) u v →
      resident (past++[level o encode i]) (p.next i) u → resident (past++[level o encode i]) (p.next i) v)
    (charges : ∀ i, groupCost (A) pre + groupCost (A) [term i] + groupCost (A) (tail i) ≤ rate) :
    Nonempty (PassRun resident pub (levelWords L : Word w) total cap small rate loc o encode past m) := by
  apply PassRun.ofInstalledPacketGroups pre term tail first middle last emptyPre emptyTail termBits
    clock big bounds arityEq baseEq fit preFits endFits lengths room agree ready _ stored transfer charges
  exact SelectorSite.install_from_packet worker (term (defaultSelection o)) operands (middle (defaultSelection o))
    clock arityEq baseEq fit preFits room

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
