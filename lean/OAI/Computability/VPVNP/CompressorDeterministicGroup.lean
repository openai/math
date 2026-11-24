import OAI.Computability.VPVNP.CompressorPassIntervalData
import OAI.Computability.VPVNP.CompressorSourceGroups
import OAI.Computability.VPVNP.CompressorIntervalCost

/-! # Executing a deterministic group of source packets

The scheduled interval uses the public pointer bank and starts in the
calendar state. Its private-clock reports come from the native scheduler.
They include the control calls surrounding each packet. At the return
boundary the live memory agrees with the source on every data address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM BlockPlanner DescriptorSpace Schedule SourceTransport
open scoped Fin.CommRing

variable {w small cap ordinal total : ℕ} {A : Script} {L : Layout}
    {pub : Fin 11 → Word w} {m raw : Memory w} {ps : List (SourceOnline.Packet A w)}
local notation "pt" => Workspace.ports (arity A.catalog) (pub 2)
local notation "tag" => LiveStageLink.tagWord w (Online.calendarIndex A.size A.size)

/-- The total data calls and probes, with the descriptor and recipe charge
for every visited row. This includes the four control calls of an empty row. -/
def groupCost (A : Script) (ps : List (SourceOnline.Packet A w)) : ℕ :=
  RAMBuckets.cost Report.probes (ps.flatMap SourceWalk.Packet.reports) * (arity A.catalog+3) +
    ps.length * (Online.Run.maxReads A.plan+4*arity A.catalog+26)

/-- A deterministic flattened tape witnesses determinism of each source visit. -/
theorem packet_quiet_of_flat {n : ℕ}
    (empty : ps.flatMap (fun p => p.stage.choices) = List.replicate n [])
    (p : SourceOnline.Packet A w) (hp : p ∈ ps) :
    p.stage.choices = List.replicate p.stage.choices.length [] := by
  apply List.eq_replicate_length.mpr
  intro b hb
  have mem : b ∈ ps.flatMap (fun p => p.stage.choices) := List.mem_flatMap.mpr ⟨p,hp,hb⟩
  rw [empty] at mem
  exact (List.mem_replicate.mp mem).2

private theorem interval_mono {steps : List (Online.Run.Step A.size A.size w)}
    (h : Online.Run.Interval A.plan pt small m steps) (le : small ≤ cap) :
    Online.Run.Interval A.plan pt cap m steps := by
  induction steps generalizing m with
  | nil => trivial
  | cons s ss ih =>
    obtain ⟨v, rest⟩ := h
    exact ⟨⟨v.phase,v.active,v.input,v.source,v.recipeCap.trans le,v.dataCap.trans le⟩, ih rest⟩

private theorem final_tag {steps : List (Online.Run.Step A.size A.size w)} (h : m (pt).tag.val = tag) :
    (Online.Run.finalMemory (C := A.catalog) pt m steps) (pt).tag.val = tag := by
  induction steps generalizing m with
  | nil => exact h
  | cons s ss ih => exact ih (by simp [Online.post,writeMemory])

/-- Run the packets under the smaller source clock, replay them at the
enclosing workspace clock, and recover all persistent boundary fields. -/
theorem deterministicGroup (group : SourceOnline.Group A L (pub 2) small ordinal total raw ps)
    (quiet : ∀ p ∈ ps, p.stage.choices = List.replicate p.stage.choices.length [])
    (clock : small ≤ cap) (bounds : Online.Run.ControlBounds A.plan small (w := w))
    (arityEq : arity A.catalog = L.shape.arity) (baseEq : (pub 2).val = L.base)
    (fit : levelStart L 0 < 2^w) (count : ordinal+ps.length ≤ total) (room : total ≤ directoryRows L)
    (agree : Agree (levelStart L 0 ≤ ·) raw m) (bank : Workspace.Installed (arity A.catalog) (pub 2) m)
    (htag : m (pt).tag.val = tag) (ord : (m (pt).ordinal.val).val = ordinal)
    (rows : (m (pt).rows.val).val = total) (stride : m ((pt).directory-1).val = (levelWords L : Word w)) :
    ∃ out : QuietInterval A pub cap small (some 0) m,
      Agree (levelStart L 0 ≤ ·) (SourceOnline.post raw ps) out.segment.memory ∧
      Workspace.Installed (arity A.catalog) (pub 2) out.segment.memory ∧
      out.segment.memory (pt).tag.val = tag ∧
      (out.segment.memory (pt).ordinal.val).val = ordinal+ps.length ∧
      (out.segment.memory (pt).rows.val).val = total ∧
      out.segment.memory ((pt).directory-1).val = (levelWords L : Word w) ∧
      RAMBuckets.cost Report.probes out.source.logs ≤ groupCost A ps := by
  obtain ⟨steps,v,phases,reports,tapes,mem,ord',rows',stride',stable⟩ :=
    SourceOnline.interval_stable A L (pub 2) arityEq baseEq fit small ordinal total m raw ps
      group.chronological group.checked group.prepared count room agree ord rows htag stride
  have big : Online.Run.ControlBounds A.plan cap (w := w) :=
    ⟨bounds.tags,bounds.calendar.trans clock,bounds.launch.trans clock⟩
  have valid := interval_mono v clock
  let seg := OnlineWorkspace.intervalSegment A pub big htag steps valid stable bank
  let core : OnlineWorkspace.Core A pub seg small :=
    ⟨Online.Run.intervalLog A.plan pt m steps,(Online.Run.intervalSegment A.plan pt (state := 0) bounds htag steps v).run,rfl⟩
  have deterministic (s : Online.Run.Step A.size A.size w) (hs : s ∈ steps) :
      s.row.choices = List.replicate s.row.choices.length [] := by
    have seen := List.mem_map_of_mem (f := fun q : Online.Run.Step A.size A.size w => q.row.choices) hs
    rw [tapes] at seen
    obtain ⟨p,hp,eq⟩ := List.mem_map.mp seen
    rw [← eq]
    exact quiet p hp
  let out : QuietInterval A pub cap small (some 0) m :=
    ⟨seg,OnlineWorkspace.intervalSegment_quiet A pub big htag steps valid stable bank deterministic,
      OnlineWorkspace.intervalSegment_stable A pub big htag steps valid stable bank,
      OnlineWorkspace.intervalSegment_state A pub big htag steps valid stable bank, core⟩
  have actual : out.segment.memory = Online.Run.finalMemory (C := A.catalog) pt m steps :=
    OnlineWorkspace.intervalSegment_memory A pub big htag steps valid stable bank
  refine ⟨out,actual.symm ▸ mem,OnlineWorkspace.intervalSegment_bank A pub big htag steps valid stable bank,
    actual.symm ▸ final_tag htag,actual.symm ▸ ord',actual.symm ▸ (congrArg Fin.val rows').trans rows,
    actual.symm ▸ stride'.trans stride,?_⟩
  have lengthEq : steps.length = ps.length := by simpa only [List.length_map] using congrArg List.length phases
  have logs : steps.flatMap (fun s => s.row.reports) = ps.flatMap SourceWalk.Packet.reports := by
    simpa only [List.flatMap_def] using congrArg List.flatten reports
  have cost := Online.Run.interval_cost_bound A.plan pt steps m v
  rw [Online.Run.sourceCost_eq_flatMap,logs,lengthEq] at cost
  exact cost

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
