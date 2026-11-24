import OAI.Computability.VPVNP.CompressorRefreshSplitWindows
import OAI.Computability.VPVNP.CompressorPublishedHeadWindows

/-!
# The real refresh group on both sides of its selector

The prefix, singleton selector and suffix consume the original refresh
reports in order. Their online ordinals are consecutive. The prefix is the
choice-independent graph preparation, the singleton contains precisely
the canonical term choice, and each suffix packet consumes empty tapes.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshCore

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PhaseRecipe BlockPlanner Schedule
open DescriptorSpace PortRefresh PortRefresh.LevelRecipe PortRefresh.Allocation SourceTransport SourceOnline
open PairSimulation.LocalHistory
open scoped Fin.CommRing Classical

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable {w g : ℕ} (base : BurstRAM.Word w) (positions blocks t : ℕ)
variable (X : State S.portExponent (S.portExponent+g))
variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "cur" => Script.levelsPerBlock scr*t+S.steps
local notation "head" => levelStart L cur
local notation "H" => levelStart L 0
local notation "start" => arrayBase L cur
local notation "old" => packedIncidence L w cur (X.positions*2^S.portExponent)
local notation "sh" => RefreshBlockPlan.shape B
local notation "P" => plan X (sh).a₀ (sh).dH (sh).ties (sh).stride start
local notation "hc" => (S.port_bound.connected_and_pos S.port_order).1
local notation "he" => Nat.two_pow_pos S.expanderExponent
local notation "hd" => S.degree_bounds.2
local notation "ties" => RefreshBlockPlan.order B
local notation "dst" => NewSlots.word (bits := w) (Plan.term P)
local notation "W" => BlockGroups.refresh B 1
local notation "ord" => (scr).initial.length+t*(scr).block.length+(W).before.length
local notation "total" => directoryRows L
local notation "Pkt" => SourceOnline.Packet scr w
local notation "o" => PassOrigin.refresh (B:=B) (f:=f) (hf:=hf) X

/-- Three exact consecutive packet ranges of the compiled refresh. -/
structure SelectedSplit (termCap cap : ℕ) (m : Memory w) (pre : List Pkt) (sel : Pkt) (tail : List Pkt) : Prop where
  whole : Group scr L base cap ord total m (pre++sel::tail)
  prePhases : pre.map (fun p => p.stage.phase) = (RefreshPrepare.window B).indices
  selPhase : sel.stage.phase = index B (CanonicalWorker.refreshTermIndex B)
  tailPhases : tail.map (fun p => p.stage.phase) = (finishWindow B).indices
  preCount : pre.length = 3+(sh).ties
  preQuiet : ∀ p ∈ pre, p.stage.choices = List.replicate p.stage.choices.length []
  selTapes : sel.stage.choices = List.ofFn (workerTapes o w c)
  tailQuiet : ∀ p ∈ tail, p.stage.choices = List.replicate p.stage.choices.length []
  fits : (P).segments ≤ 2^w
  prepare : PrepareRun X old ((P).scratch w) (NewSlots.word (bits := w) (P).demand) ties (NewSlots.word (2^g))
    fits m (post m pre) (pre.flatMap SourceWalk.Packet.reports)
  selected : termRun S.graph he hc B.refresh ties X (NewSlots.word (P).demand) dst (sh).stride termCap
    (blockTapes S.graph he hc B.refresh X c w) sel.input = some sel.reports
  finished : Finish.Run X S.graph he hc B.refresh S.port_order hd c dst (sh).stride ((P).inputs w) ((P).output w)
    sel.output (tail.flatMap SourceWalk.Packet.reports)

variable {B f hf base positions blocks t X c}
theorem SelectedSplit.groups {termCap cap : ℕ} {m : Memory w} {pre tail : List Pkt} {sel : Pkt}
    (h : SelectedSplit B f hf base positions blocks t X c termCap cap m pre sel tail) :
    Group scr L base cap ord total m pre ∧ Group scr L base cap (ord+pre.length) total (post m pre) [sel] ∧
      sel.input=post m pre ∧ Group scr L base cap (ord+pre.length+1) total sel.output tail :=
  h.whole.split_at_selector

variable (B f hf base positions blocks t X c)

private theorem quiet_packets {A : Script} {u : Memory w} {ps : List (SourceOnline.Packet A w)} {rs : List (Report w)}
    (chron : SourceWalk.Chronological SourceOnline.Visit.Runs u ps) (logs : ps.flatMap SourceWalk.Packet.reports = rs)
    (empty : branchPaths rs = List.replicate rs.length []) :
    ∀ p ∈ ps, p.stage.choices = List.replicate p.stage.choices.length [] :=
  ScheduledTrace.packet_quiet_of_flat (((PublishedHeads.chronological_tapes u ps chron).trans
    (congrArg branchPaths logs)).trans empty)

private theorem one_packet {A : Script} {ps : List (SourceOnline.Packet A w)} (h : ps.length = 1) :
    ∃ p, ps = [p] := by
  cases ps with
  | nil => simp at h
  | cons p ps =>
    have hl : ps.length=0 := by rw [List.length_cons] at h; omega
    exact ⟨p,by rw [List.eq_nil_iff_length_eq_zero.mpr hl]⟩

set_option maxHeartbeats 1500000 in
/-- Install the three actual windows for a specified already-verified
refresh run. Their concatenated packets reproduce its exact report list. -/
theorem split_verified (termCap cap : ℕ) (m : Memory w) (rs : List (Report w))
    (ht : t < blocks) (fit : H < 2^w) (room : (P).stop < 2^w) (before : head+60 < start)
    (positive : 0 < termCap) (clock : scanCap scr (max 64 termCap) ≤ cap)
    (entry : EntryState B base positions blocks t X m)
    (alloc : PrepareLayout X old (sh).a₀ (sh).dH (sh).ties (sh).stride start)
    (build : Build.Run X S.graph he hc B.refresh S.port_order hd c ties old start (sh).stride termCap alloc m rs)
    (actual : SourceWalk (fun j u logs => Scheduled.Source X S.graph he hc B.refresh hd c ties old start (sh).stride termCap j u logs ∧
      Scheduled.StageBounds (t := (sh).ties) X S.graph he hc B.refresh start (sh).stride H j u logs)
      (LevelRecipe.order sh) m rs) :
    ∃ pre sel tail, SelectedSplit B f hf base positions blocks t X c termCap cap m pre sel tail ∧
      (pre++sel::tail).flatMap SourceWalk.Packet.reports = rs := by
  obtain ⟨rp,rt,rf,all,bp,bt,bf,prep,term,finish⟩ := split_logs B X c old start termCap H alloc build actual
  let prefixMem := after m (eventLog rp)
  let suffixMem := after prefixMem (eventLog rt)
  obtain ⟨pre,hp,pLab,pLog,next⟩ := attach_part B base positions blocks t X c termCap (RefreshPrepare.stages B)
    (RefreshPrepare.window B) entry ht fit room before positive cap clock bp
  obtain ⟨ss,hs,sLab,sLog,last⟩ := attach_part B base positions blocks t X c termCap [.term]
    (selectWindow B) next ht fit room before positive cap clock (.singleton bt)
  obtain ⟨tail,htail,tLab,tLog,_⟩ := attach_part B base positions blocks t X c termCap (afterTerm B)
    (finishWindow B) last ht fit room before positive cap clock bf
  have npre : pre.length = (RefreshPrepare.stages B).length := by
    simpa only [List.length_map,Window.indices,List.length_ofFn] using congrArg List.length pLab
  have one : ss.length = 1 := by simpa only [List.length_map,Window.indices,List.length_ofFn,List.length_cons,List.length_nil] using congrArg List.length sLab
  obtain ⟨sel,rfl⟩ := one_packet one
  have slog : sel.reports=rt := by simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using sLog
  have ppost : post m pre = prefixMem := by rw [post,pLog]
  have sinput : sel.input = prefixMem := hs.chronological.1
  have sout : sel.output = suffixMem := by rw [SourceWalk.Packet.output,sinput,slog]
  have ord₁ : (scr).initial.length+t*(scr).block.length+(selectWindow B).before.length = ord+pre.length := by
    rw [select_before,npre]; omega
  have ord₂ : (scr).initial.length+t*(scr).block.length+(finishWindow B).before.length = ord+pre.length+1 := by
    rw [finish_before,npre]; omega
  have hp' : Group scr L base cap ord total m pre := hp
  have hs' : Group scr L base cap (ord+pre.length) total (post m pre) [sel] := by rw [ppost,← ord₁]; exact hs
  have ht' : Group scr L base cap (ord+pre.length+1) total (post (post m pre) [sel]) tail := by
    rw [← ord₂,ppost,post,List.flatMap_cons,List.flatMap_nil,List.append_nil,slog]; exact htail
  have rest := hs'.append ht'
  have whole : Group scr L base cap ord total m (pre++sel::tail) := hp'.append rest
  have index' : sel.stage.phase=(selectWindow B).index 0 := by
    simp only [List.map_cons,List.map_nil,Window.indices,List.ofFn_succ,List.ofFn_zero,List.cons.injEq,and_true] at sLab
    exact sLab.trans (congrArg (selectWindow B).index (Fin.ext (by rfl)))
  have qp := side_quiet B X c old start termCap H (by
    intro j hj
    rintro rfl
    simp [RefreshPrepare.stages] at hj) bp
  have qt := side_quiet B X c old start termCap H (by
    intro j hj; rintro rfl
    simp [afterTerm] at hj) bf
  have sc : branchPaths sel.reports = sel.stage.choices := ((runSegment_iff ..).mp hs.chronological.2.1).2.2
  have tape : sel.stage.choices = List.ofFn (workerTapes o w c) := sc.symm.trans
    ((congrArg branchPaths slog).trans (CanonicalWorker.refresh_branches B f hf X c w old start termCap bt.1))
  refine ⟨pre,sel,tail,⟨whole,pLab,index'.trans (select_index B),tLab,?_,quiet_packets hp.chronological pLog qp,
    tape,quiet_packets htail.chronological tLog qt,alloc.regions.fits,?_,?_,?_⟩,?_⟩
  · rw [npre]; simp [RefreshPrepare.stages]; omega
  · rw [ppost,pLog]; exact prep
  · rw [sinput,slog]; exact term
  · rw [sout,tLog]; exact finish
  · simp only [List.flatMap_append,List.flatMap_cons,pLog,slog,tLog,List.append_assoc] at all ⊢
    exact all.symm

set_option maxHeartbeats 1400000 in
/-- Split a complete refresh construction already produced by the core
builder. Its report list and final stored memory are the same after packet
attachment. The prefix and singleton now retain their individual reports. -/
theorem split_built (termCap cap : ℕ) (m : Memory w) (rs : List (Report w))
    (ht : t < blocks) (size : X.positions ≤ positions) (fit : endAddress L < 2^w)
    (entry : EntryState B base positions blocks t X m)
    (represented : (old).Represents X m)
    (termBits : termConstant S.graph he hc B.refresh ties+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (nextWidth : (dyadicRefreshNext X S.graph he hc B.refresh S.port_order hd c).maxWireWidth < 2^w)
    (budget : TermWorker.budget B.refresh (sh).ties ((sh).ports*(sh).dH) w X.maxWireWidth ≤ termCap)
    (positive : 0 < termCap) (clock : scanCap scr (max 64 termCap) ≤ cap)
    (built : Built B base positions blocks t X c termCap m rs) :
    ∃ pre sel tail, SelectedSplit B f hf base positions blocks t X c termCap cap m pre sel tail ∧
      (pre++sel::tail).flatMap SourceWalk.Packet.reports = rs := by
  have idx : cur < (L).levels := by
    have h := Nat.mul_le_mul_left (S.steps+1) ht
    rw [Nat.mul_succ] at h
    change (S.steps+1)*t+S.steps < 1+(S.steps+1)*blocks; omega
  let current : Fin (L).levels := ⟨cur,idx⟩
  have source := source_region B base positions blocks t X current rfl size fit
  have room := (BlockLevelFit.refresh B base.val positions blocks current rfl X size fit).1.word
  change (plan X (S.degreeExponent 0) (sh).dH (sh).ties (sh).stride (start+0*tableWords L)).stop < 2^w at room
  simp only [Nat.zero_mul,Nat.add_zero] at room
  obtain ⟨alloc,run⟩ := built.source
  have actual := Scheduled.verified_sources X S.graph he hc B.refresh S.port_order hd c ties old start
    (sh).stride H termCap alloc m rs represented (fun j => (source j).1) (fun j => (source j).2)
    le_rfl room termBits nextWidth budget run
  have before : head+60 < start := by change head+60 < head+66+6*slotCapacity L; omega
  exact split_verified B f hf base positions blocks t X c termCap cap m rs ht
    ((levelStart_mono L (Nat.zero_le _)).trans_lt fit) room before positive clock entry alloc run actual

/-- Execute the complete selected refresh and retain its exact selector
split alongside the represented next graph and all stored history fields. -/
theorem build_split (termCap cap : ℕ) (m : Memory w) (ht : t < blocks) (size : X.positions ≤ positions)
    (fit : endAddress L < 2^w) (entry : EntryState B base positions blocks t X m)
    (represented : (old).Represents X m)
    (termBits : termConstant S.graph he hc B.refresh ties+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (nextWidth : (dyadicRefreshNext X S.graph he hc B.refresh S.port_order hd c).maxWireWidth < 2^w)
    (budget : TermWorker.budget B.refresh (sh).ties ((sh).ports*(sh).dH) w X.maxWireWidth ≤ termCap)
    (positive : 0 < termCap) (clock : scanCap scr (max 64 termCap) ≤ cap) :
    ∃ pre sel tail, SelectedSplit B f hf base positions blocks t X c termCap cap m pre sel tail ∧
      Built B base positions blocks t X c termCap m ((pre++sel::tail).flatMap SourceWalk.Packet.reports) := by
  obtain ⟨ps,_,_,built⟩ := build_group B base positions blocks t X c termCap cap m ht size fit entry.rows entry.pitch
    clock entry.header represented termBits nextWidth budget positive
  obtain ⟨pre,sel,tail,h,hr⟩ := split_built B f hf base positions blocks t X c termCap cap m _ ht size fit entry
    represented termBits nextWidth budget positive clock built
  exact ⟨pre,sel,tail,h,hr ▸ built⟩

end CompressorRecords.RefreshCore

end

end VPVNP
end Computability
end OAI
