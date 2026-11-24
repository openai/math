import OAI.Computability.VPVNP.CompressorRefreshEmitBranchOrder
import OAI.Computability.VPVNP.CompressorRefreshEmitSources
import OAI.Computability.VPVNP.CompressorRefreshEmitAfter
import OAI.Computability.VPVNP.CompressorRefreshResidentAdvance
import OAI.Computability.VPVNP.CompressorRefreshGroupSplit

/-! # All seven windows of the physical degree refresh -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.RefreshEmit

open BurstRAM BlockPlanner Compression DescriptorSpace PassTimeline Schedule SourceOnline
open ScheduledTrace PairSimulation.TraversalRoles PairSimulation.LocalHistory PortRefresh
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → R) (hf : B.IsSolution f) {g w : ℕ} (base : Word w)
variable (positions blocks t cap n : ℕ) (initial : TaggedLayer) (initialFrame : Fin 8 → Word w)
variable (past : List (SelectedLevel B f hf)) (X : State S.portExponent (S.portExponent + g))

local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (arity (Script.catalog scr)) base
local notation "fl" => Script.levelsPerBlock scr * t
local notation "cur" => fl + S.steps
local notation "nxt" => fl + (S.steps + 1)
local notation "loc" => Located.mk t (Pass.refresh (steps := S.steps))
local notation "start" => Located.first loc B
local notation "ord" => List.length (Script.initial scr) + t * List.length (Script.block scr)
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "he" => Nat.two_pow_pos S.expanderExponent
local notation "hd" => And.right S.degree_bounds
local notation "Choice" => Refresh.DyadicRefreshChoice X S.graph he hc B.refresh
local notation "shape" => RefreshBlockPlan.shape B
local notation "sites" => LevelRecipe.Shape.ports shape
local notation "expDeg" => LevelRecipe.Shape.dH shape
local notation "numTies" => LevelRecipe.Shape.ties shape
local notation "o" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "role" => Scalars.Pass.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent
local notation "hr" => ScheduledRates.headerRate (BlockProgram.geometry B) role
local notation "cr" => Build.chargeFactor S.graph he hc B.refresh numTies
local notation "res" =>
  CompiledResident.resident B f hf base positions blocks n initial initialFrame
local notation "P" => SourceOnline.Packet scr w
local notation "logs" => (fun ps : List P => List.flatMap SourceWalk.Packet.reports ps)

variable (encode : Refresh.DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh → List Bool)
variable (m : Memory w) (termCap : ℕ)
local notation "fits" => termConstant S.graph he hc B.refresh (RefreshBlockPlan.order B) +
  4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w
local notation "workerBudget" =>
  TermWorker.budget B.refresh numTies (sites * expDeg) w X.maxWireWidth

/-- The common prefix and every selected suffix are constructed by running
the native workers. All post-selector records inhabit the output memory of
that selector, including the completed current graph and traversal history. -/
theorem build (index : past.length = cur) (live : t < blocks) (size : X.positions ≤ positions)
    (fit : endAddress L < 2 ^ w) (rows : m (pt).rows.val = (directoryRows L : Word w))
    (pitch : m ((pt).directory - 1).val = (levelWords L : Word w))
    (headerClock : scanCap scr (ScheduledRates.headerCap (BlockProgram.geometry B) role) ≤ cap)
    (termClock : scanCap scr (max 64 termCap) ≤ cap) (siteRoom : X.positions < 2 ^ w)
    (degree : slotDegree S < 2 ^ w) (demandWidth : 2 ^ S.portExponent * X.maxWireWidth < 2 ^ w)
    (bits : fits) (nextWidth : ∀ c : Choice,
      (Refresh.dyadicRefreshNext X S.graph he hc B.refresh S.port_order hd c).maxWireWidth < 2 ^ w)
    (budget : workerBudget ≤ termCap) (positive : 0 < termCap) (stored : res past X m) :
    ∃ hs ds term tail, Sources B f hf base positions blocks t cap n initial initialFrame past X
      encode m hs ds term tail := by
  classical
  have curr : CurrentGraph.Current L (cur) X n m := index ▸ stored.1.2.1
  obtain ⟨hs, ds, before⟩ := RefreshBefore.run B f hf base positions blocks t X termCap cap
    m n live size fit rows pitch headerClock termClock curr siteRoom degree demandWidth positive
  have baseEq : start = ord + (RefreshHeaders.window B).before.length := by
    rw [RefreshBefore.Before.start_offset]; rfl
  have first := before.group
  rw [← baseEq] at first
  let headerMem := post m hs
  have entry : RefreshCore.EntryState B base positions blocks t X headerMem :=
    ⟨before.inputHeader, before.headerRows, before.headerPitch⟩
  have clock : scanCap scr 42 ≤ cap := by unfold scanCap at termClock ⊢; omega
  have branch (c : Choice) : ∃ (p : P) (tail : List P),
      SourceOnline.Group scr L base cap (start + (hs ++ ds).length) (directoryRows L)
        (post m (hs ++ ds)) [p] ∧
      SourceOnline.Group scr L base cap (start + (hs ++ ds).length + 1) (directoryRows L)
        p.output tail ∧
      p.stage.choices = List.ofFn (workerTapes o w c) ∧
      (∀ q ∈ tail, q.stage.choices = List.replicate q.stage.choices.length []) ∧
      start + (hs ++ ds).length + 1 + tail.length = (loc).finish B ∧
      res (past ++ [RefreshPlacement.selectedLevel B f hf X c (encode c)])
        (Refresh.dyadicRefreshNext X S.graph he hc B.refresh S.port_order hd c)
        (post p.output tail) ∧
      RAMBuckets.cost Report.probes (logs ((hs ++ ds) ++ p :: tail)) ≤
        hr + cr * X.positions + X.positions * (18 * 2 ^ (S.degreeExponent 0) + 4) + 27 := by
    obtain ⟨pre, p, rest, split, built⟩ := RefreshCore.build_split B f hf base positions blocks t
      X c termCap cap headerMem live size fit entry before.represented bits (nextWidth c)
      budget positive termClock
    let u := RefreshPlacement.selectedLevel B f hf X c (encode c)
    have hheader := before.headers_eq c (encode c)
    have hh := before.header_for c (encode c)
    have counts := before.counts_for c (encode c)
    have align := before.matches c (encode c) (out := post headerMem pre)
      (rs := logs pre) (fit := split.fits) (by rw [← hheader]; exact split.prepare)
    obtain ⟨_, middle, input, suffix⟩ := split.groups
    have ordSel := selector_ordinal before split
    have middle' : SourceOnline.Group scr L base cap (start + (hs ++ ds).length)
        (directoryRows L) (post m (hs ++ ds)) [p] := by
      rw [ordSel, align.2]; exact middle
    let raw := after headerMem (eventLog (logs (pre ++ p :: rest)))
    have rawEq : raw = post p.output rest := by
      change post headerMem (pre ++ p :: rest) = _
      rw [post_append, ← input]
      simp only [post, List.flatMap_cons, SourceWalk.after_append, SourceWalk.Packet.output]
    obtain ⟨copies, pubs, finished⟩ := after_core B base positions blocks t cap f hf X c (encode c)
      termCap headerMem (logs (pre ++ p :: rest)) live size fit clock before.headerRows
      before.headerPitch _ counts before.atOldHeads before.atNewHeads built
    obtain ⟨_, atCopy, finish⟩ := branch_ordinals before split (copies ++ pubs) finished.count
    have joined := suffix.append (by rw [← rawEq, atCopy]; exact finished.group)
    have stateEq : post p.output (rest ++ (copies ++ pubs)) = post (post raw copies) pubs := by
      rw [post_append, ← rawEq, post_append]
    have next : res (past ++ [u]) (u.pass.next u.term)
        (post p.output (rest ++ (copies ++ pubs))) := by
      rw [stateEq]
      exact RefreshPayloadHistory.advance B base positions blocks t f hf X c (encode c)
        ⟨cur, before.oldLive⟩ ⟨nxt, before.newLive⟩ rfl (Nat.add_assoc ..).symm index live size fit
        stored hh hheader before.represented before.atNewHeads built finished.copied
        finished.installed
    refine ⟨p, rest ++ (copies ++ pubs), middle', ?_, split.selTapes, ?_, ?_, next, ?_⟩
    · rw [ordSel]; exact joined
    · intro q hq
      exact (List.mem_append.mp hq).elim (split.tailQuiet q) (finished.quiet q)
    · exact finish
    · exact aggregate B X f hf base positions blocks t cap termCap c before align.1 built
        finished.charge
  choose term tail middle last choices quiet lengths next charge using branch
  exact ⟨hs, ds, term, tail, before, first, middle, last, choices, quiet, lengths, next, charge⟩

end CompressorRecords.RefreshEmit

end

end VPVNP
end Computability
end OAI
