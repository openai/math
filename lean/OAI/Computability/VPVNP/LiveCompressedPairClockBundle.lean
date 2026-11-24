import OAI.Computability.VPVNP.CompressorChronologicalRate
import OAI.Computability.VPVNP.LiveCompressedPairBlockClock
import OAI.Computability.VPVNP.LiveCompressedPairSourceCaps
import OAI.Computability.VPVNP.PairTraversalControllerSelectedRun
import OAI.Computability.VPVNP.PairTraversalTerminalBootstrap

/-! # Simultaneous clocks for a selected physical compression branch -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork CursorBounds CompressorRecords Schedule Filter PairSimulation
open ScheduledTrace BranchSegments PairSimulation.LocalHistory

universe v
variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "scr" => BlockProgram.script B
local notation "bootBound" => TerminalBootstrap.cost (BlockProgram.allocationShape B) B.recordLimit + 1
local notation "arena" => TraversalController.callFuel B.recordLimit

/-- One length supplies the private clocks and live bucket shares used by
the fixed program. Every mathematical choice and native report is quantified
inside the bounds at this length. -/
structure BranchClocks (u : PairExponents B.growthConstant) (b : ℕ) (bs : Bootstrap)
    (initial phases raw site q link n : ℕ) : Prop where
  n2048 : 2048 ≤ n
  processors : 128 ≤ processorCount b n
  capacity : 16 ≤ liveCapacity u n
  blocks : blockCount (u.θ : ℝ) n ≤ n.log2+1
  privateRoom : ∀ G : PairStages.Group, G.clock = n^10000 → n^9999+107 ≤ G.clockAt LiveProgram.Stage.pair
  startBurst : ∀ i, sourceFuel bs initial phases n i + 5 ≤ liveCapacity u n
  startTicks : ∀ i, sourceFuel bs initial phases n i + 77 ≤ n
  bootBurst : bootBound + 9 ≤ liveCapacity u n
  bootTicks : bootBound + 107 ≤ n
  arenaBurst : arena + 9 ≤ liveCapacity u n
  arenaTicks : arena + 107 ≤ n
  sourceClock : BlockClock.small B b n + link ≤ n
  controls : ∀ cap, BlockClock.small B b n ≤ cap → Online.Run.ControlBounds (scr).plan cap (w := wordBits b n)
  online : ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
    (pub : Fin 11 → Word (wordBits b n)) {st : Option (Word (wordBits b n))} {m : Memory (wordBits b n)} {clock : ℕ}
    (segment : Segment (OnlineWorkspace.program (scr).plan pub) clock st m)
    (source : OnlineWorkspace.Core scr pub segment (BlockClock.small B b n)),
    RAMBuckets.cost Report.probes source.logs ≤ chronologicalRate B raw*(pairInput S labels hD).positions*(n.log2+1) →
    64*RAMBuckets.cost Report.probes source.logs ≤ processorCount b n*liveCapacity u n ∧
      ∀ r ∈ source.logs, r.probes+11 ≤ liveCapacity u n ∧ r.events.length+101 ≤ n
  terminal : ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
    (hT : blockCount (u.θ : ℝ) n*S.laneBits ≤ lanes) (A : Type v) [CommRing A] (f : B.Entry → A)
    (hf : B.IsSolution f), let X := pairInput S labels hD
    let T := blockCount (u.θ : ℝ) n
    let E := B.execute f hf T hT X
    ∀ z : E.Choices, let Y := E.finalState z
      let chain := E.termChain (B.records f hf T hT X) z
      320*branchAccesses X Y chain (terminalCoefficient S.baseDegree S.steps B.recordLimit bootBound 1 site) q n ≤
        processorCount b n*liveCapacity u n ∧ ∀ v, siteAccesses Y chain site q n v+9 ≤ liveCapacity u n

/-- Fix the script, address exponent, pass charge and vertex charge first.
The resulting threshold works for every finite model and each of its branches. -/
theorem eventually_branchClocks (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    (bs : Bootstrap) (initial phases raw site q link : ℕ) :
    ∀ᶠ n : ℕ in atTop, BranchClocks.{v} B u b bs initial phases raw site q link n := by
  let K := max (bootBound) (arena)
  filter_upwards [eventually_online_core_caps B u b hb (chronologicalRate B raw) 1 link,
    eventually_terminal_share B u b hb (bootBound) 1 site q, eventually_startup_burst u bs initial phases 5,
    eventually_sourceFuel bs initial phases 77, eventually_liveCapacity_ge u (K+16),
    eventually_numeric B u b 1 hb (by decide), eventually_ge_atTop (K+107),
    eventually_ge_atTop 2048] with n online terminal burst ticks hH numeric hK hn
  have bootK : (bootBound) ≤ K := le_max_left ..
  have arenaK : (arena) ≤ K := le_max_right ..
  refine ⟨hn,by have := numeric.2.2.1; omega,by omega,terminal.1,
    fun G hc => private_clock_room G (by omega) hc,burst,ticks,by omega,by omega,by omega,by omega,
    online.1,online.2.1,?_,terminal.2⟩
  intro base lanes labels hD pub st m clock segment source bound
  exact online.2.2 labels hD pub segment source (by simpa only [pow_one] using bound)

namespace BranchClocks

set_option exponentiation.threshold 10000

attribute [local irreducible] BlockProgram.script BlockClock.small CursorNetwork.cursorState
set_option maxHeartbeats 1200000

variable {B} {u : PairExponents B.growthConstant} {b : ℕ} {bs : Bootstrap}
variable {initial phases raw site q link n : ℕ}
variable (h : BranchClocks.{v} B u b bs initial phases raw site q link n)
include h
local notation "T" => blockCount (u.θ : ℝ) n
local notation "P" => initialPositions b n

/-- Convert the fixed-length ceilings to the actual private clock in the
physical group. This also gives room for every active site's private bound. -/
theorem groupCaps (G : PairStages.Group) (clock : G.clock = n^10000) :
    let fuel := G.clockAt LiveProgram.Stage.pair
    n ≤ fuel ∧ 136 ≤ fuel ∧ n^45 ≤ fuel ∧
      (∀ i, sourceFuel bs initial phases n i+77 ≤ fuel) ∧
      (bootBound+9 ≤ liveCapacity u n ∧ bootBound+107 ≤ fuel) ∧
      (arena+9 ≤ liveCapacity u n ∧ arena+107 ≤ fuel) := by
  intro fuel
  have hn := h.n2048
  have big := h.privateRoom G clock
  change n^9999+107 ≤ fuel at big
  have pos : 0 < n := by omega
  have lt : n ≤ n^9999 := by simpa only [pow_one] using Nat.pow_le_pow_right pos (by decide : 1 ≤ 9999)
  have room : n^9999 ≤ fuel := (Nat.le_add_right _ 107).trans big
  have fit : n ≤ fuel := lt.trans room
  have active : n^45 ≤ n^9999 := Nat.pow_le_pow_right pos (by decide : 45 ≤ 9999)
  exact ⟨fit,(by decide : 136 ≤ 2048).trans (hn.trans fit),active.trans room,fun i => (h.startTicks i).trans fit,
    ⟨h.bootBurst,h.bootTicks.trans fit⟩,h.arenaBurst,h.arenaTicks.trans fit⟩

variable {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
variable {a g a' g' : ℕ} {X : State a g} {E : StateExecution R a' g' X}
variable {origin : PassOrigins B f hf E} {W : E.MapWitnesses f} {readers : ExecutionReaders E W}
variable {resident : Resident B f hf (wordBits b n)} {past : List (SelectedLevel B f hf)}
variable {pub : Fin 11 → Word (wordBits b n)} {pitch : Word (wordBits b n)} {m : Memory (wordBits b n)} {cap total : ℕ}

/-- Specialize the two online bounds to the actual initial interval and
scheduled result, using the startup estimate returned by descriptor execution.
The numbering of the cursor's input positions is immaterial here. -/
theorem selectedOnline {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
    (hD : 1 < virtualBits b n)
    (start : QuietInterval scr pub cap (BlockClock.small B b n) (some 0) m)
    (first : RAMBuckets.cost Report.probes start.source.logs ≤ initialRate B*(P+1))
    (result : Result resident pub pitch total cap (BlockClock.small B b n)
      (T*(S.steps+1)*(nativePassRate scr raw*P)+4) E origin W readers past start.segment.state start.segment.memory)
    (G : PairStages.Group) (clock : G.clock = n^10000) (z : E.Choices) :
    let core := start.combinedCore result.trace result.source z
    64*RAMBuckets.cost Report.probes core.logs ≤ processorCount b n*liveCapacity u n ∧
      ∀ r ∈ core.logs, r.probes+11 ≤ liveCapacity u n ∧ r.events.length+101 ≤ G.clockAt LiveProgram.Stage.pair := by
  intro core
  have positions := pairInput_positions S labels hD
  have pos := (pairInput S labels hD).positions_pos
  rw [positions] at pos
  have cost := h.online labels hD pub _ core (by
    rw [positions]
    change RAMBuckets.cost Report.probes (start.combinedCore result.trace result.source z).logs ≤ _
    rw [start.combinedCost]
    exact (Nat.add_le_add first (result.cost z)).trans (by
      simpa only [Nat.add_assoc] using chronological_charge B raw P T n pos h.blocks))
  have fit := (h.groupCaps G clock).1
  exact ⟨cost.1,fun r hr => ⟨(cost.2 r hr).1,(cost.2 r hr).2.trans fit⟩⟩

end BranchClocks
end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
