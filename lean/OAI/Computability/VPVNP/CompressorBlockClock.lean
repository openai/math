import OAI.Computability.VPVNP.CompressorPrefixWorkerFit
import OAI.Computability.VPVNP.CompressorShrinkHeaderGreedyPackets
import OAI.Computability.VPVNP.CompressorShrinkBundlePackets
import OAI.Computability.VPVNP.CompressorInitialScriptPackets
import OAI.Computability.VPVNP.CompressorOnlineBranchCut
import OAI.Computability.VPVNP.CompressorScheduledGreedyRates

/-!
# A common clock for the fixed online descriptor program

A finite maximum covers the deterministic workers at every scheduled degree.
The motif workers add their bounds at the actual input length. A larger
outer machine clock gives the same controller, launcher, and source budgets.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockClock

open BurstRAM Compression CursorBounds Schedule SourceOnline Filter
open ShrinkSliceSweep

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

local notation "A" => BlockProgram.script B
local notation "D" => Online.N (BlockPlanner.Script.size (BlockProgram.script B))
  (BlockPlanner.Script.size (BlockProgram.script B))

/-- Fuel bound for the header publishers of the degree-refresh pass. -/
def refreshHeaders := ScheduledRates.headerCap (BlockProgram.geometry B)
  (.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent)

/-- Length-independent fuel allowance covering the deterministic workers, including surviving
slices, refresh headers and shrinking bundle scans. -/
def fixedFuel :=
  95 + (1 + SurvivingNative.ops.length) + refreshHeaders B +
    Finset.univ.sup (ShrinkBundlePackets.maxFuel B)

/-- Length-independent controller allowance for startup, shrinking headers, greedy scans and
online dispatch. -/
def fixedClock :=
  InitialScriptPackets.budget (A) (BlockProgram.layout B 0 0 0) (S.degreeExponent 0) +
    Finset.univ.sup (ShrinkHeaderGreedyPackets.clock B) +
    (30 + 2 * (A).size + 2 * (D) + 5) +
    (20 + 6 * (arity (A).catalog + 1) + 2 * (D) + 5)

/-- Worker fuel at input length `n`, including shrinking prefix preparation and term selection
at the chosen word width. -/
def workerFuel (b n : ℕ) := fixedFuel B + ShrinkBranch.prefixClock B b n +
  SelectedTermWorker.clock B (wordBits b n)

/-- Common online clock obtained by adding the fixed controller allowance to the scan budget at
the current worker fuel. -/
def small (b n : ℕ) := fixedClock B + scanCap (A) (workerFuel B b n)

theorem scan {b n fuel : ℕ} (h : fuel ≤ workerFuel B b n) :
    scanCap (A) fuel ≤ small B b n := by
  unfold small
  apply le_trans _ (Nat.le_add_left ..)
  unfold scanCap
  omega

theorem fixed (b n : ℕ) :
    scanCap (A) 95 ≤ small B b n ∧
    scanCap (A) (1 + SurvivingNative.ops.length) ≤ small B b n ∧
    scanCap (A) (refreshHeaders B) ≤ small B b n ∧
    ∀ i : Fin S.steps, scanCap (A) (ShrinkBundlePackets.maxFuel B i) ≤ small B b n := by
  have simple (j : ℕ) (hj : j ≤ fixedFuel B) := scan B (b := b) (n := n)
    (hj.trans (by unfold workerFuel; omega))
  refine ⟨simple 95 ?_, simple _ ?_, simple _ ?_, fun i ↦ simple _ ?_⟩
  · unfold fixedFuel; omega
  · unfold fixedFuel; omega
  · unfold fixedFuel; omega
  · exact (Finset.le_sup (f := ShrinkBundlePackets.maxFuel B) (Finset.mem_univ i)).trans
      (Nat.le_add_left ..)

theorem start (b n base positions blocks : ℕ) :
    InitialScriptPackets.budget (A) (BlockProgram.layout B base positions blocks)
        (S.degreeExponent 0) ≤ small B b n ∧
    ∀ i : Fin S.steps, ShrinkHeaderGreedyPackets.clock B i ≤ small B b n := by
  rw [InitialScriptPackets.budget_fixed B]
  unfold small fixedClock
  constructor
  · omega
  · intro i
    have := Finset.le_sup (f := ShrinkHeaderGreedyPackets.clock B) (Finset.mem_univ i)
    omega

theorem dynamic (b n : ℕ) :
    scanCap (A) (ShrinkBranch.prefixClock B b n) ≤ small B b n ∧
    scanCap (A) (max 64 (SelectedTermWorker.clock B (wordBits b n))) ≤ small B b n := by
  constructor
  · exact scan B (by unfold workerFuel; omega)
  · exact scan B (by unfold workerFuel fixedFuel; omega)

theorem controls {b n cap : ℕ} (tags : (D) ≤ 2 ^ wordBits b n) (h : small B b n ≤ cap) :
    Online.Run.ControlBounds (A).plan cap (w := wordBits b n) := by
  have c : fixedClock B ≤ cap := (Nat.le_add_right _ _).trans h
  unfold fixedClock at c
  refine ⟨tags, ?_, ?_⟩
  · change 30 + 2 * (A).size + 2 * (D) + 5 ≤ cap
    omega
  · change 20 + 6 * (arity (A).catalog + 1) + 2 * (D) + 5 ≤ cap
    omega

/-- The length dependence is at most quartic in the binary logarithm. -/
theorem rate (b : ℕ) : ∃ K : ℕ, ∀ n, small B b n ≤ K * (n.log2 + 1) ^ 4 := by
  let G := (SelectedTerms.shrinkGrid B).stepConstant
  let H := G * ((b + 10) ^ 4 + 2) + 7 + ShrinkDemandGather.cost + 1
  let J := SelectedTerms.stepConstant B + 7
  let F := fixedClock B + fixedFuel B + scanCap (A) 0
  let C := (b + 10) ^ 4 + 2
  refine ⟨F + H + J * (2 * C + 1), fun n ↦ ?_⟩
  let L := (n.log2 + 1) ^ 4
  have hl : 0 < L := Nat.pow_pos (Nat.succ_pos _)
  have grow (x : ℕ) := Nat.le_mul_of_pos_right x hl
  have word : wordBits b n ≤ C * L := (Nat.le_add_right ..).trans
    (show wordBits b n + Nat.clog 2 (0 + 1) + 1 ≤ C * L from word_plus_clog_le b n 0 (by omega))
  have term : SelectedTermWorker.clock B (wordBits b n) ≤ J * (2 * C + 1) * L := by
    change J * (2 * wordBits b n + 1) ≤ _
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith only [word, hl]
  have cap := SourceOnline.scanCap_le (A) (workerFuel B b n)
  change fixedClock B + scanCap (A) (workerFuel B b n) ≤ (F + H + J * (2 * C + 1)) * L
  apply (Nat.add_le_add_left cap _).trans
  change fixedClock B + (fixedFuel B + H * L + SelectedTermWorker.clock B (wordBits b n)
    + scanCap (A) 0) ≤ _
  have stable := grow F
  unfold F at *
  simp only [Nat.add_mul] at stable ⊢
  omega

/-- A single threshold covers the tag word, the smaller clock, and any fixed
number of further link instructions. -/
theorem eventually_room (b : ℕ) (hb : 1 ≤ b) (link : ℕ) : ∀ᶠ n : ℕ in atTop,
    small B b n + link ≤ n ∧
    ∀ cap, small B b n ≤ cap → Online.Run.ControlBounds (A).plan cap (w := wordBits b n) := by
  obtain ⟨K, bound⟩ := rate B b
  filter_upwards [eventually_polylog_le (K + link) 4,
    CursorRAM.eventual_word_room b hb (PolynomiallyBounded.const (D))] with n hn tags
  refine ⟨?_, fun cap enough ↦ controls B tags.le enough⟩
  have pad := Nat.le_mul_of_pos_right link (Nat.pow_pos (n := 4) (Nat.succ_pos n.log2))
  rw [Nat.add_mul] at hn
  exact (Nat.add_le_add (bound n) pad).trans hn

end CompressorRecords.BlockClock

end

end VPVNP
end Computability
end OAI
