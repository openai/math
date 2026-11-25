import OAI.Computability.BorderVNP.ShortenStageSchedule
import OAI.Computability.BorderVNP.PackedCoverScale

/-!
# Congruence levels for every executed public histogram

An epoch's input depth is the preceding epoch's terminal depth. Within that
epoch the prepared word lengths determine each intermediate level, including
the two-word descent used by the executable segment and seed lookup.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicCapacity

open Adaptive Cover Packing TeamScales Filter
open scoped Classical

variable {rounds : ℕ} (word : Fin rounds → ℕ) (last : ℕ)

/-- Depth of the rounded site table after the indicated epoch. -/
def terminalDepth (start epoch : ℕ) :=
  start - Levels.totalDrop word last * (epoch+1)

/-- Congruence level of the seed directory at one combining node. -/
def seedDepth (start epoch : ℕ) (j : Fin rounds) :=
  Levels.level word (terminalDepth word last start epoch) last (j.val+1)+1

/-- At the actual rounded initial depth, all seed levels fit the initial
quotient. Every executed node has a positive auxiliary depth, satisfies its
fixed decoding cutoff, and uses the high input prescribed by the stage path. -/
theorem eventually_schedule_levels (I : Type*) [Fintype I] [Nonempty I] (cut : ℕ)
    {τ α : ℝ} (hτ : 0 ≤ τ)
    (hg : τ*Real.logb 2 ((CoverScale.factor I : ℝ)^Levels.totalDrop word last) ≤ α/10)
    (hα : α/10 < 9/10) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let start := CoverScale.initialDepth I r n
      (∀ t j, seedDepth word last start t j ≤ start+1) ∧
      ∀ t < epochs τ n, ∀ j : Fin rounds,
        ∃ d : ℕ, 1 ≤ d ∧ d+2*word j = seedDepth word last start t j ∧
          cut ≤ d+2*word j+2*word j ∧
          d+2*word j+2*word j = Levels.level word (terminalDepth word last start t) last j.val+1 := by
  let loss := Levels.totalDrop word last
  let bound := max loss (cut+2*Finset.univ.sup word)
  filter_upwards [CoverScale.eventually_depths I loss bound hτ hg hα] with n depth
  intro r hr start
  obtain ⟨hfloor,hstart,_,_,_⟩ := depth r hr
  change bound+1 ≤ start-loss*epochs τ n at hfloor
  change (start-loss*epochs τ n)+loss*epochs τ n = start at hstart
  have hls : loss ≤ start := (le_max_left _ _ : loss ≤ bound).trans (by omega)
  constructor
  · intro t j
    have once : loss ≤ loss*(t+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos t)
    have boundHigh : terminalDepth word last start t+loss ≤ start := by
      change start-loss*(t+1)+loss ≤ start
      omega
    have atStart := Levels.le_start word (terminalDepth word last start t) last (j.val+1)
    rw [Levels.start] at atStart
    exact Nat.succ_le_succ (atStart.trans boundHigh)
  · intro t ht j
    have used := Nat.mul_le_mul_left loss (show t+1 ≤ epochs τ n by omega)
    have terminal : bound+1 ≤ terminalDepth word last start t := by
      change bound+1 ≤ start-loss*(t+1)
      omega
    have wordCap := Finset.le_sup (f := word) (Finset.mem_univ j)
    have floorCap : cut+2*word j ≤ bound :=
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 wordCap) cut).trans (le_max_right _ _)
    have low := Levels.terminal_le word (terminalDepth word last start t) last (j.val+1)
    have step := Levels.step word (terminalDepth word last start t) last j
    let s := seedDepth word last start t j
    change _ = s+2*word j at step
    have good : cut+2*word j+1 ≤ s := by
      change _ ≤ Levels.level word (terminalDepth word last start t) last (j.val+1)+1
      omega
    exact ⟨s-2*word j,by omega,by omega,by omega,by omega⟩

end Shortening.PublicCapacity

end BorderVNP
end Computability
end OAI
