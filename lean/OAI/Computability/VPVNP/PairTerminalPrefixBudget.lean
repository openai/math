import OAI.Computability.VPVNP.PairTerminalPrefixSegment
import OAI.Computability.VPVNP.CursorBranchCommunication
import OAI.Computability.VPVNP.PairLinkSlack

/-!
# Communication budget of the live terminal-prefix worker

The final outgoing directory has one entry for each slot of each final site.
The prefix stage visits exactly those entries and makes one closing call.
Including fixed linker costs on every call, these reports fit every positive
fraction of the live group's communication allowance uniformly over branches.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalPrefix.Segment

open Compression CursorNetwork CursorBounds Filter BurstRAM CompressorRecords LocalHistory

/-- The physical outgoing-arc directory has one entry for each site and slot. -/
theorem arc_count_positions {a g : ℕ} (Y : State a g) : arcCount Y = Y.positions * 2 ^ a := by
  have sites := Fintype.card_congr (siteOrder Y).entries
  rw [Fintype.card_fin] at sites
  exact congrArg (· * 2 ^ a) sites

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

/-- A common size threshold gives both the per-burst allowances and the
total charge bound, including the linker margin on the closing report. -/
theorem eventually_budget (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) {ε : ℝ} (hε : 0 < ε)
    (probeMargin : ℕ := 2) (tickMargin : ℕ := 47) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {bases lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin bases ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        let w := wordBits b n
        ∀ (z : E.Choices) (pub : Fin 11 → Word w) (dir : IncidenceDirectory w)
          (base : Word w) (m : Memory w) (rs : List (Report w)),
          let Y := E.finalState z
          Run pub Y dir base m rs →
            arcCount Y = Y.positions * S.baseDegree ∧
            (∀ r ∈ rs, 1 + r.probes + probeMargin ≤ liveBucket u.δ n ∧
              r.events.length + tickMargin ≤ n) ∧
            ((RAMBuckets.cost Report.probes rs + probeMargin * rs.length : ℕ) : ℝ) <
              ε * (processorCount b n : ℝ) * liveBucket u.δ n := by
  let C := (8 + probeMargin) * (S.baseDegree + 1)
  filter_upwards [eventually_pairAccesses B u b hb C 0 hε,
    eventually_pairBurstSlack u (8 + probeMargin), eventually_ge_atTop (29 + tickMargin)]
    with n budget slack hn
  intro bases lanes labels hD hT A _ f hf X T E w z pub dir base m rs Y run
  have count : arcCount Y = Y.positions * S.baseDegree := arc_count_positions Y
  have bucket : 8 + probeMargin ≤ liveBucket u.δ n := by
    have hn₀ : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    exact_mod_cast (le_add_of_nonneg_left hn₀).trans slack
  refine ⟨count, fun r hr => ?_, ?_⟩
  · obtain ⟨hp, ht⟩ := run.bounds r hr
    omega
  · let chain := E.termChain (B.records f hf T hT X) z
    apply lt_of_le_of_lt _ (budget labels hD hT A f hf z).1
    apply Nat.cast_le.mpr
    change _ ≤ branchAccesses X Y chain C 0 n
    rw [run.charge, run.calls, count, branchAccesses_eq]
    apply le_trans _ (Nat.mul_le_mul_left C (show Y.positions ≤ _ by omega))
    calc
      _ ≤ (8 + probeMargin) * (Y.positions * S.baseDegree) +
          (8 + probeMargin) * Y.positions := by
        have close := Nat.le_mul_of_pos_right (8 + probeMargin) Y.positions_pos
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
        omega
      _ = C * Y.positions := by dsimp [C]; ring

end PairSimulation.TerminalPrefix.Segment

end VPVNP
end Computability
end OAI
