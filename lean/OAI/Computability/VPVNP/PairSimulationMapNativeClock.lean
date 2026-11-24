import OAI.Computability.VPVNP.PairSimulationMapRowLoop
import OAI.Computability.VPVNP.PairSimulationMapSelectors
import OAI.Computability.VPVNP.PairSimulationMapTotalCheck
import OAI.Computability.VPVNP.PairSimulationEntryWork

/-!
# Instruction budgets for a complete fixed-template map call

The bounds include the port comparison, selector decoder, repeated label
lookups, the full-vector width comparison and the local histogram update.
The table constant is chosen before the dynamic widths and all input bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapNativeClock

open MotifBlocks MotifConversion MotifGrid MotifSelector MapPortAgreement

variable {K J D E : Type} [Field K] [Fintype J] [Fintype D] [Fintype E]
  {src dst : D → J} {G : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p) (realWidths q) H H')

/-- The instruction bounds of the five linked phases at a selected grid row.
Two incident ports per supply edge suffice even when both ends are at this party. -/
noncomputable def cap (z : B.grid.demands) (j : J) (u : ℕ) : ℕ :=
  ((7 * (u * B.selectorBits) + 6) * (2 * Fintype.card E) + 3) +
    ((6 * B.selectorBits + 1 + (2 * (selectorTable B).length + 1) + 5) * u + 1) +
    ((5 + 2 * (selectorTable B).length + MapRowLoop.rowCap B z j) * u + 1) +
    (Fintype.card E + 1) + (7 * u + 1)

/-- Fixing the tables gives a linear instruction cap, including the final
width comparisons on a descriptor whose totals differ. -/
theorem uniform : ∃ C : ℕ, ∀ z j u, cap B z j u ≤ C * (u + 1) := by
  let M := ∑ z : B.grid.demands, ∑ j, MapRowLoop.rowCap B z j
  let C := (7 * B.selectorBits + 6) * (2 * Fintype.card E) + 3 +
    (6 * B.selectorBits + 1 + (2 * (selectorTable B).length + 1) + 5 + 1) +
    (5 + 2 * (selectorTable B).length + M + 1) + (Fintype.card E + 1) + 8
  refine ⟨C, fun z j u ↦ ?_⟩
  have hm : MapRowLoop.rowCap B z j ≤ M :=
    (Finset.single_le_sum (fun a _ ↦ Nat.zero_le (MapRowLoop.rowCap B z a))
      (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ ↦ Nat.zero_le (∑ j, MapRowLoop.rowCap B a j))
      (Finset.mem_univ z))
  unfold cap
  dsimp only [C]
  nlinarith only [Nat.mul_le_mul_right u hm, hm, Nat.zero_le u, Nat.zero_le M,
    Nat.zero_le B.selectorBits, Nat.zero_le (Fintype.card E * B.selectorBits),
    Nat.zero_le (Fintype.card E * u), Nat.zero_le (selectorTable B).length]

end PairSimulation.MapNativeClock

namespace PairSimulation.LocalHistory

open Compression MotifBlocks MotifGrid MotifConversion MotifSelector

variable {K : Type} [Field K] {S : BlockSchedule K} (B : S.Templates)

open scoped Classical in
/-- The exact two motif tables of the selected compressor. Direct equality
checks emit no parameters and use their separate field comparison routines. -/
noncomputable def MapInvocation.nativeCap {d : ℕ} : MapInvocation B d → ℕ
  | .shrink x _ => MapNativeClock.cap B.shrink
      (demandGrid B.shrink ShrinkMotif.demandMass_pos x.demand) x.party
      (repetitions B.shrink x.demand)
  | .refresh x _ => MapNativeClock.cap B.refresh
      (demandGrid B.refresh (fun _ ↦ zero_lt_one) x.demand) x.party (repetitions B.refresh x.demand)
  | .noLookup => 0

/-- A single table constant covers both actual passes and all malformed bits. -/
theorem mapInvocation_nativeCap (B : S.Templates) :
    ∃ C : ℕ, ∀ d (m : MapInvocation B d), m.nativeCap B ≤ C * (d + 1) := by
  classical
  obtain ⟨A, ha⟩ := MapNativeClock.uniform B.shrink
  obtain ⟨A', ha'⟩ := MapNativeClock.uniform B.refresh
  refine ⟨max A A', fun d m ↦ ?_⟩
  cases m with
  | shrink x hx => exact (ha ..).trans (Nat.mul_le_mul (le_max_left ..) (Nat.succ_le_succ hx))
  | refresh x hx => exact (ha' ..).trans (Nat.mul_le_mul (le_max_right ..) (Nat.succ_le_succ hx))
  | noLookup => exact Nat.zero_le _

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
