import OAI.Computability.VPVNP.PairSimulationMapHandlerImage
import OAI.Computability.VPVNP.PairSimulationMapChainWork

/-!
# Instruction and probe bounds for the fixed map handler family

The descriptor writer's instruction count and its external probes are
fixed for each grid point and party. The rest of the call uses only private
instructions. These bounds also cover prefixes ending at rejection.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapHandlerImage.Family

open MotifSelector MotifGrid MotifBlocks MotifConversion MapConstants
open BurstRAM LocalHistory Compression

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'} {t s w : ℕ}
  (F : Family B t s)

/-- A handler initializes its descriptor, selects the entry, then runs the table. -/
noncomputable def clock (i : Index B) (u : ℕ) : ℕ :=
  let L := F.layout i
  MapArgumentWriter.clock (F.base i) (F.fields i) + MapInline.factor L F.ordinal *
    (L.lines.length + (1 + 3 * (MapPortAgreement.ports G i.2 L.core.edgeOrder).length) +
      MapNativeClock.cap B i.1 i.2 u)

/-- Only the compiled external loads in the descriptor writer charge probes. -/
noncomputable def probes (i : Index B) : ℕ :=
  ∑ j, ((MapArgumentWriter.recipes (F.base i) (F.fields i)) j).loads

private noncomputable def init (i : Index B) : ℕ :=
  (F.layout i).lines.length + (1 + 3 * (MapPortAgreement.ports G i.2
    (F.layout i).core.edgeOrder).length)

private noncomputable def localFactor (i : Index B) : ℕ :=
  MapArgumentWriter.clock (F.base i) (F.fields i) + MapInline.factor (F.layout i) F.ordinal *
    (init F i + 1)

/-- One fixed multiplier covers descriptor writing, initialization and literal lowering. -/
noncomputable def clockFactor : ℕ := ∑ i, F.localFactor i

/-- The finite bound on external loads is independent of all repetition counts. -/
noncomputable def probeBound : ℕ := ∑ i, F.probes i

theorem probes_le (i : Index B) : F.probes i ≤ F.probeBound :=
  Finset.single_le_sum (fun a _ ↦ Nat.zero_le (F.probes a)) (Finset.mem_univ i)

theorem clock_le (i : Index B) (u : ℕ) :
    F.clock i u ≤ F.clockFactor * (MapNativeClock.cap B i.1 i.2 u + 1) := by
  let n := MapNativeClock.cap B i.1 i.2 u
  let a := MapArgumentWriter.clock (F.base i) (F.fields i)
  let h := MapInline.factor (F.layout i) F.ordinal
  have hi : a + h * (init F i + 1) ≤ F.clockFactor :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (F.localFactor j)) (Finset.mem_univ i)
  calc
    _ ≤ (a + h * (init F i + 1)) * (n + 1) := by
      rw [Nat.add_mul, Nat.mul_assoc]
      apply Nat.add_le_add (Nat.le_mul_of_pos_right a (Nat.succ_pos n))
      apply Nat.mul_le_mul_left
      change init F i + n ≤ _
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ _ := Nat.mul_le_mul_right _ hi

/-- Apply the bounds to the exact instruction and probe conclusions of the native handler.
Every prefix has a smaller resource use on that same path. -/
theorem trace_le (i : Index B) (u : ℕ) (trace pre : List (Event w))
    (len : trace.length ≤ F.clock i u) (loads : countProbes trace = F.probes i)
    (isPrefix : pre <+: trace) :
    pre.length ≤ F.clockFactor * (MapNativeClock.cap B i.1 i.2 u + 1) ∧
      countProbes pre ≤ F.probeBound := by
  refine ⟨isPrefix.length_le.trans (len.trans (F.clock_le i u)), ?_⟩
  obtain ⟨tail, rfl⟩ := isPrefix
  rw [countProbes_append] at loads
  have bound := F.probes_le i
  omega

variable {S : BlockSchedule K} (T : S.Templates) {ss sr : ℕ}
  (shrink : Family T.shrink t ss) (refresh : Family T.refresh t sr)

open scoped Classical in
/-- Instruction bound and external probe count for a map invocation. Shrink and refresh use the
handler selected by the demand grid point and party, with the clock evaluated at the
demand's repetition count. A node without a lookup costs zero in both coordinates. -/
noncomputable def costs {d : ℕ} : MapInvocation T d → ℕ × ℕ
  | .shrink x _ =>
    let i := (demandGrid T.shrink ShrinkMotif.demandMass_pos x.demand, x.party)
    (shrink.clock i (repetitions T.shrink x.demand), shrink.probes i)
  | .refresh x _ =>
    let i := (demandGrid T.refresh (fun _ ↦ zero_lt_one) x.demand, x.party)
    (refresh.clock i (repetitions T.refresh x.demand), refresh.probes i)
  | .noLookup => (0, 0)

/-- The same two fixed constants can be used at every selected shrink and refresh node. -/
theorem costs_le {d : ℕ} (m : MapInvocation T d) :
    (costs T shrink refresh m).1 ≤
      (max shrink.clockFactor refresh.clockFactor + 1) * (m.nativeCap T + 1) ∧
    (costs T shrink refresh m).2 ≤ max shrink.probeBound refresh.probeBound := by
  classical
  cases m with
  | shrink x _ =>
    exact ⟨(shrink.clock_le ..).trans (Nat.mul_le_mul_right _
      ((le_max_left ..).trans (Nat.le_succ _))), (shrink.probes_le _).trans (le_max_left ..)⟩
  | refresh x _ =>
    exact ⟨(refresh.clock_le ..).trans (Nat.mul_le_mul_right _
      ((le_max_right ..).trans (Nat.le_succ _))), (refresh.probes_le _).trans (le_max_right ..)⟩
  | noLookup => exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- Charge the actual selected maps in their placement subtree to the same occurrence
count used for the child fields and the vertex history. -/
theorem probeTotal_le {A : Type*} {N Y : NetworkKernel.Network}
    (c : NetworkKernel.TermChain A N Y) (calls : MapInputs T c) {L : ℕ} (hl : c.AllRecordsLe L)
    (leaf count : N.Site → ℕ)
    (h : ∀ v, leaf v ≤ count v * max shrink.probeBound refresh.probeBound) :
    ∀ v, mapAndLeafCost (fun m ↦ (costs T shrink refresh m).2) c calls leaf v ≤
      c.occurrences count v * max shrink.probeBound refresh.probeBound :=
  mapAndLeafCost_le _ c calls (fun _ _ m ↦ (costs_le T shrink refresh m).2) hl leaf count h

end PairSimulation.MapHandlerImage.Family

end VPVNP
end Computability
end OAI
