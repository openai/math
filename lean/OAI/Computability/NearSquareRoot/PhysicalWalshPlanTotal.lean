import OAI.Computability.NearSquareRoot.PhysicalWalshPlanCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherTotal
import OAI.Computability.NearSquareRoot.PhysicalWalshRoundedTotal

/-! # Total original-order Walsh execution at the numerical and geometry cutoff

The emitted plan, router and recursive kernel are the same programs used for
the sparse runtime estimate. Their correctness on each admitted input only
requires finite executions of the router and the recursive invocations.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code FixedPoint KernelPass PhysicalWalshNode Matrix

/-- Every admitted parameter executes the emitted plan and returns records
approximating the selected Walsh matrix, with arbitrary input-dependent budgets. -/
theorem planPassTotal {a W K₀ M G : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    (router piece : Cmd) (correct : Correct p) (factor : recursionFactor p ≤ M)
    (raw : ∃ t s, EffectiveBoundedTask.Runs piece t s (rawInput hw p) (rawOutput hw p))
    (route : PositionTotalAt router K₀)
    {g : ℝ} (hg : 0 < g) (cap : g ≤ G+1)
    {I : Type} (k : I → ℕ) (bits : (i : I) → Finset (Fin (k i)))
    (mask : I → List Bool) (x : (i : I) → Fin (2^k i) → Record (k i))
    (large : ∀ i, selectedCutoff K₀ G W M ≤ k i) (hm : ∀ i, mask i = flags (bits i))
    (sparse : ∀ i, ((bits i).card : ℝ) ≤ g*k i/Real.log (2+k i))
    (norm : ∀ i, ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i)) :
    (∃ t s, EffectiveBoundedTask.Runs (planCmd (a+1) W router piece) t s
      (fun i => send (mask i,Odd.words (x i)))
      (fun i => send (Odd.words (selectedResult hw p (bits i) (x i))))) ∧
    ∀ i, ‖recordArray (selectedResult hw p (bits i) (x i)) - WithLp.toLp 2
      (BoxFin.flatWalsh (bits i) *ᵥ (fun j => FixedPoint.value (k i) (x i j)))‖ ≤ 1/(2:ℝ)^(50*k i) := by
  let s i := (bits i).card
  let pos i := gatherPerm (bits i)
  let v i := lift (gatherInput (pos i) (x i))
  let b i := Pieces.root (k i) (s i) (v i)
  have routeLarge i : K₀ ≤ k i := (le_max_left ..).trans (large i)
  have geomLarge i : SparseCutoff.threshold G W ≤ k i := (le_max_left ..).trans ((le_max_right ..).trans (large i))
  have numLarge i : precisionCutoff M ≤ k i := (le_max_right ..).trans ((le_max_right ..).trans (large i))
  have geom i := SparseCutoff.geometry (a+1) hw (geomLarge i) hg cap (sparse i)
  have guards i := accurate_of_cutoff ha hw p correct factor (numLarge i) (bits i) (pos i)
    (gatherPerm_low (bits i)) (x i) (norm i)
  have capacity (i) : (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1) := by
    change Pieces.extent (a+1) W (k i) (s i) ≤ 2^(componentBits (k i)+1)
    unfold Pieces.extent
    rw [←Padding.total (a+1) hw (geom i).1]
    calc
      _ ≤ 2^k i + 2^k i := Nat.add_le_add_left (geom i).2 _
      _ = 2^(k i+1) := by rw [pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold componentBits; omega)
  obtain ⟨t,r,even⟩ := Pieces.roundedSweepTotal hw p piece ha b capacity (fun i => (guards i).1) raw
  have grouped := GroupedCommand.groupedPass hw p ha _ k s v (fun i => (geom i).1) (fun i => (geom i).2) t r even
  exact ⟨selectedTaskTotal hw p router _ route k bits mask x routeLarge hm ⟨_,_,grouped⟩,fun i => (guards i).2⟩

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
