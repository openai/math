import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedPass
import OAI.Computability.NearSquareRoot.PhysicalWalshSparseCutoff

/-! # Computable cutoff for the original-order physical Walsh command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code Space KernelPass FixedPoint PhysicalWalshNode Matrix

/-- A bound on the width at which all three interfaces accept their inputs. -/
def selectedCutoff (router G W M : ℕ) :=
  max router (max (SparseCutoff.threshold G W) (precisionCutoff M))

noncomputable section

/-- At every width above the specified cutoff the physical command has the
sparse cost, the required live space, and the stated error on the original row. -/
theorem selectedPassAt {a W K₀ M G : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    (correct : Correct p) (factor : recursionFactor p ≤ M) {ρ c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hc : 0 ≤ c) (hP : ∀ w,0 ≤ P w)
    (release : PieceRelease hw p ρ c L P) (route : PositionRuns ρ K₀)
    {g H Q : ℝ} {q : ℕ} (hg : 0 < g) (cap : g ≤ G+1) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    {I : Type} (k : I → ℕ) (bits : (i : I) → Finset (Fin (k i)))
      (mask : I → List Bool) (x : (i : I) → Fin (2^k i) → Record (k i)) :
      (∀ i, selectedCutoff K₀ G W M ≤ k i) → (∀ i, mask i = flags (bits i)) →
      (∀ i, ((bits i).card : ℝ) ≤ g*k i/Real.log (2+k i)) →
      (∀ i, ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i)) →
      (∀ i, 0 ≤ L (componentBits (k i)) ∧ L (componentBits (k i)) ≤ H*(1+Real.log (2+k i))) →
      (∀ i, P (componentBits (k i)) ≤ Q*(k i+1:ℝ)^q) →
      let input i := send (mask i,Odd.words (x i))
      let output i := send (Odd.words (selectedResult hw p (bits i) (x i)))
      BoundedTask (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k) input output ∧
      (∃ C : ℕ, TapeRun (fun i => C*(Pieces.sparseTime ρ (k i)+1)) (fun i => C*(Pieces.sparseSpace (k i)+1)) input output) ∧
      ∀ i, ‖recordArray (selectedResult hw p (bits i) (x i)) - WithLp.toLp 2
        (BoxFin.flatWalsh (bits i) *ᵥ (fun j => FixedPoint.value (k i) (x i j)))‖ ≤ 1/(2:ℝ)^(50*k i) := by
  intro large hm sparse norm overhead setup input output
  let s i := (bits i).card
  let pos i := gatherPerm (bits i)
  let v i := lift (gatherInput (pos i) (x i))
  have routeLarge i : K₀ ≤ k i := (le_max_left ..).trans (large i)
  have geomLarge i : SparseCutoff.threshold G W ≤ k i := (le_max_left ..).trans ((le_max_right ..).trans (large i))
  have numLarge i : precisionCutoff M ≤ k i := (le_max_right ..).trans ((le_max_right ..).trans (large i))
  have geom i := SparseCutoff.geometry (a+1) hw (geomLarge i) hg cap (sparse i)
  have guards i := accurate_of_cutoff ha hw p correct factor (numLarge i) (bits i) (pos i)
    (gatherPerm_low (bits i)) (x i) (norm i)
  have grouped := Pieces.sparseGroupedPass hw p ha hr hc hP release k s v (fun i => (geom i).1)
    (fun i => (geom i).2) (fun i => (guards i).1) hg hH hQ sparse overhead setup
  have task := selectedTaskOfGrouped hw p hr.le route k bits mask x routeLarge hm grouped.1
  exact ⟨task,task.releaseOfSpaceLeTime (fun i => Pieces.space_le_clock hr.le (k i)),fun i => (guards i).2⟩

end
end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
