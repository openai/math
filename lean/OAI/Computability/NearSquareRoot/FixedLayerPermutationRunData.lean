import OAI.Computability.NearSquareRoot.FixedLayerPermutationRunPoint
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepBeads
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepExecute
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetNativeTick

/-! # The native switch on an actual Fourier interpreter batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxRecDepth 6000
set_option maxHeartbeats 1500000
noncomputable section
namespace FixedLayer
open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking ShortFourier.BatchWord
open Controlled.PositionProgram SynchronizedPermutationBudget
open Benes.PackedBatchHeader (PassPoint)

namespace PermutationBatch
variable {I : Type} {n : I → ℕ} {h : ∀ i, FixedCandidate.Directory (n i)} {dir : I → Bool}
  (z : PermutationBatch n h dir) (hd : ∀ i, 4 ≤ (box (n i)).length)
  {D : ℕ} (big : ∀ i, BoxPasses (addressBits (n i)) D 2)

/-- At this index the native routine sees all coefficient records as currently
ordered by earlier switches on the same Fourier row. -/
def input : PassPoint.Input := ⟨point z hd big,current z hd⟩

theorem input_beads : PassPoint.beads (input z hd big) =
    batchCloth (fun z : PermutationBatch n h dir => n z.1.val.instanceIndex)
      (fun z => rank z hd) (fun z => current z hd) z := rfl

theorem move_beads : PassPoint.beads (PassPoint.move (input z hd big)) =
    batchCloth (fun z : PermutationBatch n h dir => n z.1.val.instanceIndex)
      (fun z => rank z hd) (fun z => after z hd) z := rfl

theorem volume_le_grid : (point z hd big).volumeB ≤ gridVolume (n z.1.val.instanceIndex) := by
  apply Nat.mul_le_mul_left
  unfold componentBits
  change 2*(96*addressBits _ + 4 + 1) ≤ 384*addressBits _ + 23
  omega

end PermutationBatch

/-- The compiled switch consumes the dispatcher header and produces the marked
array on the actual input tape. Both conversions are included in the clock. -/
abbrev BatchKernel {I : Type} (η : ℝ) (D : ℕ) (n : I → ℕ) (h : ∀ i, Directory (n i))
    (dir : I → Bool) (hd : ∀ i, 4 ≤ (box (n i)).length) :=
  BoundedTask (fun z : PermutationBatch n h dir => nativeTick η (n z.1.val.instanceIndex))
    (fun z => n z.1.val.instanceIndex)
    (fun z => .fork (send (PermutationBatch.descriptor z D)) (PermutationBatch.array z hd (PermutationBatch.current z hd)))
    (fun z => PermutationBatch.array z hd (PermutationBatch.after z hd))

/-- After choosing one reserve cutoff, the generated command applies for every
sufficient reserve and every family of Fourier arrays. -/
theorem rawBatchKernelAt (η : ℝ) (lower : 1/2 < η) (upper : η ≤ 1) :
    ∃ d : ℕ, ∀ D ≥ d, ∀ {I : Type} (n : I → ℕ) (h : ∀ i, Directory (n i)) (dir : I → Bool)
      (hd : ∀ i, 4 ≤ (box (n i)).length) (_hn : ∀ i, 2 ≤ n i)
      (_big : ∀ i, BoxPasses (addressBits (n i)) D 2), BatchKernel η D n h dir hd := by
  obtain ⟨d,run⟩ := PassPoint.execute η lower upper
  refine ⟨d,fun D fit I n h dir hd hn big => ?_⟩
  let Z := PermutationBatch n h dir
  let idx (z : Z) := n z.1.val.instanceIndex
  let head (z : Z) := send (PermutationBatch.descriptor z D)
  let rank (z : Z) := z.rank hd
  let v (z : Z) := z.current hd
  let w (z : Z) := z.after hd
  let pick (z : Z) := z.input hd big
  let cost z := gridVolume (idx z)*(positionFactor η (addressBits (idx z))+rowFactor (addressBits (idx z)) η+1)
  have inner := run pick (fun _ => fit)
  have raw : BoundedTask cost idx (fun z => .fork (head z) (batchCloth idx rank v z)) (batchCloth idx rank w) := by
    apply (inner.bound (time' := cost) (space' := idx) 1 73728 _ _).conform (fun _ => rfl) (fun _ => rfl)
    · intro z
      exact congrArg (Tree.fork (head z)) (PermutationBatch.input_beads z hd big)
    · exact fun z => PermutationBatch.move_beads z hd big
    · intro z
      rw [Nat.one_mul]
      apply Nat.succ_le_succ
      exact Nat.mul_le_mul_right _ (PermutationBatch.volume_le_grid z hd big)
    · intro z
      have H := (PermutationBatch.volume_le_grid z hd big).trans (gridVolume_le (hn z.1.val.instanceIndex))
      change (z.point hd big).volumeB + 1 ≤ 73728*(n z.1.val.instanceIndex+1)
      omega
  exact fromNativeBatchLinear idx (fun z => hn z.1.val.instanceIndex) rank head v w cost raw

/-- The raw kernel contract consumed by the Fourier row dispatcher. -/
theorem rawBatchKernel (η : ℝ) (lower : 1/2 < η) (upper : η ≤ 1) :
    ∃ D : ℕ, ∀ {I : Type} (n : I → ℕ) (h : ∀ i, Directory (n i)) (dir : I → Bool)
      (hd : ∀ i, 4 ≤ (box (n i)).length) (_hn : ∀ i, 2 ≤ n i)
      (_big : ∀ i, BoxPasses (addressBits (n i)) D 2), BatchKernel η D n h dir hd := by
  obtain ⟨d,run⟩ := rawBatchKernelAt η lower upper
  exact ⟨d,fun n h dir hd hn big => run d le_rfl n h dir hd hn big⟩

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
