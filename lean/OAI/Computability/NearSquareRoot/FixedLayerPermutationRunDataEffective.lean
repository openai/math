import OAI.Computability.NearSquareRoot.FixedLayerPermutationRunData
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectivePlaced
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepFootprint
import OAI.Computability.NearSquareRoot.SynchronizedPermutationPointFinite

/-! # Effective raw Fourier batches with measured time and workspace -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking EffectiveBoundedTask
open SynchronizedPermutationBudget Controlled.PositionProgram
open Benes.PackedBatchHeader (PassPoint)

variable {P : Type} [Primcodable P] {I : P → Type}
  (n : (p : P) → I p → ℕ) (h : ∀ p i, Directory (n p i)) (dir : (p : P) → I p → Bool)
  (D : P → ℕ) (hd : ∀ p i, 4 ≤ (box (n p i)).length) (hn : ∀ p i, 2 ≤ n p i)
  (big : ∀ p i, BoxPasses (addressBits (n p i)) (D p) 2)

abbrev BatchState (p : P) := PermutationBatch (n p) (h p) (dir p)

abbrev BatchState.operand {p : P} (z : BatchState n h dir p) := n p z.1.val.instanceIndex

/-- Restrict the physical command for one candidate to its own declared reserve.
Each value still contains its actual switch tables, address widths and coefficients. -/
abbrev NativePass (D : ℕ) := {s : PassPoint.Input // s.1.D = D}

def BatchState.sample {p : P} (z : BatchState n h dir p) : NativePass (D p) :=
  ⟨z.input (hd p) (big p),rfl⟩

abbrev NativeMeasured (D : P → ℕ) (t s : (p : P) → NativePass (D p) → ℕ) :=
  Family t s (fun _ z => .fork (send z.val.1.descriptor) (PassPoint.beads z.val))
    (fun _ z => PassPoint.beads (PassPoint.move z.val))

include hn in
/-- Use the actual native command and retain its measured budget on every
tuple. The fixed input and output conversions account for one operand scan. -/
theorem placedBatchFromMeasurements
    (t s : (p : P) → NativePass (D p) → ℕ) (native : NativeMeasured D t s)
    (tick arena : P → ℕ → ℕ) (ct cs : P → ℕ)
    (ht : ∀ p (z : BatchState n h dir p), let N := n p z.1.val.instanceIndex
      t p (BatchState.sample n h dir D hd big z)+N+1 ≤ ct p*(tick p N+1))
    (hs : ∀ p (z : BatchState n h dir p), let N := n p z.1.val.instanceIndex
      max (s p (BatchState.sample n h dir D hd big z)) N+1 ≤ cs p*(arena p N+1)) :
    PlacedBatchFamily n h dir D hd arena tick := by
  let Z := BatchState n h dir
  let N p (z : Z p) := n p z.1.val.instanceIndex
  let rank p (z : Z p) := z.rank (hd p)
  let pick p (z : Z p) := BatchState.sample n h dir D hd big z
  let header p (z : Z p) := send (z.descriptor (D p))
  let x p (z : Z p) := z.current (hd p)
  let y p (z : Z p) := z.after (hd p)
  choose K hK using fun p => PermutationBatch.descriptor_size (n p) (h p) (dir p) (hn p) (D p)
  have inner : Family (fun p z => t p (pick p z)) (fun p z => s p (pick p z))
      (fun p z => .fork (header p z) (batchCloth (N p) (rank p) (x p) z))
      (fun p => batchCloth (N p) (rank p) (y p)) := by
    apply (native.on pick).conform (fun _ _ => rfl) (fun _ _ => rfl)
    · intro p z
      exact congrArg (Tree.fork (header p z)) (PermutationBatch.input_beads z (hd p) (big p))
    · exact fun p z => PermutationBatch.move_beads z (hd p) (big p)
  have raw := fromNativeBatchFamily N (fun p z => hn p z.1.val.instanceIndex) rank header K hK x y _ _ inner
  exact CRTStream.familyBound (t' := fun p z => tick p (N p z)) (s' := fun p z => arena p (N p z))
    raw ct cs ht hs

/-- Cost of the physical table, including its actual payload, on a single pass. -/
def nativeWork (η : ℝ) (x : PassPoint) :=
  x.volumeB * (positionFactor η x.k + rowFactor x.k η + 1)

private def extend {D : ℕ} (m : NativePass D → ℕ) (u : PassPoint.Input) :=
  if hD : u.1.D = D then m ⟨u,hD⟩ else 0

/-- Even an inaccurate candidate has a finite measured budget on each operand
width. The maximum ranges over all possible coefficient values and pass indices. -/
def passMaximum {D : ℕ} (m : NativePass D → ℕ) (N : ℕ) :=
  PassPoint.maximumAt (addressBits N) D (extend m)

theorem le_passMaximum {D N : ℕ} (m : NativePass D → ℕ) (u : NativePass D)
    (hk : u.val.1.k = addressBits N) : m u ≤ passMaximum m N := by
  have hi := PassPoint.le_maximumAt (extend m) u.val
  simpa only [passMaximum,hk,u.property,extend,dite_eq_left,Subtype.coe_eta] using hi

private theorem overhead {a N v C : ℕ} (bound : a ≤ C*(v+1)) (size : N ≤ v) :
    a+N+1 ≤ (C+1)*(v+1) := by rw [Nat.add_mul,Nat.one_mul]; omega

include hn in
/-- Choose width-only time and workspace profiles for every generated candidate.
Good widths attain the native clock and original-input workspace. Other widths
use the actual finite maxima of the supplied program's time and workspace. -/
theorem placedBatchProfiles (η : P → ℝ) (good : P → ℕ → Prop)
    (t s : (p : P) → NativePass (D p) → ℕ) (native : NativeMeasured D t s)
    (T S : P → ℕ)
    (ht : ∀ p (z : BatchState n h dir p), good p (n p z.1.val.instanceIndex) →
      let u := BatchState.sample n h dir D hd big z
      t p u ≤ T p*(nativeWork (η p) u.val.1+1))
    (hs : ∀ p (z : BatchState n h dir p), good p (n p z.1.val.instanceIndex) →
      let u := BatchState.sample n h dir D hd big z
      s p u ≤ S p*(u.val.1.volumeB+1)) :
    ∃ tick arena : P → ℕ → ℕ, PlacedBatchFamily n h dir D hd arena tick ∧
      (∀ p N, N ≤ arena p N) ∧
      ∀ p N, good p N → tick p N = nativeTick (η p) N ∧ arena p N = N := by
  classical
  let tick p N := if good p N then nativeTick (η p) N else passMaximum (t p) N+N
  let arena p N := if good p N then N else max (passMaximum (s p) N) N
  refine ⟨tick,arena,?_,?_,?_⟩
  · apply placedBatchFromMeasurements n h dir D hd hn big t s native tick arena (fun p => T p+1)
      (fun p => S p*73729+1)
    · intro p z
      let N := n p z.1.val.instanceIndex
      let u := BatchState.sample n h dir D hd big z
      change t p u+N+1 ≤ (T p+1)*(tick p N+1)
      by_cases ok : good p N
      · rw [show tick p N = nativeTick (η p) N by simp [tick,ok]]
        have price : nativeWork (η p) u.val.1 ≤ nativeTick (η p) N :=
          (Nat.mul_le_mul_right _ (PermutationBatch.volume_le_grid z (hd p) (big p))).trans
            (Nat.le_add_right ..)
        exact overhead ((ht p z ok).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ price)))
          (Nat.le_add_left ..)
      · rw [show tick p N = passMaximum (t p) N+N by simp [tick,ok]]
        have cap := le_passMaximum (t p) u (N := N) rfl
        exact (by omega : t p u+N+1 ≤ passMaximum (t p) N+N+1).trans
          (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    · intro p z
      let N := n p z.1.val.instanceIndex
      let u := BatchState.sample n h dir D hd big z
      change max (s p u) N+1 ≤ (S p*73729+1)*(arena p N+1)
      by_cases ok : good p N
      · rw [show arena p N = N by simp [arena,ok]]
        have vol := (PermutationBatch.volume_le_grid z (hd p) (big p)).trans
          (gridVolume_le (hn p z.1.val.instanceIndex))
        change u.val.1.volumeB ≤ 73728*N at vol
        have size : u.val.1.volumeB+1 ≤ 73729*(N+1) := by omega
        have bound := (hs p z ok).trans (Nat.mul_le_mul_left (S p) size)
        rw [← Nat.mul_assoc] at bound
        change s p u ≤ S p*73729*(N+1) at bound
        exact (Nat.succ_le_succ (max_le (Nat.le_add_right (s p u) N) (Nat.le_add_left N (s p u)))).trans
          (overhead bound (N := N) le_rfl)
      · rw [show arena p N = max (passMaximum (s p) N) N by simp [arena,ok]]
        have cap := le_passMaximum (s p) u (N := N) rfl
        exact (Nat.succ_le_succ (max_le_max_right N cap)).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  · intro p N
    by_cases ok : good p N <;> simp [arena,ok]
  · intro p N ok
    simp [tick,arena,ok]

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
