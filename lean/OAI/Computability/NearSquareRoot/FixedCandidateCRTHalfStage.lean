import OAI.Computability.NearSquareRoot.FixedCandidateCRTHalfStageModel
import OAI.Computability.NearSquareRoot.FixedCandidateCRTHalfStageBounds

/-! # One complete native CRT half-stage from its generated guarded batches -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream.Half
open IntegerMultiplication Code DigitPacking FixedPoint Space

noncomputable section
variable {I : Type} (n : I → ℕ) (hs : ∀ i, Directory (n i)) (inv : Bool) (hn : ∀ i, 2 ≤ n i)

include hs hn in
theorem forestCap :
    ∃ C : ℕ, ∀ x : Input n inv, (forest n inv x).count ≤ C*(n x.1+1) := by
  let dir := CRTDispatch.directory CRTDispatch.low
  have P := CRTDispatch.directory_poly _ CRTDispatch.low_poly
  obtain ⟨C,H⟩ := setupCap (n := fun x : Input n inv => n x.1) (fun x => hn x.1)
    (fun x => size (dir (seed inv x.2.1.val)))
    (((P.length.map (fun x : Input n inv => seed inv x.2.1.val))).sub (seedSizeDom n inv))
  exact ⟨C,fun x => (congrArg Tree.count (directory_forest (hs x.1) inv x.2.1.val CRTDispatch.low)).le.trans (H x)⟩

include hn in
/-- Expand the stage seed to its physical directory while leaving the packed
coefficient rows on the same tape. The temporary arena is linear in operand length. -/
theorem boot :
    BoundedTask (fun x : Input n inv => n x.1) (fun x => n x.1) (beforeStage n hs inv)
      (fun x => .fork (forest n inv x) (original n hs inv x)) := by
  let jobs := CRTDispatch.directory CRTDispatch.low
  have P := CRTDispatch.directory_poly _ CRTDispatch.low_poly
  have short := seedSizeDom n inv
  obtain ⟨t,sc,run⟩ := P.on short
  obtain ⟨T,ht⟩ := setupCap (n := fun x : Input n inv => n x.1) (fun x => hn x.1) _ sc
  obtain ⟨S,hS⟩ := setupCap (n := fun x : Input n inv => n x.1) (fun x => hn x.1) _ short
  have gen := (BoundedTask.of_time run).left (original n hs inv)
  refine (gen.bound (T+1) (T+S+75001) (fun x => ?_) (fun x => ?_)).conform
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun x => ?_)
  · have := ht x
    rw [Nat.add_mul]
    omega
  · have sizeH := hS x
    have timeH := ht x
    have dataH := packedRows_size (hn x.1) (hs x.1) x.2.1.val (pack (hs x.1) x.2.1.val x.2.2)
    change size (seed inv x.2.1.val) + t x + (original n hs inv x).count + 1 ≤ _
    change (original n hs inv x).count ≤ 75000*(n x.1+1) at dataH
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at *
    omega
  · exact congrArg (fun v => Tree.fork v (original n hs inv x)) (directory_forest (hs x.1) inv x.2.1.val _).symm

private theorem major (c z u : ℕ) : z+c*(u+1)+1 ≤ (c+1)*(z+u+1) := by
  rw [Nat.succ_mul]
  have m := Nat.mul_le_mul_left c (show u+1 ≤ z+u+1 by omega)
  omega

include hn in
/-- Each call may receive an arbitrary current address permutation. Only the
per-batch time is multiplied by the batch count. All calls reuse one arena. -/
theorem nativeStage (hcap : ∀ i, 0 < CRTDispatch.Cap (addressBits (n i)))
    (tick work : ℕ → ℕ)
    (kernel : BoundedTask (fun z : KernelIndex n inv => tick (n z.1.1)) (fun z => work (n z.1.1))
      (before n hs inv) (after n hs inv)) :
    BoundedTask (fun x : Input n inv => CRTBudget.batches (addressBits (n x.1))*tick (n x.1)+n x.1)
      (fun x => work (n x.1)+n x.1) (beforeStage n hs inv) (afterStage n hs inv) := by
  obtain ⟨D,hD⟩ := forestCap n hs inv hn
  let V (x : Input n inv) := (D+75000)*(n x.1+1)
  let X := Input n inv
  have raw := PermutationSweep.halfStage
    (fun x : X => widths x.2.1.val) (fun x => tables (hs x.1) inv x.2.1.val)
    (fun x => which x.2.1.val) (fun x => x.2.1.val.2)
    (fun x => CRTBudget.batches (addressBits (n x.1))) (fun x r => targetBatch_lt (hcap x.1) x.2.1.val r)
    (fun x => key inv x.2.1.val) (fun x => packedRows (hs x.1) x.2.1.val)
    (fun x => pack (hs x.1) x.2.1.val x.2.2) (fun x => tick (n x.1)) V (fun x => work (n x.1))
    kernel (fun x => (hD x).trans (Nat.mul_le_mul_right _ (Nat.le_add_right D 75000)))
    (fun x u => (packedRows_size (hn x.1) (hs x.1) x.2.1.val _).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_left 75000 D)))
  let T (x : X) := CRTBudget.batches (addressBits (n x.1))*tick (n x.1)+n x.1
  let S (x : X) := work (n x.1)+n x.1
  have sweep := raw.bound (time' := T) (space' := S) (D+75001) (D+75001)
    (fun x => major (D+75000) _ _) (fun x => (by simpa only [Nat.add_comm (V x) _] using major (D+75000) (work (n x.1)) (n x.1)))
  exact sequence ((boot n hs inv hn).mono (fun _ => Nat.le_add_left ..) (fun _ => Nat.le_add_left ..)) sweep


/-- The batch clock and one extra copy of the operand fit the paper's
half-stage clock. -/
theorem stageBudget (ρ : ℝ) (deg u : ℕ) (hu : 2 ≤ u) :
    CRTBudget.batches (addressBits u) * CRTBudget.batchClock ρ (addressBits u) (CRTBudget.volume u) + u ≤
      CRTBudget.stageClock ρ deg u := by
  let k := addressBits u
  let t := CRTBudget.batchClock ρ k (CRTBudget.volume u)
  have ht : u ≤ t := (CRTBudget.input_le_volume hu).trans (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _))
  change CRTBudget.batches k*t+u ≤ (CRTBudget.batches k+1)*(t+(k+1)^deg)
  calc
    _ ≤ (CRTBudget.batches k+1)*t := by rw [Nat.succ_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_right ..)

include hn in
/-- A family of guarded batch calls with its physical bit-volume peak suffices
for the candidate's actual native half-stage. -/
theorem paperStage (hcap : ∀ i, 0 < CRTDispatch.Cap (addressBits (n i))) (ρ : ℝ) (deg : ℕ)
    (kernel : BoundedTask
      (fun z : KernelIndex n inv => CRTBudget.batchClock ρ (addressBits (n z.1.1)) (CRTBudget.volume (n z.1.1)))
      (fun z => CRTBudget.volume (n z.1.1)) (before n hs inv) (after n hs inv)) :
    BoundedTask (fun x : Input n inv => CRTBudget.stageClock ρ deg (n x.1)) (fun x => n x.1)
      (beforeStage n hs inv) (afterStage n hs inv) := by
  have run := nativeStage n hs inv hn hcap
    (fun u => CRTBudget.batchClock ρ (addressBits u) (CRTBudget.volume u)) CRTBudget.volume kernel
  apply run.bound 1 9698
  · intro x
    simpa only [Nat.one_mul] using Nat.succ_le_succ (stageBudget ρ deg (n x.1) (hn x.1))
  · intro x
    have hv := CRTBudget.volume_le_linear (hn x.1)
    omega

include hn in
/-- Passing the generated half-stage to the outer sweep gives the full
forward or inverse CRT route on the original framed coefficient array. -/
theorem nativeSweep (hcap : ∀ i, 0 < CRTDispatch.Cap (addressBits (n i))) (ρ : ℝ) (deg : ℕ)
    (kernel : BoundedTask
      (fun z : KernelIndex n inv => CRTBudget.batchClock ρ (addressBits (n z.1.1)) (CRTBudget.volume (n z.1.1)))
      (fun z => CRTBudget.volume (n z.1.1)) (before n hs inv) (after n hs inv)) :
    StreamPass n (CRTBudget.routeClock ρ deg) (fun i => outcome (hs i) inv) :=
  CRTStream.nativeSweep n inv hs hn (CRTBudget.stageClock ρ deg) (paperStage n hs inv hn hcap ρ deg kernel)

end
end FixedCandidate.CRTStream.Half

end NearSquareRoot
end Computability
end OAI
