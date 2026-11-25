import OAI.Computability.NearSquareRoot.FixedCandidateCRTHalfStage
import OAI.Computability.NearSquareRoot.FixedCandidateCRTEffectiveNative
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveStages

/-! # Effective CRT half-stage and full native sweep

The uniform emitter uses the batch command of its candidate for every entry of the
generated directory. Building that directory and traversing the packed array cost
linear overhead per half-stage. Each batch reuses the same scratch space.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream.Half
open IntegerMultiplication Code DigitPacking FixedPoint EffectiveBoundedTask
open NearSquareRoot.CRTTable

noncomputable section

variable {P : Type} [Primcodable P] {I : P → Type}

private theorem enlarge (c a b : ℕ) :
    a + c * (b+1) + 1 ≤ (c+2) * (a+b+1) := by
  have h := Nat.mul_le_mul_left c (show b+1 ≤ a+b+1 by omega)
  rw [Nat.add_mul]
  omega

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2400000 in
/-- Compiles a complete packed Beneš half-stage, including the CRT directory
computed from the short input seed. The batch emitter may depend on the
candidate; its register bound applies to the full family. -/
theorem family (n : (p : P) → I p → ℕ) (valid : ∀ p i, Directory (n p i))
    (hn : ∀ p i, 2 ≤ n p i) (hcap : ∀ p i, 0 < CRTDispatch.Cap (addressBits (n p i)))
    (inv : Bool) (tick arena : P → ℕ → ℕ)
    (kernel : Family (fun p (z : KernelIndex (n p) inv) => tick p (n p z.1.1))
      (fun p z => arena p (n p z.1.1)) (fun p => before (n p) (valid p) inv)
      (fun p => after (n p) (valid p) inv)) :
    Family (fun p (x : Input (n p) inv) =>
        CRTBudget.batches (addressBits (n p x.1)) * tick p (n p x.1) + n p x.1)
      (fun p x => arena p (n p x.1) + n p x.1)
      (fun p => beforeStage (n p) (valid p) inv) (fun p => afterStage (n p) (valid p) inv) := by
  let X p := Input (n p) inv
  let N p (x : X p) := n p x.1
  let s p (x : X p) := x.2.1.val
  let B p (x : X p) := CRTBudget.batches (addressBits (N p x))
  let jointN (i : Sigma I) := n i.1 i.2
  let flatten (p : P) (x : X p) : Input jointN inv := ⟨⟨p,x.1⟩,x.2⟩
  obtain ⟨K,hK⟩ := forestCap jointN (fun i => valid i.1 i.2) inv (fun i => hn i.1 i.2)
  let V p (x : X p) := (K+75000)*(N p x+1)
  let tab p (x : X p) := key inv (s p x)
  let v p (x : X p) := pack (valid p x.1) (s p x) x.2.2
  let rows p (x : X p) := packedRows (valid p x.1) (s p x)
  have bootFamily := Family.joint (P := P) (I := X) (t := N) (s := N)
    (u := fun p => beforeStage (n p) (valid p) inv)
    (v := fun p x => .fork (Task.forest (tab p x) (List.range (B p x))) (rows p x (v p x)))
    ((boot jointN (fun i => valid i.1 i.2) inv (fun i => hn i.1 i.2)).on
      (fun z : Sigma X => flatten z.1 z.2))
  have sweep := PermutationSweep.halfStageFamily
    (fun p x => widths (s p x)) (fun p x => tables (valid p x.1) inv (s p x)) (fun p x => which (s p x))
    (fun p x => (s p x).2) B (fun p x => targetBatch_lt (hcap p x.1) (s p x))
    tab rows v (fun p x => tick p (N p x)) V (fun p x => arena p (N p x)) kernel
    (fun p x => (hK (flatten p x)).trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..)))
    (fun p x ψ => (packedRows_size (hn p x.1) _ _ _).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_left ..)))
  let T p (x : X p) := B p x * tick p (N p x) + N p x
  let S p (x : X p) := arena p (N p x) + N p x
  have run := familyBound (t' := T) (s' := S) sweep (fun _ => K+75000+2) (fun _ => K+75000+2)
    (fun _ _ => enlarge _ _ _) (fun p x => by
      rw [Nat.add_comm (V p x) (arena p (N p x))]
      exact enlarge (K+75000) (arena p (N p x)) (N p x))
  exact (bootFamily.mono (t' := T) (s' := S)
    (fun _ _ => Nat.le_add_left ..) (fun _ _ => Nat.le_add_left ..)).sequence run

/-- Execute every prepared depth and half-stage on the fixed candidate's two
framed streams, charging all of the setup and retaining the per-candidate arena. -/
theorem fullSweep (n : (p : P) → I p → ℕ) (valid : ∀ p i, Directory (n p i))
    (hn : ∀ p i, 2 ≤ n p i) (hcap : ∀ p i, 0 < CRTDispatch.Cap (addressBits (n p i)))
    (inv : Bool) (tick arena : P → ℕ → ℕ)
    (kernel : Family (fun p (z : KernelIndex (n p) inv) => tick p (n p z.1.1))
      (fun p z => arena p (n p z.1.1)) (fun p => before (n p) (valid p) inv)
      (fun p => after (n p) (valid p) inv)) :
    Family (fun p (y : (i : I p) × Array (n p i)) => count (n p y.1) *
        (CRTBudget.batches (addressBits (n p y.1))*tick p (n p y.1) + n p y.1 + n p y.1) + n p y.1)
      (fun p y => arena p (n p y.1) + n p y.1 + n p y.1)
      (fun _ y => framed y.2) (fun p y => framed (outcome (valid p y.1) inv y.2)) :=
  effectiveNativeSweep n valid hn inv (fun p u => CRTBudget.batches (addressBits u)*tick p u+u)
    (fun p u => arena p u+u) (family n valid hn hcap inv tick arena kernel)

/-- The emitted native batch family, when bounded by its bit-record volume,
gives an effective complete CRT route with the paper clock and linear arena. -/
theorem paperFamily (n : (p : P) → I p → ℕ) (valid : ∀ p i, Directory (n p i))
    (hn : ∀ p i, 2 ≤ n p i) (hcap : ∀ p i, 0 < CRTDispatch.Cap (addressBits (n p i)))
    (inv : Bool) (ρ : P → ℝ) (deg : P → ℕ)
    (kernel : Family (fun p (z : KernelIndex (n p) inv) =>
        CRTBudget.batchClock (ρ p) (addressBits (n p z.1.1)) (CRTBudget.volume (n p z.1.1)))
      (fun p z => CRTBudget.volume (n p z.1.1)) (fun p => before (n p) (valid p) inv)
      (fun p => after (n p) (valid p) inv)) :
    Family (fun p (y : (i : I p) × Array (n p i)) => CRTBudget.routeClock (ρ p) (deg p) (n p y.1))
      (fun p y => n p y.1) (fun _ y => framed y.2)
      (fun p y => framed (outcome (valid p y.1) inv y.2)) := by
  have run := fullSweep n valid hn hcap inv
    (fun p u => CRTBudget.batchClock (ρ p) (addressBits u) (CRTBudget.volume u)) (fun _ => CRTBudget.volume)
    kernel
  apply familyBound run (fun _ => 1) (fun _ => 9699)
  · intro p y
    simp only [Nat.one_mul, CRTBudget.routeClock]
    gcongr
    exact stageBudget (ρ p) (deg p) _ (hn p y.1)
  · intro p y
    have hv := CRTBudget.volume_le_linear (hn p y.1)
    omega

end
end FixedCandidate.CRTStream.Half

end NearSquareRoot
end Computability
end OAI
