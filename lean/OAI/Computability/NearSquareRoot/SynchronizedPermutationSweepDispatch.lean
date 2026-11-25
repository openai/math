import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepKernel
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepGeometryRow

/-! # Completing the permutation branch from its native batched switch command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 2200000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking FixedLayerTickets
open ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram BoxFin PermutationSweep
open SynchronizedPermutationBudget (order)
open Benes (PackedAddress)

variable {I : Type} (n : I → ℕ) (h : ∀ i, Directory (n i)) (dir : I → Bool)

/-- Valid input row at the permutation branch of the two-bit decoder. -/
abbrev PermutationRow := {e : RowInput n h dir // HasKind n h dir .permutation e}

namespace PermutationRow

variable {n h dir}

def key (e : PermutationRow n h dir) : PermDirectory.Query :=
  (dir e.val.instanceIndex,tally (addressBits (n e.val.instanceIndex)),tally e.val.position.val)

theorem tag (e : PermutationRow n h dir) :
    (directedPlan (rowKey n dir e.val.instanceIndex))[e.val.position.val].2.1 = kindCode .permutation := by
  simpa only [HasKind,RowInput.ticket,header_at] using e.property

end PermutationRow

/-- Actual directory call, including the current location of every coefficient
after previous passes. -/
abbrev PermutationBatch :=
  (e : PermutationRow n h dir) ×
    {a // a ∈ order (addressBits (n e.val.instanceIndex)) ((box (n e.val.instanceIndex)).length/4)} ×
    Equiv.Perm (PackedAddress Unit (physicalWidth (box := box (n e.val.instanceIndex))))

namespace PermutationBatch

variable {n h dir} (z : PermutationBatch n h dir)

def descriptor (D : ℕ) : Benes.PackedBatchHeader.PlacedHeader :=
  Benes.PackedBatchHeader.placedHeader (tally D, z.1.key, PermDirectory.batchTicket z.2.1.val)

def switch :=
  let e := z.1
  let k := addressBits (n e.val.instanceIndex)
  let w := physicalWidth (box := box (n e.val.instanceIndex))
  let a := z.2.1.val
  Benes.batchStage (fun b => b.val / SynchronizedPermutationBudget.capacity k) w
    (fun _ : Unit => PermDirectory.switchTable (dir e.val.instanceIndex) e.val.position.val) a.1 a.2

variable (hd : ∀ i, 4 ≤ (box (n i)).length)

def rank :=
  let e := z.1
  let _ := modulus_neZero (h e.val.instanceIndex)
  packedRecord (h e.val.instanceIndex) (hd e.val.instanceIndex)

def current := Benes.scatter z.2.2 (z.1.val.payload ∘ (rank z hd).symm)
def after := Benes.scatter (switch z) (current z hd)

def array (a : PackedAddress Unit (physicalWidth (box := box (n z.1.val.instanceIndex))) →
    Record (addressBits (n z.1.val.instanceIndex))) := tapeArray (rank z hd) (fun v => send (Dusk.mark v)) a

end PermutationBatch

/-- Once the indicated single native command is installed, the actual ticket
dispatcher implements every permutation row of the forward and adjoint words. -/
theorem permutationOfPlacedBatch (D : ℕ) (hd : ∀ i, 4 ≤ (box (n i)).length)
    (hn : ∀ i, 2 ≤ n i) (room : ∀ i, 8*SynchronizedPermutationBudget.width (addressBits (n i)) ≤ addressBits (n i))
    (clock tick : ℕ → ℕ) (hc : ∀ i, n i ≤ clock (n i)) (C : ℕ)
    (rate : ∀ i, (order (addressBits (n i)) ((box (n i)).length/4)).length*tick (n i) ≤ C*(clock (n i)+1))
    (kernel : BoundedTask (fun z : PermutationBatch n h dir => tick (n z.1.val.instanceIndex))
      (fun z => n z.1.val.instanceIndex)
      (fun z => Tree.fork (send (PermutationBatch.descriptor z D))
        (PermutationBatch.array z hd (PermutationBatch.current z hd)))
      (fun z => PermutationBatch.array z hd (PermutationBatch.after z hd))) :
    Implements n h dir hd clock .permutation := by
  let J := PermutationRow n h dir
  let ix (e : J) := e.val.instanceIndex
  let n' (e : J) := n (ix e)
  let h' (e : J) : Directory (n' e) := h (ix e)
  let mods (e : J) := modulus_neZero (h' e)
  have raw := permutationFromBatches (fun a => Benes.PackedBatchHeader.placedHeader (tally D,a))
    (Benes.PackedBatchHeader.placedHeader_fixed D) n' (fun e => hn (ix e)) h' (fun e => hd (ix e))
    (fun e => dir (ix e)) (fun e => e.val.position) (fun e => PermutationRow.tag e)
    (fun e => room (ix e)) (fun e => e.val.payload) (fun e => clock (n' e)) (fun e => tick (n' e))
    (fun e => hc (ix e)) C (fun e => rate (ix e)) kernel
  apply permutationFromTickets n h dir hd clock hn hc
  apply raw.conform (fun _ => rfl) (fun _ => rfl) _ (fun _ => rfl)
  intro e
  change Tree.fork (send (phaseStageTicket _ _ _ _)) (send (FixedCandidate.records _)) =
    Tree.fork (send (e.val.ticket n h dir)) (send (FixedCandidate.records _))
  rw [RowInput.ticket,header_at]
  rfl

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
