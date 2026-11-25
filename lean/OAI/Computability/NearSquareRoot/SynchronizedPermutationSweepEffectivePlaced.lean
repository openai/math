import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveBranch
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveKernel
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveTicket
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepDispatch

/-! # The generated Fourier opcode from one placed-batch command family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
noncomputable section

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint DigitPacking EffectiveBoundedTask FixedLayerTickets
open ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram BoxFin PermutationSweep
open Benes.PackedBatchHeader (placedHeader placedHeader_poly)
open SynchronizedPermutationBudget (order)

variable {P : Type} [Primcodable P] {I : P → Type}
  (n : ∀ p, I p → ℕ) (h : ∀ p i, Directory (n p i)) (dir : ∀ p, I p → Bool)

/-- The callback consumes a true placed header, which contains readable geometry, two
relocation tables, and the switch plan. Its stream consists of the actual records
at their current positions after the preceding passes. -/
def PlacedBatchFamily (D : P → ℕ) (hd : ∀ p i, 4 ≤ (box (n p i)).length) (arena tick : P → ℕ → ℕ) : Prop :=
  Family (fun p (z : PermutationBatch (n p) (h p) (dir p)) => tick p (n p z.1.val.instanceIndex))
    (fun p z => arena p (n p z.1.val.instanceIndex))
    (fun p z => .fork (send (z.descriptor (D p))) (z.array (hd p) (z.current (hd p))))
    (fun p z => z.array (hd p) (z.after (hd p)))

/-- Run the placed-batch program at every chronological directory entry and return
the exact natural-order Fourier permutation output. Failed cost guesses may use a
larger workspace; the arena used by each command is measured on its executed run. -/
theorem effectivePermutationFromPlacedBatchesAt (D : P → ℕ) (eff : Computable D)
    (hd : ∀ p i, 4 ≤ (box (n p i)).length) (hn : ∀ p i, 2 ≤ n p i)
    (room : ∀ p i, 8*SynchronizedPermutationBudget.width (addressBits (n p i)) ≤ addressBits (n p i))
    (arena clock tick : P → ℕ → ℕ) (fit : ∀ p i, n p i ≤ arena p (n p i))
    (hc : ∀ p i, n p i ≤ clock p (n p i)) (C : P → ℕ)
    (rate : ∀ p i, (order (addressBits (n p i)) ((box (n p i)).length/4)).length * tick p (n p i) ≤
      C p*(clock p (n p i)+1))
    (kernel : PlacedBatchFamily n h dir D hd arena tick) :
    EffectiveImplementsAt n h dir hd arena clock .permutation := by
  let J p := PermutationRow (n p) (h p) (dir p)
  let ix p (e : J p) := e.val.instanceIndex
  let num p (e : J p) := n p (ix p e)
  let val p (e : J p) : Directory (num p e) := h p (ix p e)
  let mods p (e : J p) := modulus_neZero (val p e)
  let dir' p (e : J p) := dir p (ix p e)
  let pos p (e : J p) := e.val.position
  have pre := preparePermutationTicketFamily placedHeader placedHeader_poly D eff num
    (fun p e => hn p (ix p e)) dir' pos
  have all := effectivePermutationFromBatchesAt (fun p z => placedHeader (tally (D p),z)) num
    (fun p e => hn p (ix p e)) val (fun p e => hd p (ix p e)) dir' pos (fun _ e => PermutationRow.tag e)
    (fun p e => room p (ix p e)) (fun _ e => e.val.payload)
    (fun p e => arena p (num p e)) (fun p e => clock p (num p e)) (fun p e => tick p (num p e))
    (fun p e => fit p (ix p e)) (fun p e => hc p (ix p e)) C (fun p e => rate p (ix p e)) pre kernel
  apply effectivePermutationFromTicketsAt n h dir hd arena clock hn hc fit
  apply all.conform (fun _ _ => rfl) (fun _ _ => rfl) _ (fun _ _ => rfl)
  intro p e
  change Tree.fork (send (phaseStageTicket _ _ _ _)) (send (FixedCandidate.records _)) =
    Tree.fork (send (e.val.ticket (n p) (h p) (dir p))) (send (FixedCandidate.records _))
  rw [RowInput.ticket,header_at]
  rfl

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
