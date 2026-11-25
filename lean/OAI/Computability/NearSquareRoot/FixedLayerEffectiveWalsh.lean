import OAI.Computability.NearSquareRoot.FixedLayerEffectiveDispatch
import OAI.Computability.NearSquareRoot.PhysicalBoxWalshAccuracy
import OAI.Computability.NearSquareRoot.PhysicalBoxWalshFamily

/-! # The selected Walsh command on the row dispatcher's typed inputs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1200000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint FixedLayerTickets DigitPacking
  ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram
  PhysicalWalsh PhysicalWalshNode PhysicalWalsh.GatherProgram KernelPass EffectiveBoundedTask

variable {P : Type} [Primcodable P] {I : P → Type}
  (n : ∀ p, I p → ℕ) (hv : ∀ p i, Directory (n p i)) (dir : ∀ p, I p → Bool)

/-- A dispatcher input whose chronological row carries the Walsh opcode. -/
abbrev WalshRowInput (p : P) :=
  {e : RowInput (n p) (hv p) (dir p) // HasKind (n p) (hv p) (dir p) .walsh e}

/-- The raw selected pass reads the flags of the actual schedule row and
returns its rounded output in address order. -/
def SelectedRowFamily {a W : P → ℕ} (ρ : P → ℝ) (hw : ∀ p, 0 < W p)
    (plan : ∀ p, Plan (a p+1) (W p) (W p)) : Prop :=
  Family (fun p (e : WalshRowInput n hv dir p) => Pieces.sparseTime (ρ p) (addressBits (n p e.val.instanceIndex)))
    (fun p e => Pieces.sparseSpace (addressBits (n p e.val.instanceIndex)))
    (fun p e => send (flags (walshBits (hv p e.val.instanceIndex) (dir p e.val.instanceIndex)
      e.val.position.val e.val.position.isLt), Odd.words e.val.payload))
    (fun p e => send (Odd.words (walshRowOutput (hw p) (plan p) (hv p e.val.instanceIndex)
      (dir p e.val.instanceIndex) e.val.position.val e.val.position.isLt e.val.payload)))

/-- Frame a generated selected-pass command and identify its numerical
output with the actual Walsh matrix on the caller's Fourier axes. -/
theorem effectiveWalsh_of_selectedFamily
    (hd : ∀ p i, 4 ≤ (box (n p i)).length) (hn : ∀ p i, 2 ≤ n p i)
    (clock : P → ℕ → ℕ) (lin : ∀ p i, n p i ≤ clock p (n p i)) (ρ : P → ℝ)
    (room : ∀ p i, Pieces.sparseTime (ρ p) (addressBits (n p i)) ≤ clock p (n p i))
    {a W M : P → ℕ} (hw : ∀ p, 0 < W p) (plan : ∀ p, Plan (a p+1) (W p) (W p))
    (ha : ∀ p, 1 < a p+1) (correct : ∀ p, Correct (plan p))
    (hc : ∀ p, recursionFactor (plan p) ≤ M p)
    (hk : ∀ p i, precisionCutoff (M p) ≤ addressBits (n p i))
    (raw : SelectedRowFamily n hv dir ρ hw plan) : EffectiveImplements n hv dir hd clock .walsh := by
  let idx p (e : WalshRowInput n hv dir p) := e.val.instanceIndex
  let out p (e : WalshRowInput n hv dir p) := walshRowOutput (hw p) (plan p) (hv p (idx p e))
    (dir p (idx p e)) e.val.position.val e.val.position.isLt e.val.payload
  refine ⟨out,?_,?_⟩
  · have run := walshMaskFamilyFrames (fun p e => n p (idx p e)) (fun _ e => e.val.position.val)
      (fun p e => dir p (idx p e)) (fun p e => hn p (idx p e)) (fun p e => hv p (idx p e))
      (fun _ e => e.val.position.isLt) ρ clock (fun p e => lin p (idx p e))
      (fun p e => room p (idx p e)) (fun _ e => e.val.payload) out raw
    apply run.conform (fun _ _ => rfl) (fun _ _ => rfl) _ (fun _ _ => rfl)
    intro p e
    change .fork (send _) (framed _) =
      Tree.fork (send (e.val.ticket (n p) (hv p) (dir p))) (framed _)
    exact congrArg (fun t : Ticket => Tree.fork (send t) (framed e.val.payload))
      (header_at _ e.val.position).symm
  · intro p e
    have tag : (directedPlan (rowKey (n p) (dir p) (idx p e)))[e.val.position.val].2.1 = kindCode .walsh := by
      simpa only [HasKind,RowInput.ticket,header_at] using e.property
    exact walshRowOutput_accurate (hw p) (plan p) (ha p) (correct p) (hc p) (hk p (idx p e))
      (hv p (idx p e)) (hd p (idx p e)) (dir p (idx p e)) _ e.val.position.isLt tag e.val.payload e.val.inRange

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
