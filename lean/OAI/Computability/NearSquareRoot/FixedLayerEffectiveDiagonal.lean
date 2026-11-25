import OAI.Computability.NearSquareRoot.FixedLayerEffectiveDispatch

/-! # One physical diagonal row command for all candidate parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space FixedLayerTickets
  DigitPacking ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram
open EffectiveBoundedTask

set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
noncomputable section

/-- The finite tape phase program acts on the union of all admissible rows.
Its code and register cutoff are independent of the family parameter. -/
theorem effectiveDiagonal {P : Type} [Primcodable P] {I : P → Type}
    (n : ∀ p, I p → ℕ) (hv : ∀ p i, Directory (n p i)) (dir : ∀ p, I p → Bool)
    (hd : ∀ p i, 4 ≤ (box (n p i)).length) (hn : ∀ p i, 2 ≤ n p i)
    (clock : P → ℕ → ℕ) (hl : ∀ p i, phaseClock (n p i) ≤ clock p (n p i)) :
    EffectiveImplements n hv dir hd clock .diagonal := by
  let J p := {e : RowInput (n p) (hv p) (dir p) // HasKind (n p) (hv p) (dir p) .diagonal e}
  let idx (z : Sigma J) := z.2.val.instanceIndex
  have tags (z : Sigma J) :
      ((directedPlan (rowKey (n z.1) (dir z.1) (idx z)))[z.2.val.position.val]).2.1 = kindCode .diagonal := by
    have h := z.2.property
    simpa only [HasKind,RowInput.ticket,header_at] using h
  obtain ⟨out,hr,he⟩ := phaseRowBranch (fun z : Sigma J => n z.1 (idx z)) (fun z => z.2.val.position.val)
    (fun z => dir z.1 (idx z)) (fun z => hn z.1 (idx z)) (fun z => hv z.1 (idx z))
    (fun z => hd z.1 (idx z)) (fun z => z.2.val.position.isLt) tags
    (fun z => z.2.val.payload) (fun z => z.2.val.inRange)
  refine ⟨fun p e => out ⟨p,e⟩,?_,fun p e => he ⟨p,e⟩⟩
  apply Family.joint
  apply (hr.mono (fun z => hl z.1 (idx z)) (fun _ => le_rfl)).conform
    (fun _ => rfl) (fun _ => rfl) _ (fun _ => rfl)
  intro z
  change .fork (send _) (framed _) = Tree.fork (send (z.2.val.ticket (n z.1) (hv z.1) (dir z.1))) (framed _)
  rw [RowInput.ticket,header_at]
  rfl

/-- The fixed phase row uses the requested common arena even when a parameter
family grants more than the linear input-space allowance. -/
theorem effectiveDiagonalAt {P : Type} [Primcodable P] {I : P → Type}
    (n : ∀ p, I p → ℕ) (hv : ∀ p i, Directory (n p i)) (dir : ∀ p, I p → Bool)
    (hd : ∀ p i, 4 ≤ (box (n p i)).length) (hn : ∀ p i, 2 ≤ n p i)
    (arena clock : P → ℕ → ℕ) (fit : ∀ p i, n p i ≤ arena p (n p i))
    (hl : ∀ p i, phaseClock (n p i) ≤ clock p (n p i)) :
    EffectiveImplementsAt n hv dir hd arena clock .diagonal := by
  obtain ⟨out,run,err⟩ := effectiveDiagonal n hv dir hd hn clock hl
  exact ⟨out,run.mono (fun _ _ => le_rfl) (fun p e => fit p e.val.instanceIndex),err⟩

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
