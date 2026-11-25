import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepDispatch
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineEstimate

/-! # Size of each compiled header in the live Fourier permutation directory -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer.PermutationBatch

open IntegerMultiplication Code FixedCandidate FixedPoint DigitPacking ShortFourier.BatchWord

/-- The same linear bound applies to every actual header and array ordering
encountered during the sweep. Its constant may depend on the reserve exponent. -/
theorem descriptor_size {I : Type} (n : I → ℕ) (h : ∀ i, Directory (n i)) (dir : I → Bool)
    (hn : ∀ i, 2 ≤ n i) (D : ℕ) :
    ∃ C, ∀ z : PermutationBatch n h dir, size (descriptor z D) ≤ C*(n z.1.val.instanceIndex+1) := by
  let J := PermutationRow n h dir
  let ix (e : J) := e.val.instanceIndex
  let key (q : Benes.PackedBatchHeader.RowPass) := Benes.PackedBatchHeader.placedHeader (tally D,q)
  obtain ⟨⟨C,cap⟩,_⟩ := preparePermutationTicket key (Benes.PackedBatchHeader.placedHeader_fixed D)
    (fun e : J => n (ix e)) (fun e => hn (ix e)) (fun e => dir (ix e)) (fun e => e.val.position)
  refine ⟨C,fun z => ?_⟩
  have bound := AffineAddress.forest_member_count (fun a => send (key (z.1.key,PermDirectory.batchTicket a)))
    _ z.2.1.val z.2.1.property
  exact bound.trans (cap z.1)

end FixedLayer.PermutationBatch

end NearSquareRoot
end Computability
end OAI
