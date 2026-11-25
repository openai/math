import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepKernel
import OAI.Computability.NearSquareRoot.FixedCandidateCRTCloth
import OAI.Computability.NearSquareRoot.FixedCandidateCRTEffectiveSweep
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveRetain

/-! # Unframed Fourier record arrays and the native binary-address cloth -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer
open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking PermutationSweep
open PhysicalWalsh.PositionCloth
open private easyAt ties_le from OAI.Computability.NearSquareRoot.FixedCandidateCRTCloth
open private bare_count from OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveRetain

noncomputable section
section Bounded
variable {I : Type} {A : I → Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
  (rank : (i : I) → Fin (2^addressBits (n i)) ≃ A i)

/-- The marked coefficient stream at its native tape rank, for any intermediate
array reached by a preceding permutation of the packed field addresses. -/
abbrev batchArray (v : (i : I) → A i → Record (addressBits (n i))) (i : I) :=
  tapeArray (rank i) (fun a => send (Dusk.mark a)) (v i)

/-- Replacing each marked record by a bead row retains the same natural address order. -/
abbrev batchCloth (v : (i : I) → A i → Record (addressBits (n i))) :=
  CRTStream.clothRows n (fun i => v i ∘ rank i)

include hn in
theorem openBatchRows (v : (i : I) → A i → Record (addressBits (n i))) :
    BoundedTask n n (batchArray n rank v) (batchCloth n rank v) := by
  let r i : FixedCandidate.Array (n i) := v i ∘ rank i
  have run := easyAt n _ Dusk.tie_easy.mapping (fun i => records (r i)) 75000
    (fun i => recordVolume (hn i) (r i))
  apply run.conform (fun _ => rfl) (fun _ => rfl)
  · intro i
    exact (recordForest (r i)).symm
  · intro i
    exact (CRTStream.clothRows_encode n r i).symm

include hn in
theorem closeBatchRows (v : (i : I) → A i → Record (addressBits (n i))) :
    BoundedTask n n (batchCloth n rank v) (batchArray n rank v) := by
  let r i : FixedCandidate.Array (n i) := v i ∘ rank i
  have run := easyAt n _ easy_untie.mapping (fun i => (records (r i)).map Dusk.tie) 75000
    (fun i => (ties_le _).trans (recordVolume (hn i) (r i)))
  apply run.conform (fun _ => rfl) (fun _ => rfl)
  · intro i
    exact (CRTStream.clothRows_encode n r i).symm
  · intro i
    change send (((records (r i)).map Dusk.tie).map untie) = _
    rw [show ((records (r i)).map Dusk.tie).map untie = records (r i) by
      simp [FixedCandidate.records,Function.comp_def]]
    exact (recordForest (r i)).symm

private theorem parkBound {h b C : ℕ} (bound : h ≤ C*(b+1)) :
    h+b+1 ≤ (C+1)*(b+1) := by rw [Nat.add_mul,Nat.one_mul]; omega

include hn in
/-- Convert on either side of one native pass while retaining its exact header.
A call with linear workspace uses linear workspace after both conversions. -/
theorem fromNativeBatch (header : I → Tree) (K : ℕ)
    (keySize : ∀ i, (header i).count ≤ K*(n i+1))
    (x y : (i : I) → A i → Record (addressBits (n i))) (t s : I → ℕ)
    (native : BoundedTask t s (fun i => .fork (header i) (batchCloth n rank x i)) (batchCloth n rank y)) :
    BoundedTask (fun i => t i+n i) (fun i => max (s i) (n i))
      (fun i => .fork (header i) (batchArray n rank x i)) (batchArray n rank y) := by
  have first := ((openBatchRows n hn rank x).right header).bound (time' := n) (space' := n) (K+1) (K+1)
    (fun i => parkBound (keySize i)) (fun i => by simpa only [Nat.add_comm (n i)] using parkBound (keySize i))
  have start := first.mono (fun i => Nat.le_add_left (n i) (t i)) (fun i => le_max_right (s i) (n i))
  have main := native.mono (fun i => Nat.le_add_right (t i) (n i)) (fun i => le_max_left (s i) (n i))
  have stop := (closeBatchRows n hn rank y).mono (fun i => Nat.le_add_left (n i) (t i))
    (fun i => le_max_right (s i) (n i))
  exact sequence start (sequence main stop)
private theorem headerFootprint {J : Type} {clock arena : J → ℕ} {h x y : J → Tree}
    (run : BoundedTask clock arena (fun j => .fork (h j) (x j)) y) :
    ∃ C, ∀ j, (h j).count ≤ C*(arena j+1) := by
  obtain ⟨_,C,exec⟩ := run
  refine ⟨C,fun j => ?_⟩
  obtain ⟨_,_,witness⟩ := exec j [] (fun _ => []) 0 (fun _ => le_rfl)
  have bound := witness.start 0
  rw [bare_count,Nat.zero_add] at bound
  simp only [Tree.count] at bound
  omega

include hn in
/-- A native linear-space proof already bounds the count of its input header. -/
theorem fromNativeBatchLinear (header : I → Tree)
    (x y : (i : I) → A i → Record (addressBits (n i))) (t : I → ℕ)
    (native : BoundedTask t n (fun i => .fork (header i) (batchCloth n rank x i)) (batchCloth n rank y)) :
    BoundedTask (fun i => t i+n i) n
      (fun i => .fork (header i) (batchArray n rank x i)) (batchArray n rank y) := by
  obtain ⟨K,hK⟩ := headerFootprint native
  simpa only [max_self] using fromNativeBatch n hn rank header K hK x y t n native
end Bounded

section Effective
open EffectiveBoundedTask
variable {P : Type} [Primcodable P] {I : P → Type} {A : (p : P) → I p → Type}

/-- Both film conversions are fixed programs across the entire candidate family.
Only their rank interpretation and the complexity constants depend on the candidate. -/
theorem fromNativeBatchFamily (n : (p : P) → I p → ℕ) (hn : ∀ p i, 2 ≤ n p i)
    (rank : (p : P) → (i : I p) → Fin (2^addressBits (n p i)) ≃ A p i)
    (header : (p : P) → I p → Tree) (K : P → ℕ) (keySize : ∀ p i, (header p i).count ≤ K p*(n p i+1))
    (x y : (p : P) → (i : I p) → A p i → Record (addressBits (n p i)))
    (t s : (p : P) → I p → ℕ)
    (native : Family t s (fun p i => .fork (header p i) (batchCloth (n p) (rank p) (x p) i))
      (fun p => batchCloth (n p) (rank p) (y p))) :
    Family (fun p i => t p i+n p i) (fun p i => max (s p i) (n p i))
      (fun p i => .fork (header p i) (batchArray (n p) (rank p) (x p) i))
      (fun p => batchArray (n p) (rank p) (y p)) := by
  let nj (z : Sigma I) := n z.1 z.2
  let rj (z : Sigma I) := rank z.1 z.2
  have pre := Family.joint (P := P) (I := I) (t := n) (s := n)
    (u := fun p => batchArray (n p) (rank p) (x p)) (v := fun p => batchCloth (n p) (rank p) (x p))
    (openBatchRows nj (fun z => hn _ z.2) rj (fun z => x _ z.2))
  have post := Family.joint (P := P) (I := I) (t := n) (s := n)
    (u := fun p => batchCloth (n p) (rank p) (y p)) (v := fun p => batchArray (n p) (rank p) (y p))
    (closeBatchRows nj (fun z => hn _ z.2) rj (fun z => y _ z.2))
  have parked := CRTStream.familyBound (t' := n) (s' := n) (pre.right header)
    (fun p => K p+1) (fun p => K p+1)
    (fun p i => parkBound (keySize p i)) (fun p i => by simpa only [Nat.add_comm (n p i)] using parkBound (keySize p i))
  have grow p i := Nat.le_add_left (n p i) (t p i)
  have room p i := le_max_right (s p i) (n p i)
  exact (parked.mono grow room).sequence ((native.mono (fun p i => Nat.le_add_right ..)
    (fun p i => le_max_left ..)).sequence (post.mono grow room))

theorem fromNativeBatchLinearFamily (n : (p : P) → I p → ℕ) (hn : ∀ p i, 2 ≤ n p i)
    (rank : (p : P) → (i : I p) → Fin (2^addressBits (n p i)) ≃ A p i)
    (header : (p : P) → I p → Tree)
    (x y : (p : P) → (i : I p) → A p i → Record (addressBits (n p i)))
    (t : (p : P) → I p → ℕ)
    (native : Family t n (fun p i => .fork (header p i) (batchCloth (n p) (rank p) (x p) i))
      (fun p => batchCloth (n p) (rank p) (y p))) :
    Family (fun p i => t p i+n p i) n
      (fun p i => .fork (header p i) (batchArray (n p) (rank p) (x p) i))
      (fun p => batchArray (n p) (rank p) (y p)) := by
  obtain ⟨c,R,eff,pos,hc⟩ := native
  choose K hK using fun p => headerFootprint (hc p).2.task
  simpa only [max_self] using fromNativeBatchFamily n hn rank header K hK x y t n ⟨c,R,eff,pos,hc⟩

end Effective
end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
