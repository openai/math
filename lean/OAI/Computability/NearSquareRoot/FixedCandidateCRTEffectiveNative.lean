import OAI.Computability.NearSquareRoot.FixedCandidateCRTNative
import OAI.Computability.NearSquareRoot.FixedCandidateCRTEffectiveSweep
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveRetain
import OAI.Computability.NearSquareRoot.FixedCandidateArena

/-! # Effective native-CRT stream passes with arbitrary reserve estimates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code Space DigitPacking FixedPoint EffectiveBoundedTask

noncomputable section

variable {P : Type} [Primcodable P] {I : P → Type} {H : Type} [Codec H]

/-- Uniform film conversion preserves the actual emitted program of each guess. -/
theorem fromNativeFamily (n : (p : P) → I p → ℕ) (hn : ∀ p i, 2 ≤ n p i)
    (header : (p : P) → I p → H) (K : ℕ) (keySize : ∀ p i, size (header p i) ≤ K*(n p i+1))
    (x y : (p : P) → (i : I p) → Array (n p i))
    (t arena : (p : P) → I p → ℕ)
    (native : Family t arena (fun p i => .fork (send (header p i)) (clothRows (n p) (x p) i))
      (fun p => clothRows (n p) (y p))) :
    Family (fun p i => t p i+n p i) (fun p i => arena p i+n p i)
      (fun p i => .fork (send (header p i)) (framed (x p i))) (fun p i => framed (y p i)) := by
  let T p i := t p i+n p i
  let A p i := arena p i+n p i
  have pre := Family.joint (P := P) (I := I) (t := n) (s := n)
    (u := fun p i => .fork (send (header p i)) (framed (x p i)))
    (v := fun p i => .fork (send (tally (n p i))) (.fork (send (header p i)) (clothRows (n p) (x p) i)))
    (beginRows (fun z : Sigma I => n z.1 z.2) (fun z => hn _ z.2) (fun z => header _ z.2) K
      (fun z => keySize _ z.2) (fun z => x _ z.2))
  have post := Family.joint (P := P) (I := I) (t := n) (s := n)
    (u := fun p i => .fork (send (tally (n p i))) (clothRows (n p) (y p) i))
    (v := fun p i => framed (y p i))
    (endRows (fun z : Sigma I => n z.1 z.2) (fun z => hn _ z.2) (fun z => y _ z.2))
  have main := native.right (fun p i => send (tally (n p i)))
  have charged := familyBound (t' := T) (s' := A) main (fun _ => 4) (fun _ => 4)
    (fun p i => by change size (tally (n p i))+t p i+1 ≤ 4*(t p i+n p i+1); simp [size_tally]; omega)
    (fun p i => by change arena p i+size (tally (n p i))+1 ≤ 4*(arena p i+n p i+1); simp [size_tally]; omega)
  have ht p i : n p i ≤ T p i := Nat.le_add_left ..
  have ha p i : n p i ≤ A p i := Nat.le_add_left ..
  exact (pre.mono ht ha).sequence (charged.sequence (post.mono ht ha))

set_option maxHeartbeats 2000000 in
/-- Complete native families yield the original candidate's two framed stream passes,
with an absolute register bound even on reserve guesses whose arena grows too quickly. -/
theorem effectiveNativeSweep (n : (p : P) → I p → ℕ) (valid : ∀ p i, Directory (n p i))
    (hn : ∀ p i, 2 ≤ n p i) (inv : Bool) (tick arena : P → ℕ → ℕ)
    (native : Family (fun p (e : Input (n p) inv) => tick p (n p e.1))
      (fun p e => arena p (n p e.1))
      (fun p e => .fork (send (seed inv e.2.1.val))
        (packedRows (valid p e.1) e.2.1.val (pack (valid p e.1) e.2.1.val e.2.2)))
      (fun p e => packedRows (valid p e.1) e.2.1.val
        (Benes.scatter (packedSlot (valid p e.1) inv e.2.1.val) (pack (valid p e.1) e.2.1.val e.2.2)))) :
    Family (fun p (y : (i : I p) × Array (n p i)) => count (n p y.1)*(tick p (n p y.1)+n p y.1)+n p y.1)
      (fun p y => arena p (n p y.1)+n p y.1)
      (fun _ y => framed y.2) (fun p y => framed (outcome (valid p y.1) inv y.2)) := by
  let J p := Input (n p) inv
  let atN p (e : J p) := n p e.1
  let header p (e : J p) := seed inv e.2.1.val
  let after p (e : J p) := step (valid p e.1) inv e.2.2 e.2.1.val
  let joint (z : Sigma J) : Input (fun y : Sigma I => n y.1 y.2) inv :=
    ⟨⟨z.1,z.2.1⟩,z.2.2⟩
  obtain ⟨K,hK⟩ := setupCap (n := fun z : Sigma J => atN z.1 z.2) (fun z => hn _ z.2.1) _
    ((seedSizeDom (fun y : Sigma I => n y.1 y.2) inv).map joint)
  have wrapped := fromNativeFamily atN (fun p e => hn p e.1) header K (fun p e => hK ⟨p,e⟩)
    (fun _ e => e.2.2) after (fun p e => tick p (atN p e)) (fun p e => arena p (atN p e))
    (native.conform (fun _ _ => rfl) (fun _ _ => rfl)
      (fun p e => by rw [packedRows_pack,clothRows_encode]) (fun p e => by rw [packedRows_scatter,clothRows_encode]))
  have run := effectiveSweep n valid hn inv (fun p u => tick p u+u) (fun p u => arena p u+u) wrapped
  exact familyBound run (fun _ => 1) (fun _ => 2) (fun _ _ => by simp) (fun _ _ => by omega)

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
