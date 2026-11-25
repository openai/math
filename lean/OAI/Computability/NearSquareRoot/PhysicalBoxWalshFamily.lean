import OAI.Computability.NearSquareRoot.PhysicalBoxWalshFrames
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # One generated Walsh ticket command across all template indices

The fixed pre- and postprocessing programs interface with the same emitted
mask as the parameter-dependent Walsh command. The saved operand length
occupies its own register while that command executes. Only the raw Walsh
syntax varies with the candidate, and the composed command retains a common
register bound across candidates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer
open IntegerMultiplication Code Space Strip FixedPoint FixedCandidate DigitPacking
open ShortFourier.BatchWord PhysicalWalsh PhysicalWalsh.GatherProgram
open EffectiveBoundedTask

noncomputable section

private theorem familyBudget {P : Type} [Primcodable P] {I : P → Type}
    {t s t' s' : ∀ p, I p → ℕ} {u v : ∀ p, I p → Tree}
    (h : Family t s u v) (T S : ℕ) (ht : ∀ p i,t p i+1 ≤ T*(t' p i+1))
    (hs : ∀ p i,s p i+1 ≤ S*(s' p i+1)) : Family t' s' u v := by
  obtain ⟨cmd,R,src,pos,runs⟩ := h
  exact ⟨cmd,R,src,pos,fun p => ⟨(runs p).1,(runs p).2.bound T S (ht p) (hs p)⟩⟩

/-- Keep the actual operand ruler while the compiled mask interpreter runs.
The frozen mask compiler and final output encoder are uniform over all
candidate parameters and all admissible tickets. -/
theorem walshMaskFamilyFramesAt {P : Type} [Primcodable P] {I : P → Type}
    (n stage : ∀ p, I p → ℕ) (dir : ∀ p, I p → Bool)
    (hn : ∀ p i, 2 ≤ n p i) (hb : ∀ p i, Directory (n p i))
    (inside : ∀ p i,stage p i < (directedPlan (dir p i,tally (addressBits (n p i)))).length)
    (clock arena : P → ℕ → ℕ) (lin : ∀ p i, n p i ≤ arena p (n p i))
    (large : ∀ p i, arena p (n p i) ≤ clock p (n p i))
    (x y : ∀ p (i : I p), FixedCandidate.Array (n p i))
    (raw : Family (fun p i => clock p (n p i)) (fun p i => arena p (n p i))
      (fun p i => send (flags (walshBits (hb p i) (dir p i) (stage p i) (inside p i)), Odd.words (x p i)))
      (fun p i => send (Odd.words (y p i)))) :
    Family (fun p i => clock p (n p i)) (fun p i => arena p (n p i))
      (fun p i => .fork (send (phaseStageTicket (addressBits (n p i)) (dir p i) (stage p i) (inside p i)))
        (framed (x p i))) (fun p i => framed (y p i)) := by
  let time p i := clock p (n p i)
  let park p i := send (tally (n p i))
  let a p i := send (flags (walshBits (hb p i) (dir p i) (stage p i) (inside p i)), Odd.words (x p i))
  let b p i := send (Odd.words (y p i))
  let space p i := arena p (n p i)
  have clocked : Family time space a b := raw
  have held : Family time space park park := by
    apply Family.joint
    let q := fun z : Sigma I => park z.1 z.2
    have inert : Task (fun _ : Sigma I => 0) q q := Task.self
    apply (BoundedTask.of_time inert).bound 1 3
    · intro z
      simp
    · intro z
      have hl := lin z.1 z.2
      change size (tally (n z.1 z.2))+0+1 ≤ 3*(arena z.1 (n z.1 z.2)+1)
      simp [size_tally]
      omega
  have sizes p (i : I p) : (park p i).count ≤ 75000*(space p i+1) ∧ (b p i).count ≤ 75000*(space p i+1) := by
    have hl : n p i ≤ space p i := lin p i
    constructor
    · change size (tally (n p i)) ≤ _
      simp [size_tally]
      omega
    · have h := framed_size (hn p i) (y p i)
      have eq : Odd.words (y p i) = FixedCandidate.records (y p i) := List.map_ofFn (f:=y p i) (g:=Dusk.mark)
      change size (Odd.words (y p i)) ≤ _
      rw [eq]
      change size (tally (n p i),FixedCandidate.records (y p i)) ≤ _ at h
      simp only [size_prod] at h
      omega
  have middle := Family.pairCalls large clocked held sizes
  let ns (z : Sigma I) := n z.1 z.2
  let js (z : Sigma I) := stage z.1 z.2
  let ds (z : Sigma I) := dir z.1 z.2
  have pre := walshMaskPre ns js ds (fun z => hn z.1 z.2) (fun z => hb z.1 z.2)
    (fun z => inside z.1 z.2) (fun z => x z.1 z.2)
  have post := walshMaskPost ns (fun z => hn z.1 z.2) (fun z => y z.1 z.2)
  apply Family.sequence (v:=fun p i => .fork (a p i) (park p i)) _ (Family.sequence middle _)
  · exact Family.joint (pre.mono (fun z => (lin z.1 z.2).trans (large z.1 z.2)) (fun z => lin z.1 z.2))
  · exact Family.joint (post.mono (fun z => (lin z.1 z.2).trans (large z.1 z.2)) (fun z => lin z.1 z.2))


/-- Keep the actual operand ruler while the compiled mask interpreter runs.
The frozen mask compiler and final output encoder are uniform over all
candidate parameters and all admissible tickets. -/
theorem walshMaskFamilyFrames {P : Type} [Primcodable P] {I : P → Type}
    (n stage : ∀ p, I p → ℕ) (dir : ∀ p, I p → Bool)
    (hn : ∀ p i, 2 ≤ n p i) (hb : ∀ p i, Directory (n p i))
    (inside : ∀ p i,stage p i < (directedPlan (dir p i,tally (addressBits (n p i)))).length)
    (ρ : P → ℝ) (clock : P → ℕ → ℕ) (large : ∀ p i, n p i ≤ clock p (n p i))
    (room : ∀ p i, Pieces.sparseTime (ρ p) (addressBits (n p i)) ≤ clock p (n p i))
    (x y : ∀ p (i : I p), FixedCandidate.Array (n p i))
    (raw : Family (fun p i => Pieces.sparseTime (ρ p) (addressBits (n p i)))
      (fun p i => Pieces.sparseSpace (addressBits (n p i)))
      (fun p i => send (flags (walshBits (hb p i) (dir p i) (stage p i) (inside p i)), Odd.words (x p i)))
      (fun p i => send (Odd.words (y p i)))) :
    Family (fun p i => clock p (n p i)) n
      (fun p i => .fork (send (phaseStageTicket (addressBits (n p i)) (dir p i) (stage p i) (inside p i)))
        (framed (x p i))) (fun p i => framed (y p i)) := by
  apply walshMaskFamilyFramesAt n stage dir hn hb inside clock (fun _ => id)
    (fun _ _ => le_rfl) large x y
  exact familyBudget raw 1 49 (fun p i => by simpa using Nat.succ_le_succ (room p i)) (fun p i => by
    have h := (packed_volume (hn p i)).2
    change capacity (n p i)*addressBits (n p i)+1 ≤ 49*(n p i+1)
    omega)

end
end FixedLayer

end NearSquareRoot
end Computability
end OAI
