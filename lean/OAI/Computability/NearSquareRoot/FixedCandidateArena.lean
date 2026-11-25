import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveInterface

/-! # Executing every candidate tuple with its certified time and arena

The space budget can depend on the tuple and the input width. This admits
correct slow guesses alongside the tuples for which the arena is linear.
The bounds are proofs about one emitted command file for each tuple.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate
open IntegerMultiplication Code DigitPacking FixedPoint Space EffectiveBoundedTask

variable {P : Type} [Primcodable P] (K : P → ℕ)
variable (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
variable (plans : ∀ p i, Plan (hv p i)) (c : P → Clocks)

noncomputable section

abbrev EffectiveCRTAt (arena clock : P → ℕ → ℕ)
    (op : ∀ p (i : LargeInput (K p)), Array i.val.width → Array i.val.width) :=
  Family (fun p (r : StreamDomain K p) => clock p r.1.val.width) (fun p r => arena p r.1.val.width)
    (fun _ r => framed r.2) (fun p r => framed (op p r.1 r.2))

abbrev EffectiveTransformAt (arena clock : P → ℕ → ℕ)
    (op : ∀ p (i : LargeInput (K p)), Array i.val.width → Array i.val.width) :=
  Family (fun p (r : NormDomain K hv p) => clock p r.val.1.val.width) (fun p r => arena p r.val.1.val.width)
    (fun _ r => framed r.val.2) (fun p r => framed (op p r.val.1 r.val.2))

structure EffectiveTransportsAt (arena : P → ℕ → ℕ) : Prop where
  crt : EffectiveCRTAt K arena (fun p => (c p).route) (fun p i => route (hv p i))
  undoCRT : EffectiveCRTAt K arena (fun p => (c p).route) (fun p i => afterInverseCRT (hv p i))
  fourier : EffectiveTransformAt K hv arena (fun p => (c p).forward) (fun p i => eval (hv p i) (plans p i).forward)
  adjoint : EffectiveTransformAt K hv arena (fun p => (c p).inverse) (fun p i => eval (hv p i) (plans p i).inverse)

set_option maxHeartbeats 1800000 in
/-- Effective assembly on the large-width domain. Each constituent besides the
four transports is extracted from a single checked task spanning every candidate
index and every input, yielding a constant program file for that constituent. -/
theorem effective_largeTask_atArena (arena T : P → ℕ → ℕ)
    (hK : ∀ p, 2 ≤ K p) (hnA : ∀ p n, n ≤ arena p n) (hAT : ∀ p n, arena p n ≤ T p n)
    (hT : ∀ p n, (c p).total n ≤ T p n) (ops : EffectiveTransportsAt K hv plans c arena) :
    Family (fun p (i : LargeInput (K p)) => T p i.val.width) (fun p i => arena p i.val.width)
      (fun _ i => send i.val.operands) (fun _ i => send (Lea.answer i.val.operands)) := by
  let L p := LargeInput (K p)
  let n (p : P) (i : L p) := i.val.width
  let x (p : P) (i : L p) := i.val.operands.1
  let y (p : P) (i : L p) := i.val.operands.2
  let t (p : P) (i : L p) := T p (n p i)
  let s (p : P) (i : L p) := arena p (n p i)
  have ns (p : P) (i : L p) : n p i ≤ s p i := hnA p (n p i)
  have st (p : P) (i : L p) : s p i ≤ t p i := hAT p (n p i)
  have hn (p : P) (i : L p) : 2 ≤ n p i := (hK p).trans i.property
  have hy (p : P) (i : L p) : (y p i).length = n p i := i.val.val.property.symm
  have lin (p : P) (i : L p) : n p i ≤ t p i := by
    apply le_trans _ (hT p (n p i))
    dsimp [Clocks.total]
    omega
  have mc (p : P) (i : L p) : productClock (n p i) ≤ t p i := by
    apply le_trans _ (hT p (n p i))
    dsimp [Clocks.total]
    omega
  have rc (p : P) (i : L p) : (c p).route (n p i) ≤ t p i := by
    apply le_trans _ (hT p (n p i))
    dsimp [Clocks.total]
    omega
  have fc (p : P) (i : L p) : (c p).forward (n p i) ≤ t p i := by
    apply le_trans _ (hT p (n p i))
    dsimp [Clocks.total]
    omega
  have jc (p : P) (i : L p) : (c p).inverse (n p i) ≤ t p i := by
    apply le_trans _ (hT p (n p i))
    dsimp [Clocks.total]
    omega
  let a (p : P) (i : L p) := input (hv p i) (x p i)
  let b (p : P) (i : L p) := input (hv p i) (y p i)
  let forward (p : P) (i : L p) z := eval (hv p i) (plans p i).forward (route (hv p i) z)
  let prod (p : P) (i : L p) := pointwise (forward p i (a p i)) (forward p i (b p i))
  let adj (p : P) (i : L p) := eval (hv p i) (plans p i).inverse (prod p i)
  let scaled (p : P) (i : L p) := rescale (n p i) (adj p i)
  let hN (v : Sigma L) := hn v.1 v.2
  let hV (v : Sigma L) := hv v.1 v.2
  have start : Family t n (fun _ i => send i.val.operands)
      (fun p i => .fork (framed (a p i)) (framed (b p i))) := by
    apply Family.joint
    have prep := prepare (fun v : Sigma L => v.2.val.operands) (fun v => hy v.1 v.2) hN hV
    apply (prep.mono (fun v => lin v.1 v.2) (fun _ => le_rfl)).conform
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro v
    rw [records_input (hV v) (rfl : (x v.1 v.2).length = n v.1 v.2) (hN v),
      records_input (hV v) (hy v.1 v.2) (hN v)]
    rfl
  have fw (r : ∀ p (i : L p), Array (n p i)) (hr : ∀ p i, Admissible (hv p i) (route (hv p i) (r p i))) :
      Family t s (fun p i => framed (r p i)) (fun p i => framed (forward p i (r p i))) := by
    apply Family.sequence (v := fun p i => framed (route (hv p i) (r p i)))
    · exact (ops.crt.on (fun p (i : L p) => ⟨i,r p i⟩)).mono rc (fun _ _ => le_rfl)
    · exact (ops.fourier.on (fun p (i : L p) => ⟨⟨i,route (hv p i) (r p i)⟩,hr p i⟩)).mono fc (fun _ _ => le_rfl)
  have sizeRoom (p : P) (i : L p) (r : Array (n p i)) : (framed r).count ≤ 75000*(s p i+1) :=
    (framed_size (hn p i) r).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (ns p i)))
  have both := Family.pairCalls st (fw a (fun p i => input_admissible _ (hn p i) _))
    (fw b (fun p i => input_admissible _ (hn p i) _)) (fun p i => ⟨sizeRoom p i _,sizeRoom p i _⟩)
  have mult : Family t n (fun p i => .fork (framed (forward p i (a p i))) (framed (forward p i (b p i))))
      (fun p i => framed (prod p i)) := by
    apply Family.joint
    exact spectralProduct _ _ hN (fun v => lin v.1 v.2) (fun v => mc v.1 v.2) _ _
  have inv : Family t s (fun p i => framed (prod p i)) (fun p i => framed (adj p i)) :=
    (ops.adjoint.on (fun p (i : L p) => ⟨⟨i,prod p i⟩,spectral_admissible (hv p i) (hn p i) (plans p i) _ _⟩)).mono
      jc (fun _ _ => le_rfl)
  have scale : Family t n (fun p i => framed (adj p i)) (fun p i => framed (scaled p i)) := by
    apply Family.joint
    exact (directorySqrtPass _ hN hV (fun v => adj v.1 v.2)).mono (fun v => mc v.1 v.2) (fun _ => le_rfl)
  have undo : Family t s (fun p i => framed (scaled p i)) (fun p i => framed (afterInverseCRT (hv p i) (scaled p i))) :=
    (ops.undoCRT.on (fun p (i : L p) => ⟨i,scaled p i⟩)).mono rc (fun _ _ => le_rfl)
  have finish : Family t n (fun p i => framed (afterInverseCRT (hv p i) (scaled p i))) (fun _ i => send (Lea.answer i.val.operands)) := by
    apply Family.joint
    obtain ⟨z,hz,out⟩ := readout _ hN hV (fun v => x v.1 v.2) (fun v => y v.1 v.2)
      (fun v => scaled v.1 v.2) (fun _ => rfl) (fun v => hy v.1 v.2)
      (fun v => ⟨(plans v.1 v.2).forward,(plans v.1 v.2).inverse,(plans v.1 v.2).fwd_ok,
        (plans v.1 v.2).inv_ok,eval_output (hV v) _ _ _ _⟩)
    apply (out.mono (fun v => lin v.1 v.2) (fun _ => le_rfl)).conform
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro v
    exact congrArg send ((ProductRecovery.product_postcondition_iff _ _ _ rfl (hy v.1 v.2)).mp (hz v))
  have same (p : P) (i : L p) : t p i ≤ t p i := le_rfl
  exact ((((((start.mono same ns).sequence both).sequence (mult.mono same ns)).sequence inv).sequence
    (scale.mono same ns)).sequence undo).sequence (finish.mono same ns)

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
