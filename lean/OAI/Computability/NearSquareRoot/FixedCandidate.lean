import OAI.Computability.NearSquareRoot.FixedCandidateAdmissible
import OAI.Computability.NearSquareRoot.FixedCandidateInterface
import OAI.Computability.NearSquareRoot.FixedCandidateReadout
import OAI.Computability.NearSquareRoot.PrecisionSqrtRescale

/-! # Physical composition of the fixed-exponent multiplication program

The CRT passes act on every payload of their tape format. The Fourier passes
act on payloads satisfying the proved input norm bound. The remaining commands produce the input records, align both
spectra, multiply the grid records, and read the inverse-CRT result through
the mask and carry machine. Sequential passes reuse their tape space.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code Bits DigitPacking FixedPoint Space

variable {I : Type} (n : I → ℕ)

noncomputable section

private theorem use_pass {clock total : ℕ → ℕ} {op : ∀ i, Array (n i) → Array (n i)}
    (cmd : StreamPass n clock op) (r : (i : I) → Array (n i)) (ht : ∀ i, clock (n i) ≤ total (n i)) :
    BoundedTask (fun i => total (n i)) n (fun i => framed (r i)) (fun i => framed (op i (r i))) :=
  (cmd.on (fun i => ⟨i,r i⟩)).mono ht (fun _ => le_rfl)

variable (hv : ∀ i, Directory (n i))

private theorem use_transform {clock total : ℕ → ℕ} {op : ∀ i, Array (n i) → Array (n i)}
    (cmd : AdmissiblePass n hv clock op) (r : (i : I) → Array (n i)) (hr : ∀ i, Admissible (hv i) (r i))
    (ht : ∀ i, clock (n i) ≤ total (n i)) :
    BoundedTask (fun i => total (n i)) n (fun i => framed (r i)) (fun i => framed (op i (r i))) :=
  (cmd.on (fun i => ⟨⟨i,r i⟩, hr i⟩)).mono ht (fun _ => le_rfl)

/-- Compose every physical stage on a family of sufficiently large, equal-length
operands. The exact return word is the canonical P192 binary product. -/
theorem assemble {n : I → ℕ} (hn : ∀ i, 2 ≤ n i) (hv : ∀ i, Directory (n i))
    (plan : ∀ i, Plan (hv i)) (c : Clocks) (ops : Transports n hv plan c)
    (p : I → Interface.Pair) (hx : ∀ i, (p i).1.length = n i) (hy : ∀ i, (p i).2.length = n i) :
    BoundedTask (c.total ∘ n) n (send ∘ p) (fun i => send (Lea.answer (p i))) := by
  let t := c.total ∘ n
  have lin (i : I) : n i ≤ t i := by dsimp [t, Clocks.total]; omega
  have mc (i : I) : productClock (n i) ≤ t i := by dsimp [t, Clocks.total]; omega
  have rc (i : I) : c.route (n i) ≤ t i := by dsimp [t, Clocks.total]; omega
  have fc (i : I) : c.forward (n i) ≤ t i := by dsimp [t, Clocks.total]; omega
  have jc (i : I) : c.inverse (n i) ≤ t i := by dsimp [t, Clocks.total]; omega
  let a i := input (hv i) (p i).1
  let b i := input (hv i) (p i).2
  let forward i z := eval (hv i) (plan i).forward (route (hv i) z)
  let prod i := pointwise (forward i (a i)) (forward i (b i))
  let adj i := eval (hv i) (plan i).inverse (prod i)
  let v i := rescale (n i) (adj i)
  have hw i : (p i).2.length = (p i).1.length := (hy i).trans (hx i).symm
  have prep := prepare p hw (fun i => hx i ▸ hn i) (fun i => hx i ▸ hv i)
  have start : BoundedTask t n (send ∘ p) (fun i => .fork (framed (a i)) (framed (b i))) := by
    apply (prep.conform (time' := n) (space' := n) hx hx (fun _ => rfl) _).mono lin (fun _ => le_rfl)
    intro i
    rw [hx i, records_input (hv i) (hx i) (hn i), records_input (hv i) (hy i) (hn i)]
    rfl
  have fw (r : (i : I) → Array (n i)) (hr : ∀ i, Admissible (hv i) (route (hv i) (r i))) :
      BoundedTask t n (fun i => framed (r i)) (fun i => framed (forward i (r i))) :=
    sequence (use_pass n (total := c.total) ops.crt r rc)
      (use_transform n hv (total := c.total) ops.fourier (fun i => route (hv i) (r i)) hr fc)
  have both := pairCalls lin (fw a (fun i => input_admissible (hv i) (hn i) _))
    (fw b (fun i => input_admissible (hv i) (hn i) _)) (fun i =>
    ⟨framed_size (hn i) _, framed_size (hn i) _⟩)
  have mult := spectralProduct n t hn lin mc (fun i => forward i (a i)) (fun i => forward i (b i))
  have inv := use_transform n hv (total := c.total) ops.adjoint prod
    (fun i => spectral_admissible (hv i) (hn i) (plan i) _ _) jc
  have rescale := (FixedPoint.directorySqrtPass n hn hv adj).mono mc (fun _ => le_rfl)
  have undo := use_pass n (total := c.total) ops.undoCRT v rc
  obtain ⟨z,hz,finish⟩ := readout n hn hv (fun i => (p i).1) (fun i => (p i).2) v hx hy
    (fun i => ⟨(plan i).forward,(plan i).inverse,(plan i).fwd_ok,(plan i).inv_ok,
      eval_output (hv i) _ _ _ _⟩)
  have finish' : BoundedTask t n (fun i => framed (afterInverseCRT (hv i) (v i))) (fun i => send (Lea.answer (p i))) := by
    apply (finish.mono lin (fun _ => le_rfl)).conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro i
    exact congrArg send ((ProductRecovery.product_postcondition_iff _ _ _ (hx i) (hy i)).mp (hz i))
  exact sequence (sequence (sequence (sequence (sequence (sequence start both) mult) inv) rescale) undo) finish'

/-- Instantiate the composition on the common threshold domain of the finite-prefix guard. -/
theorem largeTask {N : ℕ} (hn : 2 ≤ N)
    (hv : ∀ i : LargeInput N, Directory i.val.width) (p : ∀ i, Plan (hv i))
    (c : Clocks) (ops : Transports (fun i : LargeInput N => i.val.width) hv p c) :
    LargeTask N c.total :=
  assemble (fun i => hn.trans i.property) hv p c ops (fun i => i.val.operands)
    (fun _ => rfl) (fun i => i.val.val.property.symm)

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
