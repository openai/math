import OAI.Computability.NearSquareRoot.FixedCandidate
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Interfaces for the four effective large-input multiplication transports -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code DigitPacking FixedPoint Space EffectiveBoundedTask

variable {P : Type} [Primcodable P] (K : P → ℕ)
variable (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
variable (plans : ∀ p i, Plan (hv p i)) (c : P → Clocks)

abbrev StreamDomain (p : P) := (i : LargeInput (K p)) × Array i.val.width

noncomputable section

abbrev NormDomain (p : P) := {r : StreamDomain K p // Admissible (hv p r.1) r.2}

abbrev EffectiveCRT (clock : P → ℕ → ℕ)
    (op : ∀ p (i : LargeInput (K p)), Array i.val.width → Array i.val.width) :=
  Family (fun p (r : StreamDomain K p) => clock p r.1.val.width) (fun _ r => r.1.val.width)
    (fun _ r => framed r.2) (fun p r => framed (op p r.1 r.2))

abbrev EffectiveTransform (clock : P → ℕ → ℕ)
    (op : ∀ p (i : LargeInput (K p)), Array i.val.width → Array i.val.width) :=
  Family (fun p (r : NormDomain K hv p) => clock p r.val.1.val.width) (fun _ r => r.val.1.val.width)
    (fun _ r => framed r.val.2) (fun p r => framed (op p r.val.1 r.val.2))

/-- All varying command files are computed from the outer candidate index. -/
structure EffectiveTransports : Prop where
  crt : EffectiveCRT K (fun p => (c p).route) (fun p i => route (hv p i))
  undoCRT : EffectiveCRT K (fun p => (c p).route) (fun p i => afterInverseCRT (hv p i))
  fourier : EffectiveTransform K hv (fun p => (c p).forward) (fun p i => eval (hv p i) (plans p i).forward)
  adjoint : EffectiveTransform K hv (fun p => (c p).inverse) (fun p i => eval (hv p i) (plans p i).inverse)

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
