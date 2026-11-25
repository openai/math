import OAI.Computability.NearSquareRoot.FixedCandidateArrays
import OAI.Computability.NearSquareRoot.FixedCandidateProduct

/-! # Stream and resource interfaces of the fixed-exponent transforms -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code DigitPacking FixedPoint Space

/-- The separate large-domain running-time allowances for the non-elementary commands. -/
structure Clocks where
  route : ℕ → ℕ
  forward : ℕ → ℕ
  inverse : ℕ → ℕ

def Clocks.total (c : Clocks) (n : ℕ) :=
  n + productClock n + c.route n + c.forward n + c.inverse n

variable {I : Type} (n : I → ℕ)

/-- A single framed machine command acts on arbitrary records at every admitted size.
The second field of its input domain is the actual input payload. -/
abbrev StreamPass (clock : ℕ → ℕ) (op : ∀ i, Array (n i) → Array (n i)) :=
  BoundedTask (fun s : (i : I) × Array (n i) => clock (n s.1)) (fun s => n s.1)
    (fun s => framed s.2) (fun s => framed (op s.1 s.2))

noncomputable section

variable (hv : ∀ i, Directory (n i)) (plan : ∀ i, Plan (hv i))

/-- The transform command acts on each record packet in the permitted energy range. -/
abbrev AdmissiblePass (clock : ℕ → ℕ) (op : ∀ i, Array (n i) → Array (n i)) :=
  let D := {s : (i : I) × Array (n i) // Admissible (hv s.1) s.2}
  BoundedTask (fun s : D => clock (n s.val.1)) (fun s => n s.val.1)
    (fun s => framed s.val.2) (fun s => framed (op s.val.1 s.val.2))

/-- Four physical command boundaries surrounding the checked elementary stages.
The forward and inverse CRT commands are each available independently of the payload. -/
structure Transports (c : Clocks) : Prop where
  crt : StreamPass n c.route (fun i => route (hv i))
  undoCRT : StreamPass n c.route (fun i => afterInverseCRT (hv i))
  fourier : AdmissiblePass n hv c.forward (fun i => eval (hv i) (plan i).forward)
  adjoint : AdmissiblePass n hv c.inverse (fun i => eval (hv i) (plan i).inverse)

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
