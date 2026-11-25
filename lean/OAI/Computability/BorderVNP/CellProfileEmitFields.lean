import OAI.Computability.BorderVNP.CellDirectoryTyped
import OAI.Computability.BorderVNP.CellEmitRange
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary

/-! # Decoding the typed payload of a profile record

The transport contains a binary selector width. Every crossing profile's selector
has width at most the length of its histogram. A finite procedure can therefore
recover a unary iteration bound from the histogram and clip the binary field to it.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.ProfileData

open ExactQuantumFactoring ExactQuantumFactoring.BitStackProgram

/-- Typed payload of the fourth public record constructor. -/
abbrev Data := ℕ × Port × ℕ × List ℕ × List Route

/-- Native product/list encoding after the profile tags have been consumed. -/
def code : Data → List Bool :=
  prodCode Nat.bits (prodCode Typed.port (prodCode Nat.bits (prodCode Typed.naturals (listCode Typed.route))))

/-- Physical wire-port triple, read from its existing encoding. -/
noncomputable def portFields : Procedure Typed.port (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) Typed.portFields :=
  (Procedure.identity _).precompose Typed.portFields

/-- Route identifier, width, and the two physical ports. -/
noncomputable def routeFields : Procedure Typed.route (prodCode Nat.bits (prodCode Nat.bits (prodCode Typed.port Typed.port)))
    Typed.routeFields := (Procedure.identity _).precompose Typed.routeFields

variable {α : Type} {ea : α → List Bool} {d : α → Data}

/-- Number of original copies in the reported profile. -/
noncomputable def copies (p : Procedure ea code d) : Procedure ea Nat.bits (fun x => (d x).1) :=
  (Procedure.first ..).comp p

/-- Selector port. -/
noncomputable def selector (p : Procedure ea code d) : Procedure ea Typed.port (fun x => (d x).2.1) :=
  (Procedure.first ..).comp ((Procedure.second ..).comp p)

/-- Number of selector lanes, represented in binary. -/
noncomputable def width (p : Procedure ea code d) : Procedure ea Nat.bits (fun x => (d x).2.2.1) :=
  (Procedure.first ..).comp ((Procedure.second ..).comp ((Procedure.second ..).comp p))

/-- List of announced multiplicities in term order. -/
noncomputable def histogram (p : Procedure ea code d) : Procedure ea Typed.naturals (fun x => (d x).2.2.2.1) :=
  (Procedure.first ..).comp ((Procedure.second ..).comp ((Procedure.second ..).comp ((Procedure.second ..).comp p)))

/-- Ordered physical route records. -/
noncomputable def routes (p : Procedure ea code d) : Procedure ea (listCode Typed.route) (fun x => (d x).2.2.2.2) :=
  (Procedure.second ..).comp ((Procedure.second ..).comp ((Procedure.second ..).comp ((Procedure.second ..).comp p)))

/-- Recover a unary term count from the explicit histogram. -/
noncomputable def terms (p : Procedure ea code d) : Procedure ea unaryCode (fun x => (d x).2.2.2.1.length) :=
  (NativeAIG.Emission.listUnaryLength Nat.bits 0).comp (histogram p)

/-- Obtain the unary selector width bounded by the number of terms. -/
noncomputable def clippedWidth (p : Procedure ea code d) :
    Procedure ea unaryCode (fun x => min (d x).2.2.2.1.length (d x).2.2.1) :=
  Procedure.clippedUnary.comp ((terms p).pair (width p))

/-- For the binary width of the actual crossing profiles, clipping gives the original width. -/
theorem crossing_width (A : ℕ) : min A (Nat.clog 2 A) = Nat.clog 2 A :=
  min_eq_right (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le : A ≤ 2^A))

end CellSparse.Packet.Emit.ProfileData

end BorderVNP
end Computability
end OAI
