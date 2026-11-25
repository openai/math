import OAI.Computability.BorderVNP.CellDirectoryWire
import OAI.Computability.QuantumFactoring.BitStackListCode
import OAI.Computability.QuantumFactoring.BitStackSumInjection

/-! # Internal typed representation for the fixed private packet translator

A canonical packet is decoded once from its public transport framing. Finite
stack procedures use tagged sums for constructors and self-delimiting pairs
and lists for their variable data. None of these internal tags are additional
public advice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Typed

open ExactQuantumFactoring.BitStackProgram

/-- Encodings of repeated scalar fields and Boolean table entries. -/
abbrev naturals := listCode Nat.bits
/-- Boolean table entry list encoding. -/
abbrev booleans := listCode Procedure.boolCode

/-- Internal triple for a port. -/
def portFields (p : Port) : ℕ × ℕ × ℕ := (p.base,p.copyStride,p.laneStride)

/-- Bit-stack tuple encoding of the physical port. -/
def port (p : Port) := prodCode Nat.bits (prodCode Nat.bits Nat.bits) (portFields p)

/-- Internal tuple for a profile route. -/
def routeFields (r : Route) : ℕ × ℕ × Port × Port := (r.term,r.lanes,r.original,r.compact)

/-- Bit-stack tuple encoding of a compact route. -/
def route (r : Route) := prodCode Nat.bits (prodCode Nat.bits (prodCode port port)) (routeFields r)

/-- Right-associated tagged union of the four private factor payloads. -/
abbrev FactorFields := (List ℕ × List Bool) ⊕ (List ℕ × List Bool) ⊕ (List ℕ × List ℕ) ⊕ (ℕ × Port)

/-- Tags for Boolean, sign, gadget, and unary-position factors, respectively. -/
def factorFields : Factor → FactorFields
  | .truth ws rs => .inl (ws,rs)
  | .sign ws rs => .inr (.inl (ws,rs))
  | .gadget ws rs => .inr (.inr (.inl (ws,rs)))
  | .unary i p => .inr (.inr (.inr (i,p)))

/-- Bit-stack encoding used for a private one-copy factor. -/
def factor (f : Factor) := sumCode (prodCode naturals booleans) (sumCode (prodCode naturals booleans)
  (sumCode (prodCode naturals naturals) (prodCode Nat.bits port))) (factorFields f)

/-- Right-associated tagged union of the four sparse public record payloads. -/
abbrev RecordFields := (ℕ × ℕ × Port) ⊕ (ℕ × ℕ × Port × Port) ⊕ (ℕ × ℕ × ℕ × ℕ) ⊕
  (ℕ × Port × ℕ × List ℕ × List Route)

/-- Tags for zero, equality, site-box, and profile records, respectively. -/
def recordFields : Record → RecordFields
  | .zero c l p => .inl (c,l,p)
  | .equal c l p q => .inr (.inl (c,l,p,q))
  | .box id base c stride => .inr (.inr (.inl (id,base,c,stride)))
  | .profile c p w h rs => .inr (.inr (.inr (c,p,w,h,rs)))

/-- Bit-stack encoding of an individual public sparse record. -/
def record (r : Record) := sumCode (prodCode Nat.bits (prodCode Nat.bits port))
  (sumCode (prodCode Nat.bits (prodCode Nat.bits (prodCode port port)))
    (sumCode (prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits)))
      (prodCode Nat.bits (prodCode port (prodCode Nat.bits (prodCode naturals (listCode route))))))) (recordFields r)

/-- Typed encoding of the boxes, records and reported subtotal bit addresses. -/
def directory (D : Directory) := prodCode (listCode (listCode factor))
  (prodCode (listCode record) (listCode naturals)) (D.boxes,D.records,D.reportedCounts)

/-- Internal typed input for the physical private validator compiler. -/
def input : ℕ × Directory → List Bool := prodCode Nat.bits directory

end CellSparse.Packet.Typed

end BorderVNP
end Computability
end OAI
