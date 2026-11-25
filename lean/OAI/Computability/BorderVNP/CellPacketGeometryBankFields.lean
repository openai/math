import OAI.Computability.BorderVNP.PackedInheritedFields
import OAI.Computability.BorderVNP.PackedBankEmit

/-! # A shared operand type for the sparse records of heterogeneous seed sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Word.WidthExpr

variable {I J : Type*}

/-- Connect a site's local operand name to the corresponding common field. -/
def rewire (f : I → J) : WidthExpr I → WidthExpr J
  | .const n => .const n
  | .field i => .field (f i)
  | .binary op a b => .binary op (a.rewire f) (b.rewire f)

/-- Rewiring evaluates the very same arithmetic expression on the selected fields. -/
theorem rewire_eval (f : I → J) (x : J → ℕ) (a : WidthExpr I) :
    (a.rewire f).eval x = a.eval (x ∘ f) := by induction a <;> simp [rewire,eval, *]

/-- Rewiring adds zero arithmetic nodes to the expression. -/
theorem rewire_nodes (f : I → J) (a : WidthExpr I) : (a.rewire f).nodes = a.nodes := by
  induction a <;> simp [rewire,nodes, *]

/-- Every intermediate word has the same fit condition after pin selection. -/
theorem rewire_fits (f : I → J) (x : J → ℕ) (w : ℕ) (a : WidthExpr I) :
    (a.rewire f).Fits w x ↔ a.Fits w (x ∘ f) := by induction a <;> simp [rewire,Fits,rewire_eval, *]

end Packing.Word.WidthExpr

namespace Packing.BankPacket

open Word Inherited CellSparse
open private portWords routeWords from OAI.Computability.BorderVNP.PackedBankPacket

variable {I J : Type*}

/-- Select the three common port fields of a local record. -/
def PortCode.rewire (f : I → J) (p : PortCode I) : PortCode J :=
  ⟨p.base.rewire f,p.copyStride.rewire f,p.laneStride.rewire f⟩

/-- Select the common field names of both sides of a compact profile route. -/
def RouteCode.rewire (f : I → J) (r : RouteCode I) : RouteCode J :=
  ⟨r.term.rewire f,r.lanes.rewire f,r.original.rewire f,r.compact.rewire f⟩

/-- All record constructors and packet lengths are preserved by the common wiring. -/
def RecordCode.rewire (f : I → J) : RecordCode I → RecordCode J
  | .zero n w p => .zero (n.rewire f) (w.rewire f) (p.rewire f)
  | .equal n w p q => .equal (n.rewire f) (w.rewire f) (p.rewire f) (q.rewire f)
  | .box i b n d => .box (i.rewire f) (b.rewire f) (n.rewire f) (d.rewire f)
  | .profile n p w h rs => .profile (n.rewire f) (p.rewire f) (w.rewire f)
      (h.map (WidthExpr.rewire f)) (rs.map (RouteCode.rewire f))

private theorem port_read (f : I → J) (x : J → ℕ) (p : PortCode I) :
    (p.rewire f).read x = p.read (x ∘ f) := by simp [PortCode.rewire,PortCode.read,WidthExpr.rewire_eval]

private theorem route_read (f : I → J) (x : J → ℕ) (r : RouteCode I) :
    (r.rewire f).read x = r.read (x ∘ f) := by simp [RouteCode.rewire,RouteCode.read,port_read,WidthExpr.rewire_eval]

/-- The site's typed record uses the same real numerical operands on every branch. -/
theorem RecordCode.rewire_read (f : I → J) (x : J → ℕ) (r : RecordCode I) :
    (r.rewire f).read x = r.read (x ∘ f) := by
  cases r <;> simp [RecordCode.rewire,RecordCode.read,WidthExpr.rewire_eval,port_read,route_read,
    List.map_map,Function.comp_def]

private theorem port_words (f : I → J) (p : PortCode I) :
    portWords (p.rewire f) = (portWords p).map (WidthExpr.rewire f) := rfl

private theorem route_words (f : I → J) (r : RouteCode I) :
    routeWords (r.rewire f) = (routeWords r).map (WidthExpr.rewire f) := rfl

/-- The tagged packet expressions use the same word ordinal before and after wiring. -/
theorem RecordCode.rewire_words (f : I → J) (r : RecordCode I) :
    (r.rewire f).words = r.words.map (WidthExpr.rewire f) := by
  cases r with
  | zero | equal | box => rfl
  | profile n p w h rs =>
    simp [RecordCode.rewire,RecordCode.words,List.flatMap_map,List.map_flatMap,port_words,route_words,WidthExpr.rewire]

/-- Counts and each indexed word of the entire physical record stream survive the wiring. -/
theorem tape_rewire (f : I → J) (rs : List (RecordCode I)) :
    tape (rs.map (RecordCode.rewire f)) = (tape rs).map (WidthExpr.rewire f) := by
  simp only [tape,List.length_map,List.map_cons,WidthExpr.rewire,List.flatMap_map,List.map_flatMap]
  congr 1
  exact List.flatMap_congr fun r _ => r.rewire_words f

end Packing.BankPacket

namespace Packing.BankJoint

open BankPacket Crossing Shortening.StaticRows CellSparse Word
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)

/-- Fixed record formats in a common operand type for all origin, terminal and
paid sites of a seed. The actual input pin map is the physical bank's own map. -/
noncomputable def commonRows (v : TemplateSite e) : List (RecordCode (Prepared e)) :=
  (rows e first v).map (RecordCode.rewire (pin e v))

/-- Reading common fields produces the real bank's origin, terminal, or paid records. -/
theorem commonRows_read (raw : Raw e → ℕ) (v : TemplateSite e) :
    (commonRows e first v).map (RecordCode.read (word e raw)) = emitted e first raw v := by
  simp [commonRows,emitted,List.map_map,Function.comp_def,RecordCode.rewire_read]

/-- The true bank output ordinal is also the ordinal in the common geometry format. -/
theorem commonRows_tape (v : TemplateSite e) :
    tape (commonRows e first v) = (tape (rows e first v)).map (WidthExpr.rewire (pin e v)) :=
  tape_rewire ..

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
