import OAI.Computability.BorderVNP.CellPacketGeometryBankFields

/-! # Compiling the final placement of a frozen heterogeneous bank row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket

open Word Inherited CellSparse
open private portWords routeWords from OAI.Computability.BorderVNP.PackedBankPacket
open private rawCode portCode routeCode from OAI.Computability.BorderVNP.PackedInheritedFields

variable {I : Type*}

/-- The final offsets move the first bit of the port and preserve its internal layout. -/
def PortCode.placed (off : WidthExpr I) (p : PortCode I) : PortCode I :=
  {p with base := .binary .add off p.base}

/-- Both ends of each compact route live in the site's final bit bank. -/
def RouteCode.placed (off : WidthExpr I) (r : RouteCode I) : RouteCode I :=
  {r with original := r.original.placed off,compact := r.compact.placed off}

/-- Shift the cell-local bit addresses and the merged box ID of a frozen record. -/
def RecordCode.placed (off idx : WidthExpr I) : RecordCode I → RecordCode I
  | .zero n w p => .zero n w (p.placed off)
  | .equal n w p q => .equal n w (p.placed off) (q.placed off)
  | .box i b n d => .box (.binary .add idx i) (.binary .add off b) n d
  | .profile n p w h rs => .profile n (p.placed off) w h (rs.map (RouteCode.placed off))

private theorem port_placed (x : I → ℕ) (off : WidthExpr I) (p : PortCode I) :
    (p.placed off).read x = (p.read x).shift (off.eval x) := rfl

private theorem route_placed (x : I → ℕ) (off : WidthExpr I) (r : RouteCode I) :
    (r.placed off).read x = (r.read x).shift (off.eval x) := rfl

/-- Compiling the final placement is exactly the semantic relocation of the frozen row. -/
theorem RecordCode.placed_read (x : I → ℕ) (off idx : WidthExpr I) (r : RecordCode I) :
    (r.placed off idx).read x = ((r.read x).shift (off.eval x)).rebaseBox (idx.eval x) := by
  cases r with
  | zero | equal | box => rfl
  | profile n p w h rs => simp [placed,read,Record.shift,Record.rebaseBox,List.map_map,Function.comp_def,port_placed,route_placed]

/-- Each scalar of the marked public history incurs at most one addition at final placement. -/
def moved (off idx : WidthExpr I) : Kind × WidthExpr I → WidthExpr I
  | (.plain,a) => a
  | (.bitAddress,a) => .binary .add off a
  | (.boxID,a) => .binary .add idx a

/-- The scalar address tags are precisely those used by the true physical relocation pass. -/
theorem RecordCode.placed_words (off idx : WidthExpr I) (r : RecordCode I) :
    (r.placed off idx).words = (markedCode r).map (moved off idx) := by
  cases r with
  | zero | equal | box => rfl
  | profile n p w h rs =>
    have raw (xs : List (WidthExpr I)) : (rawCode xs).map (moved off idx) = xs := by
      simp [rawCode,List.map_map,Function.comp_def,moved]
    have port (z : PortCode I) : (portCode z).map (moved off idx) = portWords (z.placed off) := rfl
    have route (z : RouteCode I) : (routeCode z).map (moved off idx) = routeWords (z.placed off) := rfl
    simp [placed,words,markedCode,List.map_flatMap,List.flatMap_map,raw,port,route,moved]

/-- Only the checked bit and directory prefix words and their resulting sum must fit. -/
theorem moved_fits (x : I → ℕ) (w : ℕ) (off idx : WidthExpr I) (k : Kind) (v : WidthExpr I)
    (a : off.Fits w x) (b : idx.Fits w x) (c : v.Fits w x)
    (total : k.move (off.eval x) (idx.eval x) (v.eval x) < 2^w) :
    (moved off idx (k,v)).Fits w x := by
  cases k with
  | plain => exact c
  | bitAddress => exact ⟨a,c,total⟩
  | boxID => exact ⟨b,c,total⟩

/-- The output gate charge grows by at most two nodes per serialized word
when both final offsets come directly from shared source fields. -/
theorem moved_nodes (off idx : I) (k : Kind) (v : WidthExpr I) :
    (moved (.field off) (.field idx) (k,v)).nodes ≤ v.nodes+2 := by
  cases k <;> simp [moved,WidthExpr.nodes] <;> omega

end Packing.BankPacket

namespace Packing.BankJoint

open BankPacket Crossing Shortening.StaticRows CellSparse Word

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)

/-- Operand names for frozen paid sites, together with their two final offsets. -/
abbrev PlacedFields := Bool ⊕ Prepared e

/-- Final sparse record template for a newly born or later retained seed site. -/
noncomputable def placedRowsCode (v : TemplateSite e) : List (RecordCode (PlacedFields e)) :=
  (commonRows e first v).map fun r => (r.rewire Sum.inr).placed (.field (.inl false)) (.field (.inl true))

/-- The only extra operands at final placement are the site's bit and box prefix.
Every origin, terminal and paid record uses its stored one-copy birth fields. -/
theorem placedRowsCode_read (birth : Raw e → ℕ) (off idx : ℕ) (v : TemplateSite e) :
    let x := Sum.elim (fun b => if b then idx else off) (word e birth)
    (placedRowsCode e first v).map (RecordCode.read x) =
      (emitted e first birth v).map fun r => (r.shift off).rebaseBox idx := by
  intro x
  rw [← commonRows_read e first birth v]
  simp [placedRowsCode,List.map_map,Function.comp_def,RecordCode.placed_read,RecordCode.rewire_read,
    WidthExpr.eval,x]

end Packing.BankJoint

end BorderVNP
end Computability
end OAI
