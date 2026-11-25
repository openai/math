import OAI.Hierarchy.TaggedWideDatedAddresses
import OAI.Hierarchy.TaggedWidePrefixNative
import OAI.Hierarchy.TaggedWideOverlapNative

namespace OAI
/-! # Native fields compiled for a dated role and its signed overlap -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open ProbeStage.CoreBoard.HistoryRoles
open scoped Classical Fin.CommRing BigOperators

/-- Stable field order. Each endpoint gets its real aggregation and room;
each twice-indexed old/new role gets a prefix length and two displacements. -/
abbrev ApertureField (D : ℕ) := (Fin D × Fin D) ⊕ ((Fin D × Bool) ⊕ Fin D)
abbrev Field (D : ℕ) := (Bool × ApertureField D) ⊕ ((Fin D × Fin D) × Fin 3)

def columns {D : ℕ} (n start sites strideBits : ℕ) (table : Bank) (here : Expr) (q : Fin D) :
    LocalPrefix.Columns :=
  let field := fun i : Fin 3=>pageRead (DatedRoleSheets.bank n start (sites*D) strideBits i) table here q
  ⟨field 1, field 2, field 0⟩

def active (width yes : Expr) : Expr := .branch .eq width (.lit 0) (.lit 0) yes

def weight (a b : LocalPrefix.Columns) : Expr :=
  active b.width (.branch .eq a.opposite b.opposite a.width (.lit 0))

def common {D : ℕ} (row : Fin D→LocalPrefix.Columns) (i : Fin D) :=
  active (row i).width (LocalPrefix.expr row (row i))

def aperture {D : ℕ} (cap : ℕ) (row : Fin D→LocalPrefix.Columns) : ApertureField D→Expr
  | .inl (q,i)=>weight (row q) (row i)
  | .inr (.inl (i,b))=>if b then Overlap.small (.lit cap) (common row i) else .lit 0
  | .inr (.inr i)=>LocalPrefix.total D (fun j=>weight (row j) (row i))

def interval {D : ℕ} (row : Fin D→LocalPrefix.Columns) (low : Fin D→Expr) (i : Fin D) :
    Overlap.Fields := ⟨common row i,(row i).width,low i,(row i).opposite⟩

def compile {D : ℕ} (cap : ℕ) (row : Bool→Fin D→LocalPrefix.Columns) (low : Bool→Fin D→Expr) :
    Field D→Expr
  | .inl (b,f)=>aperture cap (row b) f
  | .inr ((i,j),q)=>
    let a:=interval (row false) (low false) i
    let b:=interval (row true) (low true) j
    if q=0 then Overlap.length a b else Overlap.head cap a b (if q=1 then a else b)

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
