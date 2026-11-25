import OAI.Computability.BorderVNP.CubePhysicalDeclaredPaths
import OAI.Computability.BorderVNP.CubePhysicalPadding
import OAI.Computability.BorderVNP.ParseBatchScalarExtension

/-! # The ordinary field sum after packet substitution in a placed cell network

Each branch uses the actual crossing-cable enumeration. Its bits occupy
disjoint intervals in the padded bins of ordered cell labels. A summand
retains every private bit, singleton, independently opened end, cube
selector, and internal cube wire. The public declaration is then uniquely
determined by these selectors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open Crossing Cube Cube.Physical Diagonal.CellEntries MvPolynomial
open scoped BigOperators Classical
set_option synthInstance.maxSize 1024
set_option maxRecDepth 6000

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits} {F : Type*} [CommRing F]

/-- The packet layout of one selected geometry history. The bin capacity
bound makes the real directory into an injection into the padded slots. -/
structure FieldPacketPlan (N : Network D P bits) (F : Type*) [CommRing F] where
  /-- The actual cells containing the host tensor sites. -/
  Cell : Type
  finiteCell : Fintype Cell
  decEqCell : DecidableEq Cell
  /-- The cell containing each site. -/
  cell : N.Site → Cell
  /-- The cube has one more direction than this index. -/
  dimension : ℕ
  /-- Number of available symbols in each coordinate. -/
  alphabet : ℕ
  /-- Number of blocks per oriented bin. -/
  blocks : ℕ
  /-- Number of demand bits in each parallel copy. -/
  bitWidth : ℕ
  /-- Number of copies in a demand block. -/
  copies : ℕ
  /-- Number of base alternatives used by the cube selector. -/
  alternatives : ℕ
  /-- Supply wire parameter of the cube tables. -/
  supply : ℕ
  /-- Publicly enumerated crossing cables. -/
  count : ℕ
  /-- Public row order of the surviving crossing cables. -/
  order : N.CrossingEdge cell ≃ Fin count
  /-- Product label of each cell. -/
  label : Cell → Label (dimension+1) alphabet
  capacity : ∀ u, load (cablePair order (crossSrc N cell) (crossDst N cell) label)
    (crossWidth N cell ∘ order.symm) u ≤ blocks*(copies*bitWidth)
  /-- Each packet uses its actual scalar table. -/
  table : Packet dimension alphabet blocks → TableEntry dimension bitWidth copies alternatives supply → F
  valid : ∀ i, ValidTables (table i)

attribute [instance] FieldPacketPlan.finiteCell FieldPacketPlan.decEqCell

namespace FieldPacketPlan

variable (L : FieldPacketPlan N F)

/-- The actual slot of an original crossing bit. -/
def slot := packedSlotEmbedding N L.cell L.order L.label L.blocks (L.copies*L.bitWidth) L.capacity

/-- The exact fully assigned post-packet term. -/
abbrev Path := Physical.Path N L.cell L.dimension L.alphabet L.blocks L.bitWidth L.copies L.alternatives L.supply

/-- The public encoded grouping coordinate and all directional row lengths. -/
abbrev Declaration := Broadcast L.dimension L.alphabet
  (declarationCap L.dimension L.alphabet L.blocks L.bitWidth L.copies L.supply)

/-- One ordinary field-valued table entry contributes its scalar once. -/
noncomputable def scalarTags (T : N.Tables F) : N.Tables (Entry Empty F) :=
  fun v a x => gadget (T v a x)

private noncomputable def scalarEval : MvPolynomial Empty F →+* F :=
  eval Empty.elim

/-- Product of the host cell entries and every selected cube table entry,
including the two real zero pins on each unused bin position. -/
noncomputable def weight (T : N.Tables F) (x : Ports bits) (a : L.Path) : F :=
  scalarEval (interpret id (pathTag N L.cell L.slot (scalarTags T) x L.table a))

/-- The complete cube term sum equals the original host tensor at every input. -/
theorem value_eq_sum (T : N.Tables F) (x : Ports bits) :
    N.value T x = ∑ a : L.Path, L.weight T x a := by
  let tags := scalarTags T
  have he := value_eq_physical_paths N L.cell L.slot tags x L.table (id : F → F) L.valid
  have h := congrArg (scalarEval (F := F)) he
  simpa only [Network.value, Network.read, tags, scalarTags, scalarEval, interpret_gadget, id_eq,
    map_sum, map_prod, eval_C, weight] using h

/-- The public grouping declaration which the original row checks accept. -/
def declaration (a : L.Path) : L.Declaration :=
  broadcast L.bitWidth L.supply (pathSelectors N L.cell a)

/-- A physical declaration passes exactly at the value forced by the
assigned packet selectors. -/
theorem passes_iff (a : L.Path) (r : L.Declaration) :
    passesBroadcast L.bitWidth L.supply (pathSelectors N L.cell a) r ↔ r = L.declaration a :=
  passesBroadcast_iff ..

/-- Adding the actual checked public word array to a term preserves its
multiplicity, even when the interpreted field value vanishes. -/
def declaredEquiv : L.Path ≃ {v : L.Declaration × L.Path //
    passesBroadcast L.bitWidth L.supply (pathSelectors N L.cell v.2) v.1} where
  toFun a := ⟨(L.declaration a,a),(L.passes_iff ..).mpr rfl⟩
  invFun v := v.val.2
  left_inv _ := rfl
  right_inv v := Subtype.ext (Prod.ext ((L.passes_iff ..).mp v.property).symm rfl)

end FieldPacketPlan
end FiniteDiagonal

end BorderVNP
end Computability
end OAI
