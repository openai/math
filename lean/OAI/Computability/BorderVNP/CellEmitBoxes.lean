import OAI.Computability.BorderVNP.CellEmitLists
import OAI.Computability.BorderVNP.CellSparseSweep
import OAI.Computability.QuantumFactoring.BitStackListFlatten
import OAI.Computability.QuantumFactoring.BitStackListLength

/-! # Resolving private box references on actual bit stacks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- Stored field encodings for the three sections of a sparse directory. -/
abbrev boxesCode := listCode (listCode Typed.factor)
/-- Stored list of public records. -/
abbrev recordsCode := listCode Typed.record
/-- Stored reported subtotal bit addresses. -/
abbrev reportsCode := listCode Typed.naturals

/-- Recover the table directory from the complete typed packet. -/
noncomputable def getBoxes : Procedure Typed.directory boxesCode Directory.boxes :=
  (Procedure.first boxesCode (prodCode recordsCode reportsCode)).precompose
    (fun D : Directory => (D.boxes,D.records,D.reportedCounts))

/-- Recover the public record list. -/
noncomputable def getRecords : Procedure Typed.directory recordsCode Directory.records :=
  ((Procedure.first recordsCode reportsCode).comp (Procedure.second boxesCode (prodCode recordsCode reportsCode))).precompose
    (fun D : Directory => (D.boxes,D.records,D.reportedCounts))

/-- Recover the report vector. -/
noncomputable def getReports : Procedure Typed.directory reportsCode Directory.reportedCounts :=
  ((Procedure.second recordsCode reportsCode).comp (Procedure.second boxesCode (prodCode recordsCode reportsCode))).precompose
    (fun D : Directory => (D.boxes,D.records,D.reportedCounts))

/-- Identifier, base, multiplicity and stride of a site-box reference. -/
abbrev Ref := ℕ × ℕ × ℕ × ℕ

/-- Encoding of a public box reference. -/
abbrev refCode := prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits))

/-- A box reference or the empty list for another row kind. -/
def refOf : Record → List Ref
  | .box id base c stride => [(id,base,c,stride)]
  | _ => []

/-- A tagged native dispatcher extracts public box rows in order. -/
noncomputable def getRef : Procedure Typed.record (listCode refCode) refOf := by
  let once : Procedure refCode (listCode refCode) (fun x => [x]) :=
    (Procedure.listCons refCode).comp ((Procedure.identity refCode).pair (Procedure.constant _ _ []))
  let zero := prodCode Nat.bits (prodCode Nat.bits Typed.port)
  let equal := prodCode Nat.bits (prodCode Nat.bits (prodCode Typed.port Typed.port))
  let profile := prodCode Nat.bits (prodCode Typed.port (prodCode Nat.bits (prodCode Typed.naturals (listCode Typed.route))))
  let get := Procedure.casesSum (Procedure.constant zero (listCode refCode) ([] : List Ref))
    (Procedure.casesSum (Procedure.constant equal (listCode refCode) [])
      (Procedure.casesSum once (Procedure.constant profile (listCode refCode) [])))
  exact (get.precompose Typed.recordFields).congrFun (by intro r; cases r <;> rfl)

/-- Physical computation of the complete compact reference sequence. -/
noncomputable def getRefs : Procedure Typed.directory (listCode refCode) (fun D => D.records.flatMap refOf) :=
  ((Procedure.listFlatten refCode (0,0,0,0)).comp ((Procedure.listMap (.box 0 0 0 0) [] getRef).comp getRecords)).congrFun
    (fun _ => List.flatMap_def.symm)

/-- Internal encoding of one resolved box, preserving a single copy of its factor list. -/
def blockCode (b : BoxBlock) := prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits (listCode Typed.factor)))
  (b.base,b.copies,b.stride,b.factors)

private def resolve (boxes : List (List Factor)) (r : Ref) : BoxBlock :=
  ⟨r.2.1,r.2.2.1,r.2.2.2,boxes.getD r.1 []⟩

private theorem drop_headD {α : Type} (xs : List α) (i : ℕ) (d : α) :
    (xs.drop i).headD d = xs.getD i d := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

private noncomputable def resolveP :
    Procedure (prodCode boxesCode refCode) blockCode (fun x => resolve x.1 x.2) := by
  let boxes := Procedure.first boxesCode refCode
  let r := Procedure.second boxesCode refCode
  let id := (Procedure.first Nat.bits _).comp r
  let args := (Procedure.second Nat.bits _).comp r
  let base := (Procedure.first Nat.bits _).comp args
  let rest := (Procedure.second Nat.bits _).comp args
  let copies := (Procedure.first Nat.bits Nat.bits).comp rest
  let stride := (Procedure.second Nat.bits Nat.bits).comp rest
  let factors := (Procedure.listGet (listCode Typed.factor) []).comp (id.pair boxes)
  exact (base.pair (copies.pair (stride.pair factors))).result (by
    rintro ⟨tables,r⟩
    change prodCode _ _ (r.2.1,r.2.2.1,r.2.2.2,(tables.drop r.1).headD []) = _
    rw [drop_headD]
    rfl)

private theorem blocks_eq (D : Directory) :
    (D.records.flatMap refOf).map (resolve D.boxes) = D.blocks := by
  rcases D with ⟨boxes,rs,counts⟩
  induction rs with
  | nil => rfl
  | cons r rs ih => cases r <;> simp [Directory.blocks,refOf,resolve] at ih ⊢ <;> exact ih

/-- The real stack compiler performs every private table lookup needed for the
compact repeated-site scan, even when several public references name one site. -/
noncomputable def getBlocks : Procedure Typed.directory (listCode blockCode) Directory.blocks :=
  (((Procedure.listMapWith (0,0,0,0) ⟨0,0,0,[]⟩ resolveP).comp (getBoxes.pair getRefs))).congrFun blocks_eq

/-- Read each of the four encoded fields of a resolved box. -/
def blockFields (b : BoxBlock) := (b.base,b.copies,b.stride,b.factors)

/-- Native access to a resolved base address. -/
noncomputable def blockBase : Procedure blockCode Nat.bits BoxBlock.base :=
  (Procedure.first Nat.bits _).precompose blockFields

/-- Native access to the repeated box multiplicity. -/
noncomputable def blockCopies : Procedure blockCode Nat.bits BoxBlock.copies :=
  ((Procedure.first Nat.bits _).comp (Procedure.second Nat.bits _)).precompose blockFields

/-- Native access to the stride between copies. -/
noncomputable def blockStride : Procedure blockCode Nat.bits BoxBlock.stride :=
  ((Procedure.first Nat.bits _).comp ((Procedure.second Nat.bits _).comp (Procedure.second Nat.bits _))).precompose blockFields

/-- Access the actual one-copy table descriptions. -/
noncomputable def blockFactors : Procedure blockCode (listCode Typed.factor) BoxBlock.factors :=
  ((Procedure.second Nat.bits _).comp ((Procedure.second Nat.bits _).comp (Procedure.second Nat.bits _))).precompose blockFields

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
