import OAI.Computability.BorderVNP.CellProfileEmit
import OAI.Computability.BorderVNP.CellProfileWidths
import OAI.Computability.BorderVNP.CellEmitBoxes

/-! # The complete native serializer of public cell wiring guards

The public directory supplies four tagged record payloads. Box references compare
their ID with the real number of stored private box descriptions. Profiles use
their finite histogram to bound the iteration needed to print selector tests.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

/-- Source encoding for zero pinning. -/
abbrev zeroCode := prodCode Nat.bits (prodCode Nat.bits Typed.port)

/-- Source encoding for range equality. -/
abbrev equalCode := prodCode Nat.bits (prodCode Nat.bits (prodCode Typed.port Typed.port))

private noncomputable def zeroPayload : Statement zeroCode (fun x => zeroRow x.1 x.2.1 x.2.2) := by
  let copies := Procedure.first Nat.bits (prodCode Nat.bits Typed.port)
  let rest := Procedure.second Nat.bits (prodCode Nat.bits Typed.port)
  let lanes := (Procedure.first ..).comp rest
  let port := (Procedure.second ..).comp rest
  let addr := portAddr port (constAddr zeroCode (.index 1)) (constAddr zeroCode (.index 0))
  exact loopStmt (litAddr copies) (loopStmt (litAddr lanes) (guardBool (notBool (wireBool addr))))

private noncomputable def equalPayload : Statement equalCode (fun x => equalRow x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let copies := Procedure.first Nat.bits (prodCode Nat.bits (prodCode Typed.port Typed.port))
  let rest := Procedure.second Nat.bits (prodCode Nat.bits (prodCode Typed.port Typed.port))
  let lanes := (Procedure.first ..).comp rest
  let ports := (Procedure.second ..).comp rest
  let a := (Procedure.first ..).comp ports
  let b := (Procedure.second ..).comp ports
  let i := constAddr equalCode (.index 1)
  let k := constAddr equalCode (.index 0)
  let guard := guardBool (equalBool (wireBool (portAddr a i k)) (wireBool (portAddr b i k)))
  exact loopStmt (litAddr copies) (loopStmt (litAddr lanes) guard)

private def isBox : Record → Bool
  | .box .. => true
  | _ => false

private def boxId : Record → ℕ
  | .box i .. => i
  | _ => 0

private noncomputable def getIsBox : Procedure Typed.record boolCode isBox := by
  let tag := Procedure.casesSum (Procedure.constant zeroCode boolCode false)
    (Procedure.casesSum (Procedure.constant equalCode boolCode false)
      (Procedure.casesSum (Procedure.constant refCode boolCode true) (Procedure.constant ProfileData.code boolCode false)))
  exact (tag.precompose Typed.recordFields).congrFun (by intro r; cases r <;> rfl)

private noncomputable def getBoxId : Procedure Typed.record Nat.bits boxId := by
  let get := Procedure.casesSum (Procedure.constant zeroCode Nat.bits 0) (Procedure.casesSum
    (Procedure.constant equalCode Nat.bits 0) (Procedure.casesSum (Procedure.first Nat.bits (prodCode Nat.bits (prodCode Nat.bits Nat.bits)))
      (Procedure.constant ProfileData.code Nat.bits 0)))
  exact (get.precompose Typed.recordFields).congrFun (by intro r; cases r <;> rfl)

private def fieldGuard (r : Record) : Stmt :=
  match r with
  | .box .. => .nil
  | _ => recordGuard [] r.clipProfile

private noncomputable def fieldGuardP : Statement Typed.record fieldGuard := by
  let select := Procedure.casesSum zeroPayload (Procedure.casesSum equalPayload
    (Procedure.casesSum (constStmt refCode .nil) profilePacket))
  exact (select.precompose Typed.recordFields).congrFun (by intro r; cases r <;> rfl)

/-- The guard of one record needs only the scalar number of available boxes. -/
def countedGuard (n : ℕ) (r : Record) : Stmt :=
  match r with
  | .box i .. => (Term.lit (decide (i<n))).guard
  | _ => fieldGuard r

/-- The leaf serializer receives only a box count and one physical record. -/
noncomputable def smallGuard : Statement (prodCode Nat.bits Typed.record) (fun x => countedGuard x.1 x.2) := by
  let n := Procedure.first Nat.bits Typed.record
  let row := Procedure.second Nat.bits Typed.record
  let box := guardBool (literalBool (Procedure.binaryLt.comp ((getBoxId.comp row).pair n)))
  let fields := fieldGuardP.comp row
  let pick := Procedure.conditional (getIsBox.comp row) box fields
  exact pick.congrFun (by intro ⟨i,r⟩; cases r <;> rfl)

/-- The isolated leaf uses exactly the same box-presence condition as the original checker. -/
theorem countedGuard_eq (boxes : List (List Factor)) (r : Record) :
    countedGuard boxes.length r = recordGuard boxes r.clipProfile := by cases r <;> rfl

/-- Count the actual stored boxes once before traversing any public record. -/
noncomputable def getBoxCount : Procedure Typed.directory Nat.bits (fun d => d.boxes.length) :=
  (Procedure.listLength (listCode Typed.factor) []).comp getBoxes

/-- Print one physical wiring guard, looking up the directory extent for the box-ID case. -/
noncomputable def getRecordGuard : Statement (prodCode Typed.directory Typed.record)
    (fun x => recordGuard x.1.boxes x.2.clipProfile) :=
  (smallGuard.comp ((getBoxCount.comp (Procedure.first Typed.directory Typed.record)).pair
    (Procedure.second Typed.directory Typed.record))).congrFun (fun x => congrArg (CellMacro.Generator.serialized 8)
      (countedGuard_eq x.1.boxes x.2))

/-- The fixed, deterministic record translator traverses the public list in its
actual order. It forwards one binary scalar and the current record to each leaf. -/
noncomputable def getRecordGuards : Statement Typed.directory (fun D => D.clipProfiles.recordGuards) := by
  let gather := getBoxCount.pair getRecords
  let rows := (Procedure.listMapWith (f := fun n r => CellMacro.Generator.serialized 8 (countedGuard n r))
    (.box 0 0 0 0) [] smallGuard).comp gather
  exact (Procedure.listJoinWords.comp rows).congrFun (fun x => by
    change (x.records.map (fun r => CellMacro.Generator.serialized 8 (countedGuard x.boxes.length r))).flatten = _
    simp only [countedGuard_eq,Directory.recordGuards,Directory.clipProfiles,serialized_sequence_list,
      List.flatMap_def,List.map_map]
    rfl)

/-- On directories whose profiles come from the crossing construction, the emitted word
is exactly the serialization of the original unmodified record sequence. -/
noncomputable def getValidRecordGuards : Statement (fun D : {d : Directory // d.ProfileWidths} => Typed.directory D.val)
    (fun D => D.val.recordGuards) :=
  (getRecordGuards.precompose Subtype.val).congrFun (fun x => by
    change CellMacro.Generator.serialized 8 x.val.clipProfiles.recordGuards = _
    rw [x.val.clipProfiles_eq x.property])

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
