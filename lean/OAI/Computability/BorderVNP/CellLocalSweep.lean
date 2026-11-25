import OAI.Computability.BorderVNP.CellLocalFactor
import OAI.Computability.BorderVNP.CellEmitSweep

/-! # Preparing short per-factor packets during the private site scan

The sweep parameters are computed before its box traversal. Each box materializes its
start, base, stride, factor count and copy count, and retains its one-copy factor list.
A factor invocation then receives only the block header, its own ordinal and its own table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

open ExactQuantumFactoring.BitStackProgram
open private sweep_eq_sequence from OAI.Computability.BorderVNP.CellEmitSweep

/-- Sweep parameters, starting occurrence and a single resolved box. -/
abbrev BlockArg := Params × ℕ × BoxBlock

/-- Materialized block header, copy count and its one-copy list of factors. -/
abbrev BlockData := (Params × BlockFields) × (ℕ × List Factor)

/-- Encode the sweep parameters, starting occurrence and box for a single visit. -/
abbrev blockArgCode := prodCode paramsCode (prodCode Nat.bits blockCode)
/-- Encode the parameters and materialized block fields together with the copy count and
the factor list for one copy. -/
abbrev blockDataCode := prodCode (prodCode paramsCode fieldsCode) (prodCode Nat.bits (listCode Typed.factor))

/-- Compute the fields shared across the factors of one repeated box. -/
def prepare (b : BlockArg) : BlockData :=
  ((b.1,b.2.1,b.2.2.base,b.2.2.stride,b.2.2.factors.length),b.2.2.copies,b.2.2.factors)

/-- Actual procedure reading a box and computing its factor count once before the factor loop. -/
noncomputable def prepareBlock : Procedure blockArgCode blockDataCode prepare := by
  let p := Procedure.first paramsCode (prodCode Nat.bits blockCode)
  let tail := Procedure.second paramsCode (prodCode Nat.bits blockCode)
  let start := (Procedure.first Nat.bits blockCode).comp tail
  let box := (Procedure.second Nat.bits blockCode).comp tail
  let fs := blockFactors.comp box
  let count := (Procedure.listLength Typed.factor (.truth [] [])).comp fs
  let fields := start.pair ((blockBase.comp box).pair ((blockStride.comp box).pair count))
  exact (p.pair fields).pair ((blockCopies.comp box).pair fs)

/-- Project one short factor packet from an indexed traversal of the stored one-copy list. -/
noncomputable def itemPacket : Procedure (prodCode blockDataCode (prodCode Nat.bits Typed.factor)) code
    (fun x => (x.1.1,x.2)) := by
  let owner := Procedure.first blockDataCode (prodCode Nat.bits Typed.factor)
  let ctx := (Procedure.first (prodCode paramsCode fieldsCode) (prodCode Nat.bits (listCode Typed.factor))).comp owner
  exact ctx.pair (Procedure.second blockDataCode (prodCode Nat.bits Typed.factor))

/-- The precise command tree printed from prepared scalar fields and the list of factors. -/
def blockTree (mode : Pass) (b : BlockData) : Stmt :=
  .loop (.lit b.2.1) (sequence (b.2.2.zipIdx.map (fun fj =>
    body mode b.1.1 fj.1 (index (b.1,fj.2,fj.1) 0) (offset (b.1,fj.2,fj.1) 0) (.index 0))))

/-- Print one loop header and each stored factor's one-copy body. -/
noncomputable def blockPrinter (mode : Pass) : Statement blockDataCode (blockTree mode) := by
  let t := Procedure.second (prodCode paramsCode fieldsCode) (prodCode Nat.bits (listCode Typed.factor))
  let copies := (Procedure.first Nat.bits (listCode Typed.factor)).comp t
  let fs := (Procedure.second Nat.bits (listCode Typed.factor)).comp t
  let row := (printer mode).comp itemPacket
  let cmds := sequenceMapIdx (f := fun (b : BlockData) j f => body mode b.1.1 f
    (index (b.1,j,f) 0) (offset (b.1,j,f) 0) (.index 0)) (.truth [] []) fs row
  exact loopStmt (litAddr copies) cmds

/-- The prepared box printer emits precisely its original sparse fragment. -/
noncomputable def fragment (mode : Pass) : Statement blockArgCode (fun b =>
    b.2.2.fragment b.2.1 (body mode b.1)) := by
  have eq (b : BlockArg) : blockTree mode (prepare b) = b.2.2.fragment b.2.1 (body mode b.1) := rfl
  exact ((blockPrinter mode).comp prepareBlock).congrFun (fun x => congrArg (CellMacro.Generator.serialized 8) (eq x))

/-- Native box visit input. Its first part is the already prepared sweep parameter tuple. -/
abbrev SweepInput := Params × Directory

/-- Encode the fixed sweep parameters and the directory to traverse. -/
abbrev sweepCode := prodCode paramsCode Typed.directory
/-- Extend a sweep input with the index and contents of the box being visited. -/
abbrev visitCode := prodCode sweepCode (prodCode Nat.bits blockCode)

/-- Find the globally correct start of this particular block and transfer its local tuple. -/
noncomputable def visitPacket : Procedure visitCode blockArgCode (fun x =>
    (x.1.1,(((x.1.2.blocks).take x.2.1).map fun b => b.copies*b.factors.length).sum,x.2.2)) := by
  let owner := Procedure.first sweepCode (prodCode Nat.bits blockCode)
  let item := Procedure.second sweepCode (prodCode Nat.bits blockCode)
  let p := (Procedure.first paramsCode Typed.directory).comp owner
  let d := (Procedure.second paramsCode Typed.directory).comp owner
  let i := (Procedure.first Nat.bits blockCode).comp item
  let b := (Procedure.second Nat.bits blockCode).comp item
  let start := getBlockStart.comp (d.pair i)
  exact p.pair (start.pair b)

/-- Mathematical visit addressed by an indexed box row. -/
def visitTree (mode : Pass) (x : SweepInput) (j : ℕ) (b : BoxBlock) : Stmt :=
  b.fragment (((x.2.blocks.take j).map fun t => t.copies*t.factors.length).sum) (body mode x.1)

/-- Prepare and run this particular visited box. -/
noncomputable def visitStmt (mode : Pass) : Statement visitCode (fun x => visitTree mode x.1 x.2.1 x.2.2) :=
  ((fragment mode).comp visitPacket).congrFun (fun _ => rfl)

private theorem visit_sequence (mode : Pass) (x : SweepInput) :
    sequence (x.2.blocks.zipIdx.map (fun bj => visitTree mode x bj.2 bj.1)) =
      sweep (body mode x.1) x.2.blocks 0 := by
  rw [sweep_eq_sequence,List.mapIdx_eq_zipIdx_map]
  simp only [Nat.zero_add,visitTree]

/-- Sweep the boxes in public order, with fixed precomputed sweep parameters. -/
noncomputable def sweepPrinter (mode : Pass) : Statement sweepCode (fun x => sweep (body mode x.1) x.2.blocks 0) := by
  let blocks := getBlocks.comp (Procedure.second paramsCode Typed.directory)
  let out := sequenceMapIdx (f := visitTree mode) (⟨0,0,0,[]⟩ : BoxBlock) blocks (visitStmt mode)
  exact out.congrFun (fun x => congrArg (CellMacro.Generator.serialized 8) (visit_sequence mode x))

/-- Prepare parameters once from the caller and run the fixed local-packet sweep. -/
noncomputable def sweepStmt {α : Type} {ea : α → List Bool} {dir : α → Directory} {ps : α → Params}
    (mode : Pass) (hd : Procedure ea Typed.directory dir) (hp : Procedure ea paramsCode ps) :
    Statement ea (fun x => sweep (body mode (ps x)) (dir x).blocks 0) :=
  (sweepPrinter mode).comp (hp.pair hd)

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
