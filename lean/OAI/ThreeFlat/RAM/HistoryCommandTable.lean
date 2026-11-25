import OAI.ThreeFlat.RAM.HistoryJoinController

namespace OAI
/-! # Native materialization of seven-word ordered join headers

Each task points to its child's and parent's compact node records. It also
contains the pin-map base and two prefix counts within that parent. Each
node record stores row-stream base, public pin count, row count and shared
private-bit count. All records are constant-size, even if the expanded child
stream contains many factors.
-/

namespace ThreeFlat.RAM.HistoryCommandTable

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr HistoryJoinScan

variable {w k : ℕ}

structure Node (α : Type*) where
  rowsBase : α
  pins : α
  rows : α
  shared : α

structure Task (α : Type*) where
  child : α
  parent : α
  pinMap : α
  rowPrefix : α
  bitPrefix : α

def readNode (m : Memory w) (a : Word w) : Node (Word w) :=
  ⟨m (a+0).val,m (a+1).val,m (a+2).val,m (a+3).val⟩

def readTask (m : Memory w) (a : Word w) : Task (Word w) :=
  ⟨m (a+0).val,m (a+1).val,m (a+2).val,m (a+3).val,m (a+4).val⟩

def Task.header {α : Type*} [Add α] [Mul α] [OfNat α 4] (a : Task α) (child parent : Node α) : Header α :=
  ⟨child.rowsBase,parent.rowsBase+4*a.rowPrefix,a.pinMap,child.pins,parent.pins,parent.shared+a.bitPrefix⟩

def Task.past {α : Type*} [Add α] [Mul α] [OfNat α 4] (a : Task α) (child parent : Node α) :=
  (a.header child parent).dest + 4*child.rows

/-- `Task i` is laid out as a five-word record. `vs` holds current output
address, command-table start, and compact task-table start. -/
def term (w k : ℕ) : Term w k 3 :=
  let delta := Term.binary .sub (.result 0) (.result 1)
  let i := Term.binary .div delta (.literal 7)
  let col := Term.binary .mod delta (.literal 7)
  let t := Term.binary .add (.result 2) (Term.binary .mul (.literal 5) i)
  let fld (a : Term w k 3) (v : Word w) := (Term.binary .add a (.literal v)).load
  let child := fld t 0
  let parent := fld t 1
  let dest := Term.binary .add (fld parent 0) (Term.binary .mul (.literal 4) (fld t 3))
  let offset := Term.binary .add (fld parent 3) (fld t 4)
  let endAddr := Term.binary .add dest (Term.binary .mul (.literal 4) (fld child 2))
  Term.select .eq col (.literal 0) (fld child 0) <|
  Term.select .eq col (.literal 1) dest <|
  Term.select .eq col (.literal 2) (fld t 2) <|
  Term.select .eq col (.literal 3) (fld child 1) <|
  Term.select .eq col (.literal 4) (fld parent 1) <|
  Term.select .eq col (.literal 5) offset endAddr

def selectWord (u : Header (Word w)) (past col : Word w) :=
  if col = 0 then u.source else if col = 1 then u.dest else if col = 2 then u.pins
  else if col = 3 then u.oldPins else if col = 4 then u.newPins else if col = 5 then u.offset else past

/-- The expression reads only the indexed five-word task and the two node
records named by it. In particular it never scans trivalent rows. -/
theorem term_eval (data : Fin k → Word w) (m : Memory w) (vs : Fin 3 → Word w) :
    let delta := vs 0-vs 1
    let i := BinaryOp.eval .div delta 7
    let c := BinaryOp.eval .mod delta 7
    let t := readTask m (vs 2 + 5*i)
    let a := readNode m t.child
    let b := readNode m t.parent
    (term w k).eval data m vs = selectWord (t.header a b) (t.past a b) c := by
  dsimp only
  simp only [term,Term.eval_select,Term.eval_load,Term.eval_binary,Term.eval_literal,Term.eval,
    Comparison.test,beq_iff_eq,selectWord,Task.header,Task.past,readTask,readNode,BinaryOp.eval]
  all_goals split_ifs <;> simp_all

/-- The uniform program size is independent of all physical stage sizes. -/
theorem binds_le : (term w k).binds ≤ 512 := by
  simp only [term,Term.load,Term.binary,Term.select,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  decide

end ThreeFlat.RAM.HistoryCommandTable

end OAI
